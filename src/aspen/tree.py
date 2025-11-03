from typing import (
    Optional,
    Self,
    Literal,
    Sequence,
    ByteString,
    NamedTuple,
    Iterator,
    List,
    cast,
    reveal_type,
    Hashable,
)
from collections import defaultdict, namedtuple
from pathlib import Path
from dataclasses import dataclass
from graphlib import TopologicalSorter, CycleError

from clingo.control import Control
from clingo.symbol import Symbol, Function, Number, String, Tuple_, SymbolType
from clingo.core import Library
from clingo.solve import Model
import tree_sitter as ts
import aspen

from aspen.utils.logging import get_logger, get_clingo_logger, get_ts_logger
from aspen.utils.tree_sitter_utils import ts_edit_tree


logger = get_logger(__name__)
clingo_logger = get_clingo_logger(logger)
ts_logger = get_ts_logger(logger)

Id = int
Bytes = tuple[int, int]
StringEncoding = Literal["utf8", "utf16"]
StringName = str

SourceInputValue = Path | str | tuple[Hashable, Path] | tuple[Hashable, str]
SourceInput = tuple[SourceInputValue]


class StringInput(NamedTuple):
    """A named tuple representing an input string to be
    parsed and turned into facts by an AspenTree instance.

    """

    name: StringName
    value: str
    language: Optional[ts.Language] = None
    encoding: Optional[StringEncoding] = None
    included_ranges: Optional[Sequence[ts.Range]] = None


class FileInput(NamedTuple):
    """A named tuple representing an input file to be
    parsed and turned into facts by an AspenTree instance.

    """

    path: Path
    language: Optional[ts.Language] = None
    encoding: Optional[StringEncoding] = None
    included_ranges: Optional[Sequence[ts.Range]] = None


@dataclass
class SourceString:
    """Source file processed by an AspenTree."""

    id: int
    symbol: Symbol
    name: StringName
    source_bytes: bytes
    encoding: StringEncoding
    parser: ts.Parser
    tree: ts.Tree


@dataclass
class SourceFile:
    """Source file processed by an AspenTree."""

    id: int
    symbol: Symbol
    path: Path
    source_bytes: bytes
    encoding: StringEncoding
    parser: ts.Parser
    tree: ts.Tree


Source = SourceString | SourceFile
SourceNode = tuple[Source, ts.Node]
FormatEdit = tuple[SourceNode, tuple[str, list[SourceNode]]]


class AspenTree:
    """A tree that wraps a tree-sitter tree and it's representation as a set ASP facts.

    The class further defined various transformation operations on
    both representations, and syncs the two in case of
    changes. Transformations to the tree-sitter tree can be made via
    the wrapped tree's API, while trasformations on the ASP fact
    reperesentation can be defined via a logic program, which deriving
    special transformation predicates in it's answer sets with the
    fact representation of the tree as input.

    """

    def __init__(
        self,
        source_strings: Optional[Sequence[StringInput]] = None,
        source_files: Optional[Sequence[FileInput]] = None,
        default_language: Optional[ts.Language] = None,
        default_encoding: StringEncoding = "utf8",
        clingo_lib: Optional[Library] = None,
    ):
        self.source_strings: dict[StringName, SourceString] = {}
        self.string_id2name: dict[int, StringName] = {}
        self.source_files: dict[Path, SourceFile] = {}
        self.file_id2path: dict[int, Path] = {}
        self.default_language = default_language
        self.default_encoding = default_encoding
        self.lib = clingo_lib if clingo_lib is not None else Library(logger=clingo_logger)
        self.facts: List[Symbol] = []
        self.next_transform_program: Optional[tuple[str, Sequence[Symbol]]] = None
        if source_strings is not None:
            self.parse_strings(source_strings)
        if source_files is not None:
            self.parse_files(source_files)

    def parse_strings(self, string_inputs: Sequence[StringInput]):
        """Parse input strings, and generate fact representation."""
        if not isinstance(string_inputs, list):  # nocoverage
            raise ValueError("Inputs must be a list.")
        for s in string_inputs:
            cast(StringInput, s)  # No idea why this is necessary for mypy.
            language = s.language if s.language is not None else self.default_language
            if language is None:  # nocoverage
                raise ValueError(
                    f"Input source '{s}' has no language specified, "
                    "and no default language is given."
                )
            encoding = s.encoding if s.encoding is not None else self.default_encoding
            parser = ts.Parser(
                language, included_ranges=s.included_ranges, logger=ts_logger
            )
            source_bytes = bytes(s.value, encoding)
            tree = parser.parse(source_bytes, encoding=encoding)
            identifier = len(self.source_strings)
            self.string_id2name[identifier] = s.name
            source_symb = Function(self.lib, "s", [Number(self.lib, identifier)])
            source_string = SourceString(
                identifier, source_symb, s.name, source_bytes, encoding, parser, tree
            )
            self.source_strings[s.name] = source_string
            self.reify_ts_tree(tree, source_string)

    def parse_files(self, file_inputs: Sequence[FileInput]):
        """Parse input files, and generate fact representation."""
        if not isinstance(file_inputs, list):  # nocoverage
            raise ValueError("Inputs must be a list.")
        for f in file_inputs:
            path = f.path.resolve()
            if not path.is_file():  # nocoverage
                raise IOError(f"File {path} not found.")
            language = f.language if f.language is not None else self.default_language
            if language is None:  # nocoverage
                raise ValueError(
                    f"Input source '{f}' has no language specified, "
                    "and no default language is given."
                )
            encoding = f.encoding if f.encoding is not None else self.default_encoding
            parser = ts.Parser(
                language, included_ranges=f.included_ranges, logger=ts_logger
            )
            source_bytes = path.read_bytes()
            tree = parser.parse(source_bytes, encoding=encoding)
            identifier = len(self.source_files)
            self.file_id2path[identifier] = path
            source_symb = Function(self.lib, "f", [Number(self.lib, identifier)])
            source_file = SourceFile(
                identifier, source_symb, path, source_bytes, encoding, parser, tree
            )
            self.source_files[path] = source_file
            self.reify_ts_tree(tree, source_file)

    def reify_node_attrs(
        self, node: ts.Node, node_id: Symbol, encoding: StringEncoding
    ) -> list[Symbol]:
        """Reify a tree-sitter node and it's attributes into a (set of) fact(s)."""
        facts: list[Symbol] = []
        facts.append(Function(self.lib, "node", [node_id]))
        if node.is_named:
            facts.append(
                Function(self.lib, "type", [node_id, String(self.lib, node.type)])
            )
        if node.is_error:
            facts.append(Function(self.lib, "error", [node_id]))
        if node.is_missing:
            facts.append(Function(self.lib, "missing", [node_id]))
        if node.is_extra:  # nocoverage
            facts.append(Function(self.lib, "extra", [node_id]))
        if node.child_count == 0 and node.text is not None:
            facts.append(
                Function(
                    self.lib,
                    "leaf_text",
                    [node_id, String(self.lib, node.text.decode(encoding))],
                )
            )
        return facts

    def reify_ts_subtree(
        self,
        node: ts.Node,
        subtree_path: Symbol,
        source_symb: Symbol,
        encoding: StringEncoding,
    ) -> list[Symbol]:
        """Reify tree-sitter subtree with input root node into a set of facts."""
        stack: list[tuple[ts.Node, Symbol]] = [(node, subtree_path)]
        facts: list[Symbol] = []
        while len(stack) > 0:
            parent, parent_path = stack.pop()
            parent_id = Tuple_(self.lib, [source_symb, parent_path])
            facts.extend(self.reify_node_attrs(parent, parent_id, encoding))
            for idx, child in enumerate(parent.children):
                child_path = Tuple_(self.lib, [parent_path, Number(self.lib, idx)])
                child_id = Tuple_(self.lib, [source_symb, child_path])
                field_name = parent.field_name_for_child(idx)
                if field_name is not None:
                    facts.append(
                        Function(
                            self.lib, "field", [child_id, String(self.lib, field_name)]
                        )
                    )
                stack.append((child, child_path))
        return facts

    def reify_ts_tree(self, tree: ts.Tree, source: Source):
        """Reify tree-sitter tree into a set of facts."""
        root_node = tree.root_node
        root_path = Tuple_(self.lib, [])
        if source.parser.language is None:  # nocoverage
            raise ValueError(f"Parser of source cannot be None: '{source}'")
        lang_name = source.parser.language.name
        if lang_name is None:  # nocoverage
            raise ValueError(f"Language of parser of source cannot be None: '{source}'.")
        if isinstance(source, SourceFile):
            source_origin = str(source.path)
        elif isinstance(source, SourceString):
            source_origin = source.name
        else:  # nocoverage
            raise ValueError(
                "Arguments subtree_source must be a SourceFile or SourceString instance."
            )
        origin_fact = Function(
            self.lib, "origin", [source.symbol, String(self.lib, source_origin)]
        )
        lang_fact = Function(
            self.lib,
            "language",
            [source.symbol, String(self.lib, source.parser.language.name)],  # type: ignore
        )
        self.facts.append(origin_fact)
        self.facts.append(lang_fact)
        self.facts.extend(
            self.reify_ts_subtree(root_node, root_path, source.symbol, source.encoding)
        )

    def path2py(self, path_symb: Symbol) -> list[int] | Literal[False]:
        """Convert path expression from symbolic to list form."""
        l: list[int] = []
        nil = Tuple_(self.lib, [])
        while path_symb != nil:
            if not path_symb.match(2) or path_symb.arguments[1].type != SymbolType.Number:
                return False
            l.append(path_symb.arguments[1].number)
            path_symb = path_symb.arguments[0]
        return l

    def source2py(self, source_symb: Symbol) -> Source | Literal[False]:
        """Retrieve aspen source from it's identifier symbol."""
        source: Source
        if (
            source_symb.match("s", 1)
            and source_symb.arguments[0].type == SymbolType.Number
        ):
            source_string_name = self.string_id2name[source_symb.arguments[0].number]
            source = self.source_strings[source_string_name]
        elif (
            source_symb.match("f", 1)
            and source_symb.arguments[0].type == SymbolType.Number
        ):
            source_file_path = self.file_id2path[source_symb.arguments[0].number]
            source = self.source_files[source_file_path]
        else:
            return False
        return source

    def is_node_id(self, symb: Symbol) -> bool:
        """Returns true if symbol is syntactically valid node id."""
        return (
            symb.match(2)
            and bool(self.source2py(symb.arguments[0]))
            and bool(self.path2py(symb.arguments[1]))
        )

    def conslist2list(self, l: Symbol) -> list[Symbol]:
        """Convert symbolic cons list consisting of nested tuples into
        a python list of symbols."""
        l_py: list[Symbol] = []
        nil = Tuple_(self.lib, [])
        while l != nil:
            l_py.append(l.arguments[0])
            l = l.arguments[1]
        return l_py

    def node_id2ts(self, node_id: Symbol) -> SourceNode:
        """Retrieve tree-sitter node from node identifier symbol."""
        source_symb, path_symb = node_id.arguments
        path_list = self.path2py(path_symb)
        if not path_list:
            raise ValueError(f"Malformed path symbol: {path_symb}.")
        source = self.source2py(source_symb)
        if not source:
            raise ValueError(f"Malformed source symbol '{source_symb}'.")
        tree = source.tree
        node = tree.root_node
        while True:
            try:
                idx = path_list.pop()
            except IndexError:
                break
            tmp_node = node.child(idx)
            if tmp_node is None:
                raise ValueError(f"No node found at path '{path_symb}'.")
            node = tmp_node
        return source, node

    def get_descendant_ids(
        self, node: ts.Node, node_path_symb: Symbol, source_symb: Symbol
    ) -> list[Symbol]:
        """Return list of identifiers for all descendents of node."""
        desc_ids: list[Symbol] = []
        stack: list[tuple[ts.Node, Symbol]] = [(node, node_path_symb)]
        while len(stack) > 0:
            parent, parent_path = stack.pop()
            parent_id = Tuple_(self.lib, [source_symb, parent_path])
            desc_ids.append(parent_id)
            for idx, child in enumerate(parent.children):
                child_path = Tuple_(self.lib, [parent_path, Number(self.lib, idx)])
                child_id = Tuple_(self.lib, [source_symb, child_path])
                desc_ids.append(child_id)
                stack.append((child, child_path))
        return desc_ids

    def node2path_symb(self, node: ts.Node) -> Symbol:
        """Given a tree-sitter node, calculate the corresponding path symbol."""
        path: list[int] = []
        parent = node.parent
        while parent is not None:
            path.append(parent.children.index(node))
            node = parent
            parent = node.parent
        path_symb = Tuple_(self.lib, [])
        while True:
            try:
                idx = path.pop()
            except IndexError:
                break
            path_symb = Tuple_(self.lib, [path_symb, Number(self.lib, idx)])
        return path_symb

    def _reparse_sources(self, edited_sources: dict[Symbol, set[ts.Range]]) -> None:
        """Re-parse sources that have been edited, and update fact
        representation based on the changed ranges of sources.

        A set of additional ranges who's fact representation should be
        updated can be provided as the value for the given source in
        the edited_sources dict argument.
        """
        delete_ids: set[Symbol] = set()
        reify_subtree_roots: list[tuple[ts.Node, Symbol, Symbol, StringEncoding]] = []
        additional_facts: List[Symbol] = []
        for source_symb, changed_ranges in edited_sources.items():
            source = self.source2py(source_symb)
            if not source:
                raise ValueError(f"Malformed source symbol '{source_symb}'.")
            old_tree = source.tree
            # print(source.source_bytes)
            new_tree = source.parser.parse(
                source.source_bytes, old_tree, encoding=source.encoding
            )
            changed_ranges.update(old_tree.changed_ranges(new_tree))
            # print(changed_ranges)
            source.tree = new_tree
            # print(f"Changed ranges in source {source}:.")
            # print(changed_ranges)
            for changed_range in changed_ranges:
                start, end = changed_range.start_byte, changed_range.end_byte
                node = new_tree.root_node.descendant_for_byte_range(start, end)
                if node is None:
                    raise RuntimeError("Code should be unreachable.")
                # Not sure if this is necessary, but we walk up to the
                # greatest node that spans the changed range.
                parent = node.parent
                while (
                    parent is not None
                    and parent.start_byte == start
                    and parent.end_byte == end
                ):
                    node = parent
                    parent = node.parent
                path_symb = self.node2path_symb(node)
                reify_subtree_roots.append(
                    (node, path_symb, source.symbol, source.encoding)
                )
                delete_ids.update(self.get_descendant_ids(node, path_symb, source.symbol))
                if parent is not None:
                    node_idx = parent.children.index(node)
                    field_name = parent.field_name_for_child(node_idx)
                    if field_name is not None:
                        node_id = Tuple_(self.lib, [source_symb, path_symb])
                        field_fact = Function(
                            self.lib, "field", [node_id, String(self.lib, field_name)]
                        )
                        additional_facts.append(field_fact)
        # print("Ids to be deleted:")
        # print([str(s) for s in delete_ids])
        self.facts = [f for f in self.facts if f.arguments[0] not in delete_ids]
        # print("Reification to be done after transform:")
        # print([str(s) for s in reify_subtree_roots])
        for args in reify_subtree_roots:
            self.facts.extend(self.reify_ts_subtree(*args))
        if len(additional_facts) > 0:
            self.facts.extend(additional_facts)

    def _edit_tree(
        self, edit_symbols: Sequence[Symbol], deps: dict[Symbol, List[Symbol]]
    ) -> dict[Symbol, set[ts.Range]]:
        """Apply edits to tree according to operations given in
        edit_symbols, and return dictionary who's keys are source
        symbols that have been edited, and the values are a set of
        additional changed ranges that will not (necessarily) be
        detected by tree-sitter when re-parsing after the edit.

        """

        seen = set()
        dupes = {
            f.arguments[0]
            for f in edit_symbols
            if f.arguments[0] in seen or seen.add(f.arguments[0])  # type: ignore
        }
        if len(dupes) > 0:
            raise ValueError(
                "Multiple edits defined for following nodes; "
                f"expected one each: '{dupes}'."
            )
        # print(edit_symbols)
        # print(deps)
        # Toplogically sort edits, so they are processed in correct
        # order We edit (children of) replacement nodes before the
        # target node of any given derived edit fact.
        for s in edit_symbols:
            if s not in deps.keys():
                deps[s] = []
        tsorter = TopologicalSorter(deps)
        edit_symbols = list(tsorter.static_order())
        # print(edit_symbols)
        edited_sources: dict[Symbol, set[ts.Range]] = {}
        for symb in edit_symbols:
            replacement = symb.arguments[1]
            if replacement.match("format", 2):
                target_source, target_node = self.node_id2ts(symb.arguments[0])
                format_string = replacement.arguments[0].string
                replacement_tup = replacement.arguments[1]
                repl_texts: list[str] = []
                replacements = self.conslist2list(replacement_tup)
                for repl in replacements:
                    try:
                        repl_source, repl_node = self.node_id2ts(repl)
                        start, end = repl_node.start_byte, repl_node.end_byte
                        repl_text = repl_source.source_bytes[start:end].decode(
                            repl_source.encoding
                        )
                    except ValueError:
                        repl_text = str(repl)
                        if repl_text.startswith('"') and repl_text.endswith('"'):
                            repl_text = repl_text[1:-1]
                    repl_texts.append(repl_text)
                replacement_text = format_string.format(*repl_texts)
                replacement_bytes = bytes(replacement_text, target_source.encoding)
                target_source.source_bytes = ts_edit_tree(
                    target_source.tree,
                    target_node,
                    replacement_bytes,
                    target_source.source_bytes,
                )
                if target_source.symbol not in edited_sources:
                    edited_sources[target_source.symbol] = set()
                # changes to leaf nodes do not show up in tree changed_ranges method,
                # so we manually mark these nodes as changed instead
                if target_node.child_count == 0:
                    edited_sources[target_source.symbol].add(target_node.range)

            else:
                raise ValueError(
                    f"Symbol '{replacement}' does not match any "
                    "allowed replacement symbols."
                )
        # print(edited_sources)
        return edited_sources

    def _on_model(self, model: Model) -> Literal[False]:
        """Model callback for control object. Returns False as we only
        expect one model."""
        if logger.level == 10:
            logger.debug(
                "Stable model obtained by applying transformation meta-encoding:"
            )
            for s in model.symbols(shown=True):
                logger.debug(str(s))

        edit_symbols: list[Symbol] = []
        next_transform_symbols: list[Symbol] = []
        deps: defaultdict[Symbol, list[Symbol]] = defaultdict(list)
        for symb in model.symbols(shown=True):
            if symb.match("aspen", 1):
                arg = symb.arguments[0]
                if arg.match("edit", 2):
                    if not self.is_node_id(arg.arguments[0]):
                        logger.info(
                            "First argument of edit symbol '%s' is not a valid node id,"
                            " ignoring.",
                            str(symb),
                        )
                        continue
                    if arg.arguments[1].match("format", 2):
                        logger.info(
                            "Edit derived by transformation meta-encoding: '%s'",
                            str(symb),
                        )
                        edit_symbols.append(arg)
                elif arg.match("depends", 2):
                    deps[arg.arguments[1]].append(arg.arguments[0])
                elif arg.match("next_transform_program", 2):
                    next_transform_symbols.append(arg)
        if len(next_transform_symbols) > 1:
            raise ValueError(
                (
                    "Multiple following transformation program defined, expected one: "
                    f"'{next_transform_symbols}'."
                )
            )
        if len(next_transform_symbols) > 0:
            next_symb = next_transform_symbols[0]
            if next_symb.arguments[0].type != SymbolType.String:
                raise ValueError(
                    "First argument of next_transform_program must be a string, "
                    f"found: '{next_symb}'."
                )
            self.next_transform_program = (
                next_symb.arguments[0].string,
                next_symb.arguments[1].arguments,
            )
        edited_sources = self._edit_tree(edit_symbols, deps)
        self._reparse_sources(edited_sources)
        return False

    def transform(
        self,
        meta_files: Optional[Sequence[Path]] = None,
        meta_string: Optional[str] = None,
        initial_program: tuple[str, Sequence[Symbol]] = ("base", ()),
        util_encodings: Sequence[str] = ("all.lp",),
        control_options: Optional[Sequence[str]] = None,
    ):
        """Transform fact base via a meta-encoding."""
        options = control_options if control_options is not None else []
        if meta_files is not None:
            for f in meta_files:
                if not f.is_file():
                    raise IOError(f"File {f} not found.")
        encoding_files = [str(f) for f in meta_files] if meta_files is not None else []
        aspen_init_path = Path(aspen.__file__)
        encoding_path = (aspen_init_path / ".." / "asp").resolve()
        base_encodings = [encoding_path / "defined.lp", encoding_path / "edit.lp"]
        encoding_files.extend([str(p) for p in base_encodings])
        encoding_files.extend(
            [str(encoding_path / "utils" / name) for name in util_encodings]
        )
        base_program = ("base", ())
        self.next_transform_program = initial_program
        while self.next_transform_program is not None:
            control = Control(self.lib, options=options)
            control.parse_files(encoding_files)
            if meta_string is not None:
                control.parse_string(meta_string)
            with control.backend as backend:
                for fact in self.facts:
                    atom = backend.atom(fact)
                    backend.rule([atom])
            parts = (
                None
                if self.next_transform_program == base_program
                else [base_program, self.next_transform_program]
            )
            control.ground(parts=parts)
            self.next_transform_program = None
            with control.solve() as handle:
                last_model = handle.last()
                if last_model is None:
                    raise RuntimeError("Transformation program is unsatisfiable.")
                self._on_model(last_model)
