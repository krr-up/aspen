from unittest import TestCase
from pathlib import Path

import tree_sitter_clingo as ts_clingo
from tree_sitter import Language, Parser
from clingo.symbol import parse_term, String, Tuple_, Number, Function
from clingo.core import Library

from aspen.tree import AspenTree, StringInput, FileInput

asp_dir = Path("tests", "files").resolve()
lib = Library()
clingo_lang = Language(ts_clingo.language())


class TestAspenTree(TestCase):
    """Test AspenTree class."""

    def test_parse_strings(self):
        """Test parsing of input strings."""
        tree = AspenTree(
            source_strings=[StringInput("test", "a :- b.", language=clingo_lang)]
        )
        # we have to parse and then turn back into string due to
        # clingo6 bug: https://github.com/potassco/clingo/issues/579
        with (asp_dir / "ab_reified_string.txt").open() as f:
            expected_symbols = [str(parse_term(lib, s)) for s in f.readlines()]
        expected_symbols.sort()
        symbols = [str(parse_term(lib, str(s))) for s in tree.facts]
        symbols.sort()
        self.assertListEqual(symbols, expected_symbols)

    def test_parse_files(self):
        """Test parsing of input files."""
        tree = AspenTree(
            source_files=[FileInput(asp_dir / "ab.lp", language=clingo_lang)]
        )
        with (asp_dir / "ab_reified_file.txt").open() as f:
            expected_symbols = [str(parse_term(lib, s)) for s in f.readlines()]
        expected_symbols.sort()
        symbols = [str(parse_term(lib, str(s))) for s in tree.facts]
        symbols.sort()
        self.assertListEqual(symbols, expected_symbols)

    def test_reify_missing_node(self):
        """Test reification of missing node."""
        tree = AspenTree(
            source_strings=[StringInput("test", "=2.", language=clingo_lang)]
        )
        with (asp_dir / "missing_reified.txt").open() as f:
            expected_symbols = [str(parse_term(lib, s)) for s in f.readlines()]
        expected_symbols.sort()
        symbols = [str(parse_term(lib, str(s))) for s in tree.facts]
        symbols.sort()
        self.assertListEqual(symbols, expected_symbols)

    def test_reify_error_node(self):
        """Test reification of error node."""
        tree = AspenTree(
            source_strings=[StringInput("test", "+a.", language=clingo_lang)]
        )
        with (asp_dir / "error_reified.txt").open() as f:
            expected_symbols = [str(parse_term(lib, s)) for s in f.readlines()]
        expected_symbols.sort()
        symbols = [str(parse_term(lib, str(s))) for s in tree.facts]
        symbols.sort()
        self.assertListEqual(symbols, expected_symbols)

    def test_path2py(self):
        """Test conversion of symbolic path to python list"""
        tree = AspenTree(default_language=clingo_lang)
        good_path = Tuple_(
            lib, [Tuple_(lib, [Tuple_(lib, []), Number(lib, 2)]), Number(lib, 1)]
        )
        self.assertListEqual(tree.path2py(good_path), [1, 2])
        inverted_path = Tuple_(
            lib, [Number(lib, 1), Tuple_(lib, [Number(lib, 2), Tuple_(lib, [])])]
        )
        self.assertFalse(tree.path2py(inverted_path))
        bad_element_path = Tuple_(
            lib,
            [Tuple_(lib, [Tuple_(lib, []), Function(lib, "b", [])]), String(lib, "a")],
        )
        self.assertFalse(tree.path2py(bad_element_path))

    def test_transform_add_vars(self):
        """Test transformation, adding variables to atoms."""
        tree = AspenTree(
            source_strings=[StringInput("test", "a :- b.", language=clingo_lang)]
        )
        tree.transform(
            meta_files=[asp_dir / "add_var.lp"],
            initial_program=("add_var_to_atoms", [String(tree.lib, "X")]),
        )
        self.assertEqual(b"a(X) :- b(X).", tree.source_strings["test"].source_bytes)
        tree2 = AspenTree(
            source_strings=[StringInput("test", "a(X) :- b(X).", language=clingo_lang)]
        )
        expected_symbols = [str(f) for f in tree2.facts]
        symbols = [str(f) for f in tree.facts]
        expected_symbols.sort()
        symbols.sort()
        self.assertListEqual(symbols, expected_symbols)
