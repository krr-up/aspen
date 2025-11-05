aspen(_replacement(edit(N,format(S,R)),R)) :- aspen(edit(N,format(S,R))).
aspen(_replacement(G,R)) :- aspen(_replacement(G,(F,R))).
aspen(replacement(G,F)) :- aspen(_replacement(G,(F,R))).

aspen(target(edit(N,S),N)) :- aspen(edit(N,S)).

aspen(desc((S,P), (S,P))) :- aspen(query_desc((S,P))).
aspen(desc((S,P), (S,(P',I)))) :- aspen(desc((S,P), (S,P'))), node((S,(P',I))).

aspen(query_desc(T)) :- aspen(replacement(G,T)).
% edit G' must occur before G
aspen(comes_before(G',G))
  :- aspen(replacement(G,R)), aspen(target(G',T)), aspen(desc(R,T)), G != G'.

%% #show replacement/2.
%% #show target/2.
%% #show desc/2.
%% #show depends/2.
