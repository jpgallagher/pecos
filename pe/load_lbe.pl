:- module(load_lbe, [main/1, load_file/1,lbe_clause/4], [assertions, isomodes, doccomments, dynamic]).

%! \title loader for Horn clauses in LBE form
%
%  \module
%    Load clauses in `lbe_clause/4` (keeps a unique identifer for each
%    clause). Ignores any other terms in the file.

:- dynamic lbe_clause/4.

:- use_module(library(streams)).
:- use_module(library(lists)).
:- use_module(library(read)).
:- use_module(chclibs(common), [conj2List/2]).

main([F]) :-
    load_file(F).
    
load_file(F) :-
    retractall(lbe_clause(_,_,_,_)),
    open(F,read,S),
    remember_all(S,1),
    close(S).

remember_all(S,K) :-
    read(S,C),
    ( C == end_of_file ->
        true
    ; remember_clause(C,K),
      K1 is K+1,
      remember_all(S,K1)
    ).

remember_clause((A:-Def,PCalls), K) :- 
    !,
    makeClauseId(K,CK),
    assertz(lbe_clause(A,Def,PCalls,CK)).
remember_clause(_,_).

makeClauseId(K,CK) :-
    name(K,NK),
    append("c",NK,CNK),
    name(CK,CNK).


