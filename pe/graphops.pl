% Transitive closure of a graph 


:- module(graphops,_,[]).

:- use_module(chclibs(setops)).
:- use_module(library(lists)).
:- use_module(library(aggregates)).

% Depth first search returning cross/forward edges, tree edges and back edges

dfsEdges([P|Ps],Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1) :-
    member(P,M0),   % P already visited.
    !,
    dfsEdges(Ps,Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1).
dfsEdges([P|Ps],Es,Anc,M0,M2,Bs0,Bs2,Cs0,Cs2,Ts0,Ts2) :-
    dfsVisit(P,Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1),
    dfsEdges(Ps,Es,Anc,M1,M2,Bs1,Bs2,Cs1,Cs2,Ts1,Ts2).
dfsEdges([],_,_,M,M,Bs,Bs,Cs,Cs,Ts,Ts). 

dfsVisit(P,Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1) :-
    successors(P,Es,Ss),
    dfsVisitSuccs(Ss,P,Es,[P|Anc],[P|M0],M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1).

dfsVisitSuccs([],_,_,_,M,M,Bs,Bs,Cs,Cs,Ts,Ts).
dfsVisitSuccs([Q|Qs],P,Es,Anc,M0,M1,[P-Q|Bs0],Bs1,Cs0,Cs1,Ts0,Ts1) :-   % back edge
    member(Q,Anc),
    !,
    dfsVisitSuccs(Qs,P,Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1).
dfsVisitSuccs([Q|Qs],P,Es,Anc,M0,M1,Bs0,Bs1,[P-Q|Cs0],Cs1,Ts0,Ts1) :-           % cross or forward edge
    member(Q,M0),
    !,
    dfsVisitSuccs(Qs,P,Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1).
dfsVisitSuccs([Q|Qs],P,Es,Anc,M0,M2,Bs0,Bs2,Cs0,Cs2,[P-Q|Ts0],Ts2) :-           % tree edge
    dfsVisit(Q,Es,Anc,M0,M1,Bs0,Bs1,Cs0,Cs1,Ts0,Ts1),
    dfsVisitSuccs(Qs,P,Es,Anc,M1,M2,Bs1,Bs2,Cs1,Cs2,Ts1,Ts2).
    
reachableSets(Vs,Es,C) :-
    transClosure(Vs,Es,[],C).
    
transClosure([V|Vs],Es,C0,C3) :-
    updateMatrix(C0,V,V,C1),
    dfs(Es,V,V,C1,C2),
    transClosure(Vs,Es,C2,C3).
transClosure([],_,C,C).

dfs(Es,Root,Descendant,C0,C1) :-
    predecessors(Descendant,Es,Ss),
    dfsChildren(Ss,Es,Root,C0,C1).
    
dfsChildren([Child|Ss],Es,Root,C0,C1) :-
    member(reach(Root,Ds),C0),
    member(Child,Ds),       % Child is already reachable from Root
    !,
    dfsChildren(Ss,Es,Root,C0,C1).
dfsChildren([Child|Ss],Es,Root,C0,C3) :-
    updateMatrix(C0,Root,Child,C1),
    dfs(Es,Root,Child,C1,C2),
    dfsChildren(Ss,Es,Root,C2,C3).
dfsChildren([],_,_,C,C).        
    
updateMatrix([],P,Q,[reach(P,[Q])]).
updateMatrix([reach(P,As)|Ds],P,Q,[reach(P,As1)|Ds]) :- 
    setunion([Q],As,As1).
updateMatrix([reach(P1,As)|Ds],P,Q,[reach(P1,As)|Ds1]) :-
    P \== P1,
    updateMatrix(Ds,P,Q,Ds1).
    
successors(P,Es,Ss) :-
    bagof(Q, member(P-Q,Es),
                    Ss),
    !.
successors(_,_,[]).

predecessors(P,Es,Ss) :-
    bagof(Q, member(Q-P,Es),
                    Ss),
    !.
predecessors(_,_,[]).
