% Transform to large block form of clauses

:- module(lbe,_,[dynamic]).

:- use_module(library(write)).
:- use_module(library(read)).
:- use_module(library(lists)).
:- use_module(library(aggregates)).
:- use_module(library(streams)).

:- use_module(chclibs(common)).
:- use_module(chclibs(program_loader)).
:- use_module(chclibs(setops)).
:- use_module(chclibs(balanced_tree)).
:- use_module(chclibs(canonical)).

:- use_module(graphops).
:- use_module(unionfind).
:- use_module(library(read_from_string), [read_from_atom/2]).


:- dynamic lbe_clause/4.


main([F,Q]) :-
	convertQueryString(Q,Q1),
	lbe(F,Q1).
	
lbef(File,Goal,OutFile) :-
	load_file(File),
	makeLBE(Goal,Defs),
	open(OutFile,write,OutS),
	writeList(Defs,OutS),
	close(OutS).
	
lbe(File,Goal) :-
	load_file(File),
	makeLBE(Goal,Defs),
	writeList(Defs,user_output).
	
assertLBE(File,Goal) :-
	load_file(File),
	makeLBE(Goal,Defs),
	assertLBEClauses(Defs,1).

makeLBE(Goal,Defs) :-
	cleanup,
	functor(Goal,P,N),	% entry node P/N
	dependency_graph(Es,Vs),
	%length(Vs,NVs),
	%write(NVs),nl,
	%length(Es,NEs),
	%write(NEs),nl,
	dfsVisit(P/N,Es,[],[],RVs,BEs,[],CEs,[],TEs,[]), 	% find reached nodes, back, cross and tree edges
	
	%write(OutS,		'Back: '), write(OutS,BEs),nl(OutS),
	%write(OutS,		'Cross: '), write(OutS,CEs),nl(OutS),
	%write(OutS,		'Tree: '), write(OutS,TEs),nl(OutS),
	%write(OutS,		'Reachable nodes: '), write(OutS,RVs),nl(OutS),
	
	treePartition(Vs,TEs,CEs,BEs,TP),					% partition nodes by subtrees 
	
	%write(OutS,		'Trees: '), write(OutS,TP),nl(OutS),
	treeRoots(TP,Roots),
	parentTreeList(Roots,Es,TP,PreTrees),
	reachableSets(Roots,Es,RSs),
	reverse(RVs,Stack),
	mergeTrees(Stack,Roots,Es,RSs,PreTrees,TP,_TP1,Ms), 
	
	%write(OutS,		'Multitree: '), write(OutS,Ms),nl(OutS),
	%write(OutS,		'Singletree: '), write(OutS,Ss),nl(OutS),
	%write(OutS,		'Multicontext: '), write(OutS,MCs),nl(OutS),
	%write(OutS,		'Reachable: '), write(OutS,RSs),nl(OutS),
	
	unfoldBlocks(RVs,P/N,PreTrees,Ms,[],Defs).
	
	%write(OutS,		'Subtrees: '), write(OutS,TP1),nl(OutS).	
	
assertLBEClauses([D|Defs], K) :- 
	!,
	makeClauseId(K,CK),
	melt(D,(A:-Def,PCalls)),
	assertz(lbe_clause(A,Def,PCalls,CK)),
	K1 is K+1,
	assertLBEClauses(Defs,K1).
assertLBEClauses([],_).

convertQueryString(Q,Q1) :-
	read_from_atom(Q,Q1).


cleanup :-
	retractall(lbe_clause(_,_,_,_)).
	
dependency_graph(Es,Vs) :-
	findall(P/N-Q/M, (
			my_clause(H,Bs,_),
			functor(H,P,N),
			member(B,Bs),
			\+ constraint(B,_),
			functor(B,Q,M)
			),
			Es),	% multiset of edges
	%makeset(Es1,Es),
	findall(A, (
			member(X-Y,Es),
			(A=X; A=Y)
			),
			Vs1),
	makeset(Vs1,Vs2),
	(setof(P/N, [H,Bs,C]^(my_clause(H,Bs,C),functor(H,P,N)), Vs3) -> true; Vs3=[]),  % include uncalled unit clauses
	setunion(Vs2,Vs3,Vs).	
		
writeReachSets([reach(P,As)|Ds]) :- 
	write(P),
	write(' reaches '),
	write(As),
	nl,
	writeReachSets(Ds).
writeReachSets([]).

isConstraint(C) :-
	constraint(C,_).
	
unfoldBlocks([P|Ps],Entry,PreTrees,Ms,Hs,[PDef|Defs]) :-
	definedPred(P,PreTrees,Ms),
	!,
	unfoldBlock(P,PreTrees,Ms,Hs,PDef),
	unfoldBlocks(Ps,Entry,PreTrees,Ms,Hs,Defs).
unfoldBlocks([_|Ps],Entry,PreTrees,Ms,Hs,Defs) :-
	unfoldBlocks(Ps,Entry,PreTrees,Ms,Hs,Defs).
unfoldBlocks([],_,_,_,_,[]).
	
unfoldBlock(F/N,PreTrees,Ms,Hs,(A:-Def,PCalls)) :-
	!,
	functor(A,F,N),
	treeDef(A,F/N,PreTrees,Ms,Hs,_,Def,[],PCalls,[]),
	numbervars((A:-Def,PCalls),0,_).

% get the clauses defining A and then expand the body to a large block
treeDef(A,V,PreTrees,Ms,Hs0,Hs1,[Def|F0],F1,PCs0,PCs1) :-
	pdef(A,E),
	expand(E,V,Def,PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1).

expand((B1;B2),V,(C1;C2),PreTrees,Ms,Hs0,Hs2,F0,F2,PCs0,PCs2) :-
	!,
	expand(B1,V,C1,PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1),
	expand(B2,V,C2,PreTrees,Ms,Hs1,Hs2,F1,F2,PCs1,PCs2).
expand([],_,[],_,_,Hs,Hs,F,F,PCs,PCs) :-
	!.
expand([B|Bs],V,[C|Bs1],PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1) :-
	constraint(B,C),
	!,
	expand(Bs,V,Bs1,PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1).
expand([B|Bs],V,[Eqs|Bs1],PreTrees,Ms,Hs0,Hs2,F0,F2,PCs0,PCs2) :- 	% B is a merge point
	mergePoint(B,P,N,Ms),
	!,
	functor(CB,P,N),
	B =.. [P|Xs],
	CB =.. [P|Ys],
	makeEqualities(Xs,Ys,Eqs),
	expandOrReuse(CB,B,V,PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1),
	expand(Bs,V,Bs1,PreTrees,Ms,Hs1,Hs2,F1,F2,PCs1,PCs2).
expand([B|Bs],V,[Bool|Bs1],PreTrees,Ms,Hs0,Hs1,F0,F1,[(Bool=B)|PCs0],PCs1) :-
	singleCall(B,V,PreTrees),	% this is the only call to B in V's tree
	!,
	expand(Bs,V,Bs1,PreTrees,Ms,[used(B)|Hs0],Hs1,F0,F1,PCs0,PCs1).
expand([B|Bs],V,[Eqs,Bool|Bs1],PreTrees,Ms,Hs0,Hs1,F0,F1,[(Bool=CB)|PCs0],PCs1) :-
	definedAtom(B,PreTrees),	% each call gets renamed apart
	!,
	makeEqualities(Xs,Ys,Eqs),
	makeCall(B,Xs,CB,Ys),
	expand(Bs,V,Bs1,PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1).
expand([B|Bs],V,[Def|Bs1],PreTrees,Ms,Hs0,Hs2,F0,F1,PCs0,PCs2) :-
	treeDef(B,V,PreTrees,Ms,Hs0,Hs1,Def,[],PCs0,PCs1),
	expand(Bs,V,Bs1,PreTrees,Ms,Hs1,Hs2,F0,F1,PCs1,PCs2).
	
expandOrReuse(CB,_,_,_,_,Hs,Hs,F,F,PCs,PCs) :-
	member(used(CB),Hs),		% unifies CB with previous copy
	!.
expandOrReuse(CB,B,V,PreTrees,Ms,Hs0,Hs1,F0,F1,PCs0,PCs1) :-
	treeDef(B,V,PreTrees,Ms,[used(CB)|Hs0],Hs1,F0,F1,PCs0,PCs1).
	
selectOrReuse(CB,_,Hs,Hs,PCs,PCs) :-
	member(used(CB),Hs), 		% select the one already defined
	!.
selectOrReuse(CB,Bool,Hs,[used(CB)|Hs],[(Bool=CB)|PCs],PCs).

	
	
makeEqualities([],[],[]).
makeEqualities([X|Xs],[Y|Ys],[X=Y|Eqs]) :-
	makeEqualities(Xs,Ys,Eqs).

boolvars([B=_|PCalls],[B|Bools]) :-
	boolvars(PCalls,Bools).
boolvars([],[]).
	
definedPred(P/N,PreTrees,Ms) :-
	member(preTrees(P/N,_),PreTrees),
	\+ member(P/N,Ms).
	
definedAtom(B,PreTrees) :-
	functor(B,P,N),
	member(preTrees(P/N,_),PreTrees).
	
mergePoint(B,P,N,Ms) :-
	functor(B,P,N),
	member(P/N,Ms).
	
singleCall(B,V,PreTrees) :-
	functor(B,P,N),
	member(preTrees(P/N,Ws),PreTrees),
	member([V],Ws).		% only one call to P/N in V's tree
	

makeCall(B,Xs,CB,Ys) :-
	functor(B,P,N),
	functor(CB,P,N),
	B =..  [P|Xs],
	CB =.. [P|Ys].

writeList([],_).
writeList([X|Xs],S) :-
	write(S,X),
	write(S,'.'),
	nl(S),
	writeList(Xs,S).
	
pdef(H,Def) :-
	findall((H,B), my_clause(H,B,_), Bs),
	makeDef(H,Bs,Def).
	
makeDef(H,[(H,B)],B) :-
	!.
makeDef(H,[(H,B)|Bs],(B;Bs1)) :-
	makeDef(H,Bs,Bs1).
makeDef(_,[],0=1).

treePartition(Vs,TEs,CEs,BEs,Es1) :-
	initTreeClasses(Vs,root,Es0),
	addEdgeConstraints(TEs,CEs,BEs,Es0,Es1).

initTreeClasses([],Es,Es).
initTreeClasses([X|Xs],Es0,Es2) :-
	make(X,Es0,Es1),
	!,
	initTreeClasses(Xs,Es1,Es2).
	
addEdgeConstraints([P-Q|Cs],CEs,BEs,Es0,Es2) :-
	nonRoot(Q,CEs,BEs),
	!,
	merge(P,Q,Es0,Es1,_),
	addEdgeConstraints(Cs,CEs,BEs,Es1,Es2).
addEdgeConstraints([_|Cs],CEs,BEs,Es0,Es1) :-
	addEdgeConstraints(Cs,CEs,BEs,Es0,Es1).
addEdgeConstraints([],_,_,Es0,Es0).

nonRoot(Q,CEs,BEs) :-
	\+ edgeTarget(Q,CEs),
	\+ edgeTarget(Q,BEs).
	
edgeTarget(Q,Xs) :-
	member(_-Q,Xs).
	
mergeTrees([V|Vs],Roots,Edges,RSs,PreTrees,Ts0,Ts1,Ms) :-
	member(V,Roots),
	!,
	classifyTree(V,PreTrees,RSs,Ts0,TType),
	mergeTrees1(TType,V,Vs,Roots,Edges,RSs,PreTrees,Ts0,Ts1,Ms).
mergeTrees([_|Vs],Roots,Edges,RSs,PreTrees,Ts0,Ts1,Ms) :-	% not a root node
	mergeTrees(Vs,Roots,Edges,RSs,PreTrees,Ts0,Ts1,Ms).
mergeTrees([],_,_,_,_,Ts,Ts,[]).


mergeTrees1(noMerge,_,Vs,Roots,Edges,RSs,PreTrees,Ts0,Ts1,Ms) :-		% noMerge
	mergeTrees(Vs,Roots,Edges,RSs,PreTrees,Ts0,Ts1,Ms).
mergeTrees1(merge(W),V,Vs,Roots,Edges,RSs,PreTrees,Ts0,Ts2,[V|Ms]) :-	% merge trees V and W
	merge(W,V,Ts0,Ts1,_),
	mergeTrees(Vs,Roots,Edges,RSs,PreTrees,Ts1,Ts2,Ms).
	
classifyTree(V,PreTrees,RSs,Ts0,merge(W)) :-		% only one pre-tree, and single-context
	member(preTrees(V,[[W,W|_]]),PreTrees),	
	\+ multiContext(V,W,RSs,Ts0),
	!.
classifyTree(_,_,_,_,noMerge).						% otherwise do not merge.

multiContext(V,W,RSs,Ts0) :-
	treeNodes(W,Ts0,Ns),
	reachedFrom(V,RSs,VRs),
	andNodes(Ns,N1,N2),
	member(N1,VRs),
	member(N2,VRs),
	!.
	
andNodes([N|_],N1,N2) :-
	nonLinClause(N,N1,N2).
andNodes([_|Ns],N1,N2) :-
	andNodes(Ns,N1,N2).
	
nonLinClause(P/N,F1/N1,F2/N2) :-
	functor(H,P,N),
	my_clause(H,Bs,_),
	append(_,[B1|Bs1],Bs),
	\+ isConstraint(B1),
	functor(B1,F1,N1),
	append(_,[B2|_],Bs1),
	\+ isConstraint(B2),
	functor(B2,F2,N2).
	
	
parentTreeList([V|Vs],Edges,Trees,[preTrees(V,Ws)|PTs]) :-
	parentTrees(V,Edges,Trees,Ws),
	parentTreeList(Vs,Edges,Trees,PTs).
parentTreeList([],_,_,[]).


parentTrees(V,Edges,Trees,Ws) :-
	predecessors(V,Edges,Preds),
	parents(Preds,Trees,Ps),
	groupByTree(Ps,Ws).
	
parents([Q|Qs],Trees,[A|As]) :-
	findSimple(_,Q,Trees,data(A,_)),
	parents(Qs,Trees,As).
parents([],_,[]).
	
groupByTree([P|Ps],Ws) :-
	groupByTree(Ps,Ws1),
	insertInGroup(P,Ws1,Ws).
groupByTree([],[]).

insertInGroup(P,[],[[P]]).						% first occurrence of P
insertInGroup(P,[[P|Ps]|Gs],[[P,P|Ps]|Gs]) :- 	% found another P
	!.
insertInGroup(P,[G|Gs],[G|Gs1]) :-
	insertInGroup(P,Gs,Gs1).

	
treeRoots(TP,Roots) :-
	traverse_tree(TP,Nodes),
	rootNodes(Nodes,Roots).

rootNodes([rec(W,data(V,_))|Nodes],[W|Roots]) :-
	W==V,
	!,
	rootNodes(Nodes,Roots).
rootNodes([_|Nodes],Roots) :-
	rootNodes(Nodes,Roots).
rootNodes([],[]).
	
treeNodes(W,Ts0,Ns) :-
	findSimple(_,W,Ts0,data(V,Ns1)),	% find the tree root
	(V==W -> Ns=Ns1; findSimple(_,V,Ts0,data(V,Ns))).
	
reachedFrom(V,RSs,VRs) :-
	member(reach(V,VRs),RSs).
	
makeHeads([P/N|Ss],Ms,[P/N|Hs]) :-
	makeHeads(Ss,Ms,Hs).
makeHeads([],Ms,Hs) :-
	makeHeads1(Ms,Hs).
	
makeHeads1([P/N|Ms],[P/N|Hs]) :-
	makeHeads1(Ms,Hs).
makeHeads1([],[]).


	

makeClauseId(K,CK) :-
	name(K,NK),
	append("c",NK,CNK),
	name(CK,CNK).