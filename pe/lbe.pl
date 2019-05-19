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
	reachableSets(Roots,Es,RSs),
	reverse(RVs,Stack),
	mergeTrees(Stack,Roots,Es,RSs,TP,_TP1,Ms,MCs,Ss), 
	
	%write(OutS,		'Multitree: '), write(OutS,Ms),nl(OutS),
	%write(OutS,		'Singletree: '), write(OutS,Ss),nl(OutS),
	%write(OutS,		'Multicontext: '), write(OutS,MCs),nl(OutS),
	%write(OutS,		'Reachable: '), write(OutS,RSs),nl(OutS),
	
	makeHeads(Ss,Ms,Hs),
	unfoldBlocks(RVs,P/N,Ms,MCs,Ss,Hs,Defs).
	
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
	
unfoldBlocks([P|Ps],S,Ms,MCs,Ss,Hs,[PDef|Defs]) :-
	definedPred(P,S,Ms,MCs),
	!,
	unfoldBlock(P,Ms,MCs,Ss,Hs,PDef),
	unfoldBlocks(Ps,S,Ms,MCs,Ss,Hs,Defs).
unfoldBlocks([_|Ps],S,Ms,MCs,Ss,Hs,Defs) :-
	unfoldBlocks(Ps,S,Ms,MCs,Ss,Hs,Defs).
unfoldBlocks([],_,_,_,_,_,[]).
	
unfoldBlock(F/N,Ms,MCs,Ss,Hs,(A:-Def,PCalls)) :-
	!,
	functor(A,F,N),
	treeDef(A,Ms,MCs,Ss,Hs,_,Def,[],PCalls,[]),
	numbervars((A:-Def,PCalls),0,_).

treeDef(A,Ms,MCs,Ss,Hs0,Hs1,[Def|F0],F1,PCs0,PCs1) :-
	pdef(A,E),
	expand(E,Def,Ms,MCs,Ss,Hs0,Hs1,F0,F1,PCs0,PCs1).

expand((B1;B2),(C1;C2),Ms,MCs,Ss,Hs0,Hs2,F0,F2,PCs0,PCs2) :-
	!,
	expand(B1,C1,Ms,MCs,Ss,Hs0,Hs1,F0,F1,PCs0,PCs1),
	expand(B2,C2,Ms,MCs,Ss,Hs1,Hs2,F1,F2,PCs1,PCs2).
expand([],[],_,_,_,Hs,Hs,F,F,PCs,PCs) :-
	!.
expand([B|Bs],[C|Bs1],Ms,MCs,Ss,Hs0,Hs1,F0,F1,PCs0,PCs1) :-
	constraint(B,C),
	!,
	expand(Bs,Bs1,Ms,MCs,Ss,Hs0,Hs1,F0,F1,PCs0,PCs1).
expand([B|Bs],[Eqs|Bs1],Ms,MCs,Ss,Hs0,Hs2,F0,F2,PCs0,PCs2) :-
	singleContext(B,P,N,Ss),
	!,
	functor(CB,P,N),
	B =.. [P|Xs],
	CB =.. [P|Ys],
	makeEqualities(Xs,Ys,Eqs),
	expandOrReuse(CB,B,Ms,MCs,Ss,Hs0,Hs1,F0,F1,PCs0,PCs1),
	expand(Bs,Bs1,Ms,MCs,Ss,Hs1,Hs2,F1,F2,PCs1,PCs2).
expand([B|Bs],[Eqs,Bool|Bs1],Ms,MCs,Ss,Hs0,Hs1,F0,F1,[(Bool=CB)|PCs0],PCs1) :-
	multiContextCall(B,MCs),
	!,
	makeEqualities(Xs,Ys,Eqs),
	makeCall(B,Xs,CB,Ys),
	expand(Bs,Bs1,Ms,MCs,Ss,Hs0,Hs1,F0,F1,PCs0,PCs1).
expand([B|Bs],[Eqs,Bool|Bs1],Ms,MCs,Ss,Hs0,Hs2,F0,F1,PCs0,PCs2) :-
	leafCall(B,P,N,Ms),
	!,
	functor(CB,P,N),
	B =.. [P|Xs],
	CB =.. [P|Ys],
	makeEqualities(Xs,Ys,Eqs),
	selectOrReuse(CB,Bool,Hs0,Hs1,PCs0,PCs1),
	expand(Bs,Bs1,Ms,MCs,Ss,Hs1,Hs2,F0,F1,PCs1,PCs2).
expand([B|Bs],[Def|Bs1],Ms,MCs,Ss,Hs0,Hs2,F0,F1,PCs0,PCs2) :-
	treeDef(B,Ms,MCs,Ss,Hs0,Hs1,Def,[],PCs0,PCs1),
	expand(Bs,Bs1,Ms,MCs,Ss,Hs1,Hs2,F0,F1,PCs1,PCs2).
	
expandOrReuse(CB,_,_,_,_,Hs,Hs,F,F,PCs,PCs) :-
	member(used(CB,_Bool),Hs),
	!.
expandOrReuse(CB,B,Ms,MCs,Ss,Hs0,Hs2,F0,F1,PCs0,PCs1) :-
	firstUse(CB,_Bool,Hs0,Hs1),
	treeDef(B,Ms,MCs,Ss,Hs1,Hs2,F0,F1,PCs0,PCs1).
	
selectOrReuse(CB,Bool,Hs,Hs,PCs,PCs) :-
	member(used(CB,Bool),Hs),
	!.
selectOrReuse(CB,Bool,Hs0,Hs1,[(Bool=CB)|PCs],PCs) :-
	firstUse(CB,Bool,Hs0,Hs1).

firstUse(CB,Bool,[P/N|Hs],[used(CB,Bool)|Hs]) :- 	% record that CB has been used
	functor(CB,P,N),
	!.
firstUse(CB,Bool,[H|Hs],[H|Hs1]) :-
	firstUse(CB,Bool,Hs,Hs1).
	
makeEqualities([],[],[]).
makeEqualities([X|Xs],[Y|Ys],[X=Y|Eqs]) :-
	makeEqualities(Xs,Ys,Eqs).

boolvars([B=_|PCalls],[B|Bools]) :-
	boolvars(PCalls,Bools).
boolvars([],[]).
	
multiContextCall(B,MCPs) :-
	functor(B,P,N),
	member(P/N,MCPs).
	
leafCall(B,P,N,Ms) :-
	functor(B,P,N),
	member(P/N,Ms).
	
singleContext(B,P,N,Ss) :-
	functor(B,P,N),
	member(P/N,Ss).

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
	
mergeTrees([V|Vs],Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss) :-
	member(V,Roots),
	!,
	parentTrees(V,Edges,Ts0,Ws),
	classifyTree(V,Ws,RSs,Ts0,TType),
	mergeTrees1(TType,V,Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss).
mergeTrees([_|Vs],Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss) :-	% not a root node
	mergeTrees(Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss).
mergeTrees([],_,_,_,Ts,Ts,[],[],[]).


mergeTrees1(multiTree,V,Vs,Roots,Edges,RSs,Ts0,Ts1,[V|Ms],MCs,Ss) :-	% multi-tree
	!,
	mergeTrees(Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss).
mergeTrees1(multiContext,V,Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,[V|MCs],Ss) :- % multi-context	
	!,
	mergeTrees(Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss).
mergeTrees1(singleContext(W),V,Vs,Roots,Edges,RSs,Ts0,Ts2,Ms,MCs,[V|Ss]) :-	% single-context
	merge(W,V,Ts0,Ts1,_),
	mergeTrees(Vs,Roots,Edges,RSs,Ts1,Ts2,Ms,MCs,Ss).
mergeTrees1(rootContext,V,Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,[V|Ss]) :-	% root-context
	mergeTrees(Vs,Roots,Edges,RSs,Ts0,Ts1,Ms,MCs,Ss).
	
classifyTree(V,Ws,RSs,Ts0,multiContext) :-
	member(W,Ws),
	treeNodes(W,Ts0,Ns),
	reachedFrom(V,RSs,VRs),
	andNodes(Ns,N1,N2),
	member(N1,VRs),
	member(N2,VRs),
	!.
classifyTree(_,[_,_|_],_,_,multiTree) :-		% at least two parent trees
	!.
classifyTree(_,[],_,_,rootContext) :-			% root context
	!.
classifyTree(_,[W],_,_,singleContext(W)) :-		% else single-context, single-tree
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
	
parentTrees(V,Edges,Trees,Ws) :-
	predecessors(V,Edges,Qs),	
	(setof(W,[Q,N,D]^(member(Q,Qs),findSimple(N,Q,Trees,data(W,D))),Ws) -> true; Ws = []).
	
	
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


definedPred(P,P,_,_) :-
	!.
definedPred(P,_,Ms,_) :-
	member(P,Ms),
	!.
definedPred(P,_,_,MCs) :-
	member(P,MCs).
	

makeClauseId(K,CK) :-
	name(K,NK),
	append("c",NK,CNK),
	name(CK,CNK).