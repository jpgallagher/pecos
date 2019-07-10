:- module(elimVars, _, [assertions, isomodes, doccomments,dynamic]).
%! \title Quantifier elimination using Monniaux algorithm
% arXiv:0803.1575v2 [cs.LO] 4 Sep 2008 and LPAR 2008
% David Monniaux: A Quantifier Elimination Algorithm for Linear Real Arithmetic.

:- use_module(library(read)).
:- use_module(library(write)).
:- use_module(library(streams)).
:- use_module(library(aggregates)).

:- use_module(library(terms_vars)).
:- use_module(library(lists)).
:- use_module(library(stream_utils)).
:- use_module(library(ppl)).

:- use_module(chclibs(common)).
:- use_module(chclibs(setops)).
:- use_module(chclibs(canonical)).
:- use_module(chclibs(linearize)).
:- use_module(chclibs(timer_ciao)).
:- use_module(chclibs(ppl_ops)).
:- use_module(chclibs(program_loader)).
:- use_module(chclibs(yices2_sat)).
:- use_module(ciao_yices(ciao_yices_2)).

:- use_module(lbe).

:- include(chclibs(messages)).

:- dynamic flag/1.

main([File]) :-
	start_ppl,
	yices_init,
	getFormula(File,F),					% first term in File is F of the form (H:-B)
	quantifiedVariables(F,B,Xs,Ys), 	% forall Xs. exists Ys. B
	yices_context(Ctx),
	length(Xs,N),
	varTypes(Xs,real,Vs),
	declareVars(Vs),
	existElim(B,Ys,N,false,O,B,Ctx),
	yices_free_context(Ctx),
	write(O),nl,
	yices_exit,
	end_ppl.

% function ExistElim defined in Monniaux 2008.  Eliminate Ys from F
existElim(F,Ys,N,O1,O2,H,Ctx) :-
	checkSat(H,Status,Ctx),
	existElimLoop(Status,Ctx,F,Ys,N,O1,O2,H).
	
existElimLoop(satisfiable,Ctx,F,Ys,N,O1,O2,H) :-
	yices_get_model(Ctx,1,Model),
	generalize1(Model,F,M1),
	generalize2(Ctx,neg(F),M1,M2),
	%M1 = M2,
	elimVarsConjunct(M2,Ys,N,Pi),
	yices_reset_context(Ctx),
	existElim(F,Ys,N,(O1;Pi),O2,[H,neg(Pi)],Ctx).
existElimLoop(unsatisfiable,_,_,_,_,O,O1,_) :-
	removeFalse(O,O1).

% function Generalize1 defined in Monniaux 2008
generalize1(Model,F,M) :-
	atomicConstraints(F,As,[]),
	testAllAtoms(As,Model,M).
	
% function Generalize2 defined in Monniaux 2008
generalize2(Ctx,G,M,M2) :-
	length(M,N),
	testAllConjuncts(N,Ctx,G,M,M2).
	
	
testAllAtoms([],_,[]).
testAllAtoms([C|As],Model,[C|Cs]) :-
	trueInModel(C,Model),
	!,
	testAllAtoms(As,Model,Cs).
testAllAtoms([X=Y|As],Model,[X>Y|Cs]) :-
	trueInModel(X>Y,Model),
	!,
	testAllAtoms(As,Model,Cs).
testAllAtoms([X=Y|As],Model,[X<Y|Cs]) :-
	trueInModel(X<Y,Model),
	!,
	testAllAtoms(As,Model,Cs).
testAllAtoms([C|As],Model,[NC|Cs]) :-
	negateAtom(C,NC),
	testAllAtoms(As,Model,Cs).
	
testAllConjuncts(0,_,_,M,M).
testAllConjuncts(K,Ctx,G,M,M2) :-
	removeKth(K,M,M1),
	isUnsat(Ctx,[M1,G]),
	!,
	K1 is K-1,
	testAllConjuncts(K1,Ctx,G,M1,M2).
testAllConjuncts(K,Ctx,G,M,M2) :-
	K1 is K-1,
	testAllConjuncts(K1,Ctx,G,M,M2).
	
isSat(Ctx,Phi) :-
	checkSat(Phi,StatusName,Ctx),
	StatusName==satisfiable.
	
isUnsat(Ctx,Phi) :-
	checkSat(Phi,StatusName,Ctx),
	StatusName==unsatisfiable.
	
negateAtom(X>Y,X=<Y).
negateAtom(X>=Y,X<Y).
negateAtom(X<Y,X>=Y).
negateAtom(X=<Y,X>Y).
	
checkSat(E,StatusName,Ctx) :-
	expr2yices(E,Y),
	yices_parse_term(Y,T),
	check_no_error(T),
	yices_reset_context(Ctx),
	yices_assert_formula(Ctx,T,_Status),
	yices_check(Ctx,StatusName).
	
atomicConstraints((D1;D2),As0,As2) :-
	!,
	atomicConstraints(D1,As0,As1),
	atomicConstraints(D2,As1,As2).
atomicConstraints([C|Cs],As0,As2) :-
	!,
	atomicConstraints(C,As0,As1),
	atomicConstraints(Cs,As1,As2).
atomicConstraints(false,As,As) :-
	!.
atomicConstraints([],As,As) :-
	!.
atomicConstraints(neg(A),As0,As1) :-
	!,
	atomicConstraints(A,As0,As1).
atomicConstraints(A,[A|As],As) :-
	linear_constraint(A),
	!.
atomicConstraints(_,As,As).

trueInModel(C,Model) :-
	expr2yices(C,CExpr),
	yices_parse_term(CExpr,E),
	yices_formula_true_in_model(Model,E,V),
	V==1.
	

	
check_no_error(S) :-
	( S<0 -> report_error
	; true
	).
	
report_error :-
	yices_error_string(E),
	write_string(E),nl,
	throw(yices_error(E)).
	
declareVars([(X,Tau)|Vars]) :- !,
	expr2yices(X,V),
	yices_declare_var(Tau,V),
	declareVars(Vars).
declareVars([]).

varTypes([],_,[]).
varTypes([X|Xs],T,[(X,T)|Ys]) :-
	varTypes(Xs,T,Ys).
	
getFormula(File, (H :- B)) :-
	open(File,read,S),
	read(S,F),
	(F = (H:-B) -> true; 
	               write('Error, no formula found'),
	               nl),
	close(S).
	
quantifiedVariables((H:-B),B,Xs,Ys) :-
	varset((H:-B),Xs),
	varset(B,Zs),
	setdiff(Zs,Xs,Ys),
	numbervars(Xs,0,_).

allNeg([],[]) :-
	!.
allNeg([B|Bs],[neg(B)|Ns]) :-
	allNeg(Bs,Ns).
	
list2disjunct([],false) :-
	!.
list2disjunct([B],B) :-
	!.
list2disjunct([B|Bs],(B;Ds)) :-
	list2disjunct(Bs,Ds).
	
removeFalse((false;O),O) :-
	!.
removeFalse((C;O1),(C;O2)) :-
	removeFalse(O1,O2).
	
extendDim(H,N) :-
	ppl_Polyhedron_space_dimension(H,M),
	(M<N -> 
		D is N-M, ppl_Polyhedron_add_space_dimensions_and_embed(H,D);
		true).

removeKth(1,[_|Xs],Xs).
removeKth(K,[X|Xs],[X|Ys]) :-
	K>1,
	K1 is K-1,
	removeKth(K1,Xs,Ys).

elimVarsConjunct(F0,Ys,N,F1) :-
	makePolyhedron(F0,H),
	extendDim(H,N),
	project(H,Ys,H1),
	getConstraint(H1,F1).

