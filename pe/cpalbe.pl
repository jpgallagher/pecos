:- module(cpalbe, _, [assertions, isomodes, doccomments,dynamic]).
%! \title Convex Polyhedra Analysis 
% with SAT-based fixpoint checking and large block encoding 

:- use_module(library(read)).
:- use_module(library(write)).
:- use_module(library(streams)).
:- use_module(library(aggregates)).

:- use_module(chclibs(common)).

:- use_module(chclibs(setops)).
:- use_module(chclibs(canonical)).
:- use_module(chclibs(wto)).
:- use_module(chclibs(linearize)).
:- use_module(library(terms_vars)).
:- use_module(library(ppl)).
:- use_module(library(lists)).
:- use_module(chclibs(timer_ciao)).
:- use_module(chclibs(ppl_ops)).
:- use_module(chclibs(scc)).
:- use_module(chclibs(program_loader)).
:- use_module(lbe).
:- use_module(elimVars).

:- use_module(chclibs(yices2_sat)).
:- use_module(ciao_yices(ciao_yices_2)).

:- include(chclibs(get_options)).
:- include(chclibs(messages)).

:- dynamic(flag/1).
:- dynamic(currentflag/1).
:- dynamic(nextflag/1).
:- dynamic(operatorcount/1).
:- dynamic(widening_point/3).
:- dynamic(outputfile/1).
:- dynamic(newfact/3).
:- dynamic(oldfact/3).
:- dynamic(prio_widen/1).
:- dynamic(widenAt/1).
:- dynamic(widenf/1).
:- dynamic(detectwps/1).
:- dynamic(delays/1).
:- dynamic(clauseCount/1).
:- dynamic(invariant/2).
:- dynamic(versionCount/1).
:- dynamic(versiontransition/2).
:- dynamic(version/3).
:- dynamic(clauseCount/1).
:- dynamic(pathtransition/1).
:- dynamic(atomicproposition/1).
:- dynamic cEx/1.
:- dynamic threshold/1.
:- dynamic traceTerm/2.


go(File) :-
	go2(File,temp).
	
go2(FileIn,FileOut) :-
	cpalbe:main(
		['-prg',FileIn,
		'-widenpoints','widenpoints',
		'-widenout','widencns',
		'-withwut',
		'-wfunc','h79',
		'-threshold','wut.props',
		'-o',FileOut]).
			
recognised_option('-prg',programO(R),[R]).
recognised_option('-widenpoints',widenP(R),[R]).
recognised_option('-widenout',widenO(R),[R]).
recognised_option('-wfunc',widenF(F),[F]).
recognised_option('-v',verbose,[]). % some verbose
recognised_option('-debug-print',debug_print,[]). % detailed comments
recognised_option('-querymodel',querymodel(Q),[Q]).
recognised_option('-nowpscalc',nowpscalc,[]).
recognised_option('-withwut',withwut,[]).
recognised_option('-detectwps',detectwps(M),[M]).
recognised_option('-o',factFile(F),[F]).
recognised_option('-cex',counterExample(F),[F]).
recognised_option('-threshold',thresholdFile(F),[F]).
	
main(['-prg',FileIn]) :-
	!,
	go(FileIn).		
main(['-prg',FileIn, '-o', FileOut]) :-
	!,
	go2(FileIn,FileOut).
main(ArgV) :-
	verbose_message(['Starting Convex Polyhedra analysis']),
	cpalbe:get_options(ArgV,Options,_),
	cleanWorkspace,
	cpalbe:set_options(Options,File,FactFile),
	initialise,
	( flag(verbose) -> start_time ; true ),
	Entry = false,
	assertLBE(File,Entry),
	cpalbe:dependency_graph(Es,Vs),
	scc_graph(Es,Vs,G),
	start_ppl,
	yices_init,
	iterate(G),
	verbose_message(['Convex Polyhedra Analysis Succeeded']),
	( flag(verbose) -> end_time(user_output) ; true ),
	!,
	factFile(FactFile),
	%generateCEx,
	yices_exit,
	ppl_finalize.
/*
generateCEx:-
	cEx('$NOCEX'),
	!.
generateCEx :-
	cEx(CexFile),
	open(CexFile,write,S),
	findCounterexampleTrace(S),
	close(S).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Iterate solves each component 
% recursive components involve iterative fixpoint
% non-recursive components solved in one step
% with no abstraction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterate([(non_recursive,[P])|SCCs]) :-
	debug_message(['Non-recursive component ',P]),
	(flag(first) -> true; assertz(flag(first))),
	non_recursive_scc(P),
	!,
	iterate(SCCs).
iterate([(recursive,Ps)|SCCs]) :-
	debug_message(['Recursive component ',Ps]),
	(flag(first) -> true; assertz(flag(first))),
	recursive_scc(Ps),
	!,
	iterate(SCCs).
iterate([]).

non_recursive_scc(P/N) :-
	functor(A,P,N),
	lbe_clause(A,Def,PCalls,_),
	(solutionConstraint(A,Def,PCalls,(A,Phi,Ids,AllBools)), Phi \== false -> 
		(isSat(Phi,AllBools) ->			% numbervars is called within isSat
			removeExistsVars(A,AllBools,Phi,Phi1),	
			(Phi1=(_;_) -> Phi2=[Phi1]; Phi2=Phi1),
			record(A,nonrecPred(Phi2),[],Ids);
			true)
		;
		true
	),
	incrementOperatorCount,
	newoldfacts,
	switch_flags.
	
recursive_scc(Ps) :-
	sccIterate(Ps),
	(not_converged ->
		incrementOperatorCount,
		widen,
		newoldfacts,
		switch_flags,
		!,
		recursive_scc(Ps);
	true).
		
sccIterate([P/N|Ps]) :-
	functor(A,P,N),
	lbe_clause(A,B,C,_),
	solutionConstraint(A,B,C,(A,Phi,Ids,AllBools)), 
	solveAndUpdate(A,Phi,Ids,AllBools),
	sccIterate(Ps).
sccIterate([]).
	
solveAndUpdate(A,Phi,Ids,Bools) :-
	(getoldfact(A,Psi,[],_) -> true; Psi=false),	% no booleans in recursive approx.
	varset((A,Phi),Vars),
	setdiff(Vars,Bools,Reals),
	numbervars(Vars,0,_), 
	yices_context(Ctx),
	checkSat(Ctx,[neg(Psi),Phi],Reals,Bools,StatusName),
	(StatusName==satisfiable -> 
		% sat(and(not(Psi),Phi)) ==> there is a new soln. for A
		updateRecursiveApprox(A,Ctx,[neg(Psi),Phi],Bools,Ids)
		;
		true
	),
	yices_free_context(Ctx).
	
checkSat(Ctx,E,Reals,Bools,StatusName) :-
	expr2yices(E,Y),
	varTypes(Reals,real,Us),
	varTypes(Bools,bool,Vs),
	declareVars(Us),
	declareVars(Vs),
	yices_parse_term(Y,T),
	check_no_error(T),
	yices_assert_formula(Ctx,T,_Status),
	yices_check(Ctx,StatusName).
		
updateRecursiveApprox(A,Ctx,Phi,Bools,Ids) :-
	yices_get_model(Ctx,1,Model),
	buildConjunct(Phi,Model,Bools,APhi),
	melt((A,APhi),(A1,APhi1)),
	varset(A1,Xs),
	varset((A1,APhi1),Ys),
	numbervars((A1,APhi1),0,_),
	length(Ys,N),
	makePolyhedron(APhi1,H1),
	extendDim(H1,N),
	setdiff(Ys,Xs,Zs),
	project(H1,Zs,Hp),
	getConstraint(Hp,Cs),
	record(A,recPred(Cs),[],Ids).
	
buildConjunct(Phi,Model,Bools,Cs) :-
	atomicConstraints(Phi,Bools,As,[]),
	checkTrue(As,Model,Cs).
	
atomicConstraints((D1;D2),Bools,As0,As2) :-
	!,
	atomicConstraints(D1,Bools,As0,As1),
	atomicConstraints(D2,Bools,As1,As2).
atomicConstraints([C|Cs],Bools,As0,As2) :-
	!,
	atomicConstraints(C,Bools,As0,As1),
	atomicConstraints(Cs,Bools,As1,As2).
atomicConstraints(false,_,As,As) :-
	!.
atomicConstraints([],_,As,As) :-
	!.
atomicConstraints(neg(A),Bools,As0,As1) :-
	!,
	atomicConstraints(A,Bools,As0,As1).
atomicConstraints(X=E,Bools,As0,As1) :-
	member(X,Bools),
	!,
	atomicConstraints(E,Bools,As0,As1).
atomicConstraints(A,_,[A|As],As) :-
	linear_constraint(A),
	!.
atomicConstraints(_,_,As,As).

checkTrue([],_,[]).
checkTrue([C|As],Model,[C|Cs]) :-
	trueInModel(C,Model),
	!,
	checkTrue(As,Model,Cs).
checkTrue([_|As],Model,Cs) :-
	checkTrue(As,Model,Cs).

trueInModel(C,Model) :-
	expr2yices(C,CExpr),
	yices_parse_term(CExpr,E),
	yices_formula_true_in_model(Model,E,V),
	V==1.
	
yicesVarNames(['$VAR'(X)|Bs],[Y|Ys]) :-
	name(X,Xn),
	append("x",Xn,Y),
	yicesVarNames(Bs,Ys).
yicesVarNames([],[]).	
	
check_no_error(S) :-
	( S<0 -> report_error
	; true
	).
	
report_error :-
	yices_error_string(E),
	throw(yices_error(E)).
	
declareVars([(X,Tau)|Vars]) :- !,
	expr2yices(X,V),
	yices_declare_var(Tau,V),
	declareVars(Vars).
declareVars([]).

varTypes([],_,[]).
varTypes([X|Xs],T,[(X,T)|Ys]) :-
	varTypes(Xs,T,Ys).
	
solutionConstraint(A,Def,PCalls,(A,[Def|Ans],[],AllBools)) :-
	prove(PCalls,Ans,Bools,OBs),
	appendall([Bools|OBs],AllBools). 
	
appendall([],[]).
appendall([Bs|Bools],AllBs) :-	
	appendall(Bools,AllBs1),
	append(Bs,AllBs1,AllBs).
	
isSat(Phi,Bools) :-
	varset(Phi,Vars),
	setdiff(Vars,Bools,Reals),
	numbervars(Vars,0,_),
	yices_context(Ctx),
	checkSat(Ctx,Phi,Reals,Bools,StatusName),
	StatusName==satisfiable,
	yices_free_context(Ctx).
	
potentialChange(B) :-
	(changed(B) -> true; flag(first)).

prove([],[],[],[]).
prove([(Bool=B)|Bs],[(Bool=CsOld)|Cs],[Bool|Bools],[OldBools|OBs]):-
	getoldfact(B,CsOld,OldBools,_),
	!,
	prove(Bs,Cs,Bools,OBs).
prove([(Bool=_)|Bs],[(Bool=false)|Cs],[Bool|Bools],OBs):-
	prove(Bs,Cs,Bools,OBs).
	
getoldfact(B,Cs1,Bools1,T) :-
	functor(B,F,N),
	functor(B1,F,N),
	oldfact(B1,Cs,Bools),
	melt((B1,Cs,Bools),(B,Cs1,Bools1)),
	traceTerm(B1,T).
	
allFalse([],[]) :-
	!.
allFalse([B|Bs],[neg(B)|Ns]) :-
	allFalse(Bs,Ns).
	
list2disjunct([],false) :-
	!.
list2disjunct([B],B) :-
	!.
list2disjunct([B|Bs],(B;Ds)) :-
	list2disjunct(Bs,Ds).
	
incrementOperatorCount :-
	retract(operatorcount(X)),
	Y is X + 1,
	assertz(operatorcount(Y)).
	
removeExistsVars(A,Bools,Phi,Phi1) :-
	melt((A,Phi,Bools),(A1,Phi2,Bools1)),
	varset((A1,Phi2),Xs),	% all vars
	varset(Phi2,Zs),		% body vars
	setdiff(Zs,Xs,Ys),		% exists vars
	numbervars(Xs,0,_),
	elimVars(Phi2,Xs,Ys,Bools1,Phi1).
	

/*

findSatPath([Y|Ys],[B|Bs],Model,[B|Path]) :-
	yices_get_term_by_name(Y,YN),
	yices_get_bool_value(Model,YN,V,_StB),
	V > 0, 	% B is true in the model, hence on the path
	!,
	findSatPath(Ys,Bs,Model,Path).
findSatPath([_|Ys],[_|Bs],Model,Path) :-
	findSatPath(Ys,Bs,Model,Path). % omit vars that are not on the path
findSatPath([],[],_,[]).


extractPathConstraints(([B|Phi]; _),Path,APsi) :-
	member(B,Path), 	% it is on the path
	!,
	extractPathConstraints(Phi,Path,APsi).
extractPathConstraints((_;F),Path,APsi) :-
	!,
	extractPathConstraints(F,Path,APsi).
extractPathConstraints([oneHot(_)|Phi],Path,APsi) :-
	!,					% ignore oneHot constraints
	extractPathConstraints(Phi,Path,APsi).
extractPathConstraints([B|Phi],Path,APsi) :-
	member(B,Path), 	% Phi is on the path
	!,
	extractPathConstraints(Phi,Path,APsi).
extractPathConstraints([F1|F2],Path,APsi) :-
	!,
	extractPathConstraints(F1,Path,APsi1),
	extractPathConstraints(F2,Path,APsi2),
	append(APsi1,APsi2,APsi).
extractPathConstraints([],_,[]) :-
	!.
extractPathConstraints(F,_,[F]) :-
	arithConstraint(F).
	

	
arithConstraint(F) :-
	F =.. [P|_],
	member(P,['=','<','>','>=','=<','==','=:=', 'neq']).
	
*/

	
not_converged :-
	nextflag(_).

changed(Bs) :- 
	member(B,Bs),
	\+ formula(B),
	isflagset(B),
	!.

%%%%%%%%%%%%%%%%%
%  new/old facts
%%%%%%%%%%%%%%%%%

switch_flags :-
	retractall(currentflag(_/_)),
	retract(nextflag(F/N)),
	assertz(currentflag(F/N)),
	fail.
switch_flags :-
	true.

isflagset(F) :-
	functor(F,Fn,N),
	currentflag(Fn/N).

raise_flag(F):-
	functor(F,Fn,N),
	( nextflag(Fn/N) ->
	    true
	; assertz(nextflag(Fn/N))
	).

record(F,nonrecPred(Cs),Bools,T) :-
	cond_assert_nonrec(F,Cs,Bools,T).
	
record(F,recPred(Cs),_,T) :-
	cond_assert_rec(F,Cs,T).
	
cond_assert_nonrec(F,Cs,Bools,T):-
	%write('Asserting...'),nl,
	assertz(newfact(F,Cs,Bools)),
	raise_flag(F),
	(traceTerm(F,_) -> true; assertz(traceTerm(F,T))).
	%write(traceTerm(F,T)),nl).
	

cond_assert_rec(F,Cs,T):-
	functor(F,_,N),
	makePolyhedron(Cs,H),
	extendDim(H,N),
	%write('Asserting...'),nl,
	\+ subsumedByExisting(F,N,H),
	getExistingConstraints(F,Cs0,[]),	% assume no bools in recursive approximations
	(Cs0=empty -> H0=empty;
		makePolyhedron(Cs0,H0),
		extendDim(H0,N)),
	convhull(H0,H,H2),
	getConstraint(H2,Cs2),
	assertz(newfact(F,Cs2,[])),
	raise_flag(F),
	(traceTerm(F,_) -> true; assertz(traceTerm(F,T))).
	%write(traceTerm(F,T)),nl).
	
subsumedByExisting(F,N,H) :-
	fact(F,Cs,[]), 
	makePolyhedron(Cs,H1), 
	extendDim(H1,N),
	contains(H1,H).


getExistingConstraints(F,Cs,Bools) :-
	oldfact(F,Cs,Bools),
	!.
getExistingConstraints(_,empty,[]).




fact(X,Y,Bools) :-
	newfact(X,Y,Bools).
fact(X,Y,Bools) :-
	oldfact(X,Y,Bools).
	
newoldfacts :-
	retract(newfact(F,H,Bools)),
	retractall(oldfact(F,_,_)),
	assertz(oldfact(F,H,Bools)),
	fail.
newoldfacts.

%%%%%%%%%%%%%
% Widening
%%%%%%%%%%%%%

widen :-
	prio_widen(PrioWiden),
	possibleWidenPs(PrioWiden,PosPW),
	debug_message(['Possible Wideningpoints ',PosPW]),
	!,
	widenlist(PosPW).

possibleWidenPs([],[]).
possibleWidenPs([(Dg,F,N)|WPs],[Fn|PWPs]) :- 	% Possible WP if there is both old and new fact
	widening_point(F/N,Dg,_Delays),
	functor(Fn,F,N),
	newfact(Fn,_,_),
	oldfact(Fn,_,_),
	!,
	possibleWidenPs(WPs,PWPs).
possibleWidenPs([_|WPs],PWPs) :-
	!,
	possibleWidenPs(WPs,PWPs).

widenlist([]).
widenlist([Wc|Ws]) :-
	functor(Wc,WcF,WcN),
	widening_point(WcF/WcN,P,D), % delay widening
	D > 0,
	!,
	ND is D-1,
	retractall(widening_point(WcF/WcN,P,D)),
	assertz(widening_point(WcF/WcN,P,ND)),
	widenlist(Ws).
widenlist([Wc|Ws]) :-
	functor(Wc,WcF,WcN),
	widening_point(WcF/WcN,_,0),
	retract(newfact(Wc,NewCs,[])),
	retract(oldfact(Wc,OldCs,[])),
	makePolyhedron(NewCs,NewH),
	makePolyhedron(OldCs,OldH),
	%write(NewCs),nl,
	%write(OldCs),nl,
	write(WcF/WcN),nl,
	extendDim(NewH,WcN),
	extendDim(OldH,WcN),
	debug_message(['Widening at ',Wc]),
	wutwiden(Wc,NewH,OldH,H2),
	getConstraint(H2,C2),
	assertz(oldfact(Wc,C2,[])),
	widenlist(Ws).
	
extendDim(H,N) :-
	ppl_Polyhedron_space_dimension(H,M),
	(M<N -> 
		D is N-M, ppl_Polyhedron_add_space_dimensions_and_embed(H,D);
		true).

wutwiden(F,H0,H1,H2) :-
	widenWRToptions(F,H0,H1),
	H2 = H0,
	( equivalent(H1,H2) ->
	    true
	; raise_flag(F)
	).

widenWRToptions(_,H0,H1) :-
	widenf(nowut),
	!,
	widenPolyhedra(H0,H1).
widenWRToptions(F,H0,H1) :-
	widenf(withwut),
	!,
	getThresholds(F,Cns),
	debug_message(['Widen upto constraints: ',Cns]),
	widenUpto(H0,H1,Cns).

widenPolyhedra(H0,H1) :-
	( widenf(bhrz03) -> widenPolyhedraBHRZ03(H0,H1)
	; widenPolyhedraH79(H0,H1)
	).
		
widenUpto(H0,H1,Cs) :-
	( widenf(bhrz03) -> widenUptoBHRZ03(H0,H1,Cs)
	; widenUptoH79(H0,H1,Cs)
	).

getThresholds(F,Cout) :-
	bagof(Cs,invariant(F,Cs),Clist),
	!,
	flattenList(Clist,Cout).
getThresholds(_,[]).

flattenList([],[]).
flattenList([L|Ls],Lout) :-
	flattenList(Ls,Lpre),
	append(L,Lpre,Lout).
	
%%% input threshold constraints %%%%
readWutfacts:-
	threshold('$NOTHRESHOLD'),
	!.
readWutfacts :-
	threshold(TFile),
	open(TFile,read,S),
	read(S,C),
	assertWutFacts(C,S),
	close(S).
	
assertWutFacts(end_of_file,_) :-
	!.
assertWutFacts((H :- C), S) :-
	numbervars((H :- C),0,_),
	assertz(invariant(H,C)),
	read(S,C1),
	assertWutFacts(C1,S).
	
%%% input widening points %%%%
	
load_widenpoints(WPfile) :-
	open(WPfile,read,WP),
	read(WP,W),
	assert_widenpoints(W, WP),
	collect_wps.
	
assert_widenpoints(end_of_file,WP) :-
	!,
	close(WP).
assert_widenpoints(W,WP) :-
	assertWP(W),
	read(WP,W1),
	assert_widenpoints(W1,WP).
	
collect_wps :-
	findall((Dgs,F,N),widening_point(F/N,Dgs,_Delays),Wps),
	reverse(Wps,RWps),
	debug_message(['Ordered by degree ',RWps]),
	assertz(prio_widen(RWps)).
	
assertWP(widening_point(X,Y)) :-
	!,
	delays(D),
	assertz(widening_point(X,Y,D)).
assertWP(widening_point(X)) :-
	!,
	delays(D),
	assertz(widening_point(X,0,D)).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicate dependency graph
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dependency_graph(Es,Vs) :-
	findall(P/N-Q/M, (
			lbe_clause(H,_,Calls,_),
			functor(H,P,N),
			member((_=B),Calls),
			\+ formula(B),
			functor(B,Q,M)
			),
			Es1),
	makeset(Es1,Es),
	findall(A, (
			member(X-Y,Es),
			(A=X; A=Y)
			),
			Vs1),
	findall(P/N, (lbe_clause(H,_,_,_),functor(H,P,N)), Vs2),
	append(Vs1,Vs2,Vs3),
	makeset(Vs3,Vs).		
	

%%%% Getting and setting options

set_options(Options,File,FactFile) :-
	member(programO(File),Options),
	( member(verbose,Options) -> assertz(flag(verbose))
	; retractall(flag(verbose))
	),
	( member(debug_print,Options) -> assertz(flag(debug_print))
	; retractall(flag(debug_print))
	),
	( member(singlepoint,Options) -> assertz(widenAt(singlepoint))
	; assertz(widenAt(allpoints))
	),
	( member(widenO(WOutput),Options) -> true
	; WOutput='widencns'
	),
	( member(widenF(WFunc),Options) -> assertz(widenf(WFunc))
	; assertz(widenf(h79))
	),
	( member(detectwps(M),Options) -> assertz(detectwps(M))
	; assertz(detectwps(feedback))
	),
	( member(thresholdFile(TFile),Options) -> assertz(threshold(TFile))
	; assertz(threshold('$NOTHRESHOLD'))
	),
	( member(withwut,Options) ->
	  assertz(widenf(withwut)),
	  readWutfacts,
	  ( flag(debug_print) ->
	      write('Widening points: '),nl,
	      showallwideningpoints
	  ; true
	  )
	; assertz(widenf(nowut))
	),
	( member(widenP(WPoints),Options) -> true
	; WPoints='widenpoints'
	),
	( member(factFile(FactFile),Options) -> true
	; true
	),
	( member(counterExample(CexFile),Options) -> assertz(cEx(CexFile))
	; assertz(cEx('$NOCEX'))
	),
	assertz(delays(0)),
	detectwps(WPSMethod),
	( member(nowpscalc,Options) -> true
	; verbose_opts(WOpts),
	  wto_file(File,WPSMethod,WPoints,WOpts)
	),
	load_widenpoints(WPoints),
	assertz(outputfile(WOutput)).
	
%%%% clean workspace

initialise :-
	assertz(operatorcount(0)),
	assertz(flag(first)).

cleanWorkspace :-
	retractall(flag(_)),
	retractall(currentflag(_)),
	retractall(nextflag(_)),
	retractall(operatorcount(_)),
	retractall(widening_point(_,_,_)),
	retractall(outputfile(_)),
	retractall(newfact(_,_,_)),
	retractall(oldfact(_,_,_)),
	retractall(prio_widen(_)),
	retractall(widenAt(_)),
	retractall(widenf(_)),
	retractall(detectwps(_)),
	retractall(clauseCount(_)),
	retractall(versionCount(_)),
	retractall(versiontransition(_,_)),
	retractall(version(_,_,_)),
	retractall(pathtransition(_)),
	retractall(atomicproposition(_)),
	retractall(cEx(_)),
	retractall(traceTerm(_,_)).

	
%%%% Output 

showallwideningpoints:-
	widening_point(X,Degree,Delays),
	write('  '),
	write(X),
	write(' Included in '),
	write(Degree),
	write(' program loops'),
	write(' - should be delayed for iterations = '),
	write(Delays),nl,
	fail.
showallwideningpoints.

factFile(user_output):-
	!.

factFile(File) :-
	open(File,write,Sout),
	%(File=user_output -> Sout=user_output; open(File,write,Sout)),
	(oldfact(F,C,_),
	%ppl_Polyhedron_get_minimized_constraints(H,C),
	%numbervars(F,0,_),
	writeq(Sout,F), write(Sout,' :- '), 
	writeq(Sout,C),
	write(Sout,'.'),
	nl(Sout),
	fail;
	close(Sout)).



/*
findCounterexampleTrace(S) :-
	(traceTerm(false,Id); traceTerm(false_ans,Id)),
	!,
	makeTrace(Id,Trace),
	write(Trace),nl,
	write(S,counterexample(Trace)),
	write(S,'.'),
	nl(S).
findCounterexampleTrace(S) :-
	write(S,'safe'),
	write(S,'.'),
	nl(S).	

makeTrace(Id,Trace) :-
	lbe_clause(_,_,B,Id),
	makeTraceList(B,Ids),
	Trace =.. [Id|Ids].
	
makeTraceList([],[]).
makeTraceList([true],[]).
makeTraceList([B|Bs],Ts):-
	constraint(B,_),
	!,
	makeTraceList(Bs,Ts).
makeTraceList([B|Bs],[T|Ts]):-
	functor(B,F,N),
	functor(B1,F,N),
	traceTerm(B1,T),
	makeTraceList(Bs,Ts).
*/
	
linearConstraints([],[],[]).
linearConstraints([C|Cs],[C|LCs],NLCs) :-
	linear_constraint(C),
	!,
	linearConstraints(Cs,LCs,NLCs).
linearConstraints([C|Cs],LCs,[C|NLCs]) :-
	linearConstraints(Cs,LCs,NLCs).
	
formula(B) :-
	cpalbe:isConstraint(B),
	!.
formula((_;_)).
formula([_|_]).
formula([]).
formula(true).

isConstraint(C) :-
	constraint(C,_).
