:- module(chcNorm,_).

:- use_module(library(lists)).
:- use_module(library(terms_vars)).
%the use of transf may not be appropriate for real division (eg. 1.8/10)
:- use_module(chclibs(lcm), [transf/2]).
:- use_module(chclibs(common), _).




:- dynamic(intDomain/0).

main([FIn,FOut,'-int']) :-
    cleanup,
    assert(intDomain),
    open(FIn,read,S1),
    open(FOut,write,S2),
    read(S1,C),
    normaliseClauses(C,S1,S2,Ds,[],0,_),
    normaliseRationalClauses(Ds,Ds1),
    (intDomain -> integerTransCls(Ds1,Ds2); Ds1=Ds2),
    addBoolClauses(Ds2,S2),
    addNeqClauses(S2),
    close(S1),
    close(S2).
    
main([FIn,FOut]) :-
    cleanup,
    open(FIn,read,S1),
    open(FOut,write,S2),
    read(S1,C),
    normaliseClauses(C,S1,S2,Ds,[],0,_),
    normaliseRationalClauses(Ds,Ds1),
    addBoolClauses(Ds1,S2),
    addNeqClauses(S2),
    close(S1),
    close(S2).
    
cleanup :-
    retractall(intDomain).
    
normaliseClauses(end_of_file,_,_,Ds,Ds,K,K) :-
    !.
normaliseClauses(C,S1,S2,Ds0,Ds2,K0,K2) :-
    normaliseClause(C,C1,Ds0,Ds1,K0,K1),
    numbervars(C1,0,_),
    normaliseRationals(C1,C3),
    writeClause(C3,S2),
    read(S1,C2),
    normaliseClauses(C2,S1,S2,Ds1,Ds2,K1,K2).
    
%  assume H is already normalised, i.e. p(X1,...,Xn), n >= 0, X1,...,Xn distinct variables

normaliseClause((H :- B), (H1 :- B5), Ds0,Ds1,K0,K1) :-
    !,
    H =.. [_|Xs],
    userPredArgs(B,Xs,Ys),
    removeBooleanVars(B,B1,Ys),
    peBoolExpr(B1,B2,Ds0,Ds1,Cs0,[],K0,K1),
    list2Conj(Cs0,Cs1),
    conjunct(Cs1,B2,B3),
    trueFalseSubst(B3,B4),
    trueFalseSubst(H,H1),
    (intDomain -> integerTrans(B4,B5); B4=B5).
normaliseClause(H, (H :- true),Ds,Ds,K,K).

normaliseRationals((H :- B), (H :- B1)) :-
    !,
    rationalTransform(B, B1).
normaliseRationals(H, (H :- true)).

normaliseRationalClauses([],[]).
normaliseRationalClauses([C|Cs],[C1|Cs1]) :-
    normaliseRationals(C,C1),
    normaliseRationalClauses(Cs,Cs1).
    
userPredArgs(B,Xs,Xs) :-
    var(B),
    !.
userPredArgs((B,Bs),Xs0,Xs2) :-
    !,
    userPredArgs(B,Xs0,Xs1),
    userPredArgs(Bs,Xs1,Xs2).
userPredArgs(B,Xs,Xs) :-
    isConstraint(B),
    !.
userPredArgs(B,Xs0,Xs1) :-
    B =.. [_|Ys],
    append(Ys,Xs0,Xs1).
    
isConstraint(B) :-
    functor(B,F,_),
    member(F,['=','>','<','>=','=<', or, and, if, iff, true, false, '=>']).


    

removeBooleanVars(B,B,_) :-
    var(B),
    !.
removeBooleanVars((B,Bs),Bs3,Xs) :-
    !,
    simplifyIff(B,B1,Xs),
    removeBooleanVars(Bs,Bs2,Xs),
    conjunct(B1,Bs2,Bs3).
removeBooleanVars(B,B,_).
    
simplifyIff(B,true,Xs) :-
    nonvar(B),
    B = iff(X,Y),
    var(X),
    \+ vmemb(X,Xs),
    !,
    X=Y.
simplifyIff(B,B,_).

trueFalseSubst(X,X) :-
    var(X),
    !.
trueFalseSubst((B,Bs),(B1,Bs1)) :-
    !,
    trueFalseSubst(B,B1),
    trueFalseSubst(Bs,Bs1).
trueFalseSubst(B,B1) :-
    B =.. [P|Xs],
    substTrueFalseList(Xs,Ys),
    B1 =.. [P|Ys].
    
substTrueFalse(X,X) :-
    var(X),
    !.
substTrueFalse(true,1) :-
    !.
substTrueFalse(false,0) :-
    !.
substTrueFalse(T1,T2) :-
    T1 =.. [P|Xs],
    substTrueFalseList(Xs,Ys),
    T2 =.. [P|Ys].
    
substTrueFalseList([],[]).
substTrueFalseList([X|Xs],[Y|Ys]) :-
    substTrueFalse(X,Y),
    substTrueFalseList(Xs,Ys).


peBoolExpr(B,B,Ds,Ds,Cs,Cs,K,K) :-
    var(B),
    !.
peBoolExpr((B,Bs),Bs3,Ds0,Ds2,Cs0,Cs2,K0,K2) :-
    !,
    peBoolExpr(B,B1,Ds0,Ds1,Cs0,Cs1,K0,K1),
    peBoolExpr(Bs,Bs2,Ds1,Ds2,Cs1,Cs2,K1,K2),
    conjunct(B1,Bs2,Bs3).
peBoolExpr(Or,B1,Ds0,Ds2,Cs0,Cs1,K0,K2) :-
    Or =.. [or|Ts],
    !,
    peBoolExprList(Ts,Ts1,Ds0,Ds1,Cs0,Cs1,K0,K1),
    varset(Ts,Xs),
    newPred(or,OrK,K1,K2),
    B1 =.. [OrK|Xs],
    makeOrClauses(B1,Ts1,Ds1,Ds2).
peBoolExpr(And,B1,Ds0,Ds2,Cs0,Cs1,K0,K2) :-
    And =.. [and|Ts],
    !,
    peBoolExprList(Ts,Ts1,Ds0,Ds1,Cs0,Cs1,K0,K1),
    varset(Ts,Xs),
    newPred(and,AndK,K1,K2),
    B1 =.. [AndK|Xs],
    makeAndClauses(B1,Ts1,Ds1,Ds2).
peBoolExpr(if(B,Then,Else),BIf,Ds0,Ds2,Cs0,Cs1,K0,K2) :-
    !,
    peBoolExprList([B,not(B),Then,Else],[B1,NotB1,Then1,Else1],Ds0,Ds1,Cs0,Cs1,K0,K1),
    varset(if(B1,Then1,Else1),Xs),
    newPred(if,IfK,K1,K2),
    BIf =.. [IfK|Xs],
    makeIfClauses(BIf,B1,NotB1,Then1,Else1,Ds1,Ds2).
peBoolExpr(not(B),B1,Ds0,Ds1,Cs0,Cs1,K0,K1) :-
    !,
    nnf(B,NotB),
    peBoolExpr(NotB,B1,Ds0,Ds1,Cs0,Cs1,K0,K1).
peBoolExpr('=>'(F1,F2),BImplies,Ds0,Ds2,Cs0,Cs1,K0,K2) :-
    !,
    peBoolExprList([not(F1),F2],[NotF1,F3],Ds0,Ds1,Cs0,Cs1,K0,K1),
    varset('=>'(F1,F2),Xs),
    newPred(implies,BImplies,K1,K2),
    BImplies =.. [BImplies|Xs],
    makeImpliesClauses(BImplies,NotF1,F3,Ds1,Ds2).
peBoolExpr(iff(B1,B2),BIff,Ds0,Ds2,Cs0,Cs1,K0,K2) :-
    !,
    peBoolExprList([B1,B2,not(B1),not(B2)],[B3,B4,B5,B6],Ds0,Ds1,Cs0,Cs1,K0,K1),
    (iffUnify(B3,B4) -> BIff=(B3=B4), Ds1=Ds2, K1=K2; 
            varset(iff(B3,B4),Xs),
            newPred(iff,IffK,K1,K2),
            BIff =.. [IffK|Xs],
            makeIffClauses(BIff,B3,B4,B5,B6,Ds1,Ds2)).
peBoolExpr(B,B1,Ds0,Ds1,Cs0,Cs1,K0,K1) :-
    B =.. [RelOp|Xs],
    member(RelOp,['=','>','<','>=','=<',neq]),
    !,
    peArithExprList(Xs,Ys,Ds0,Ds1,Cs0,Cs1,K0,K1),
    B1 =.. [RelOp|Ys].
peBoolExpr(B,B,Ds,Ds,Cs,Cs,K,K). % should be only user predicates that reach this clause

iffUnify(X,Y) :-
    (var(X); atomic(X)),
    (var(Y); atomic(Y)),
    !.
    

peArithExpr(B,B,Ds,Ds,Cs,Cs,K,K) :-
    var(B),
    !.
peArithExpr(if(B,Then,Else),R,Ds0,Ds3,[BIf|Cs0],Cs2,K0,K3) :-
    !,
    peBoolExprList([B,not(B)],[B1,NotB1],Ds0,Ds1,Cs0,Cs1,K0,K1),
    peArithExprList([Then,Else],[Then1,Else1],Ds1,Ds2,Cs1,Cs2,K1,K2),
    varset(if(B1,Then1,Else1),Xs),
    newPred(if,IfK,K2,K3),
    BIf =.. [IfK,R|Xs],
    makeArithIfClauses(BIf,R,B1,NotB1,Then1,Else1,Ds2,Ds3).
peArithExpr((A mod B), R, Ds0,Ds1, [R>=0, R=<D-1, C=_K*D+R|Cs0],Cs1,K0,K1) :-
    !,
    peArithExprList([A,B],[C,D],Ds0,Ds1,Cs0,Cs1,K0,K1).
peArithExpr(div(A,B), K, Ds0,Ds1, [R>=0, R=<D-1, C=K*D+R|Cs0],Cs1,K0,K1) :-
    !,
    peArithExprList([A,B],[C,D],Ds0,Ds1,Cs0,Cs1,K0,K1).
peArithExpr(E,E1, Ds0,Ds1, Cs0,Cs1,K0,K1) :-
    E =.. [Op|Xs],
    member(Op,['+','-','/','*']),
    !,
    peArithExprList(Xs,Ys,Ds0,Ds1,Cs0,Cs1,K0,K1),
    E1 =.. [Op|Ys].
peArithExpr(E,E,Ds,Ds,Cs,Cs,K,K).       % catch-all but should not be needed

peBoolExprList([],[],Ds,Ds,Cs,Cs,K,K).
peBoolExprList([B|Bs],[B1|Bs1],Ds0,Ds2,Cs0,Cs2,K0,K2) :-
    peBoolExpr(B,B1,Ds0,Ds1,Cs0,Cs1,K0,K1),
    peBoolExprList(Bs,Bs1,Ds1,Ds2,Cs1,Cs2,K1,K2).
    
peArithExprList([],[],Ds,Ds,Cs,Cs,K,K).
peArithExprList([B|Bs],[B1|Bs1],Ds0,Ds2,Cs0,Cs2,K0,K2) :-
    peArithExpr(B,B1,Ds0,Ds1,Cs0,Cs1,K0,K1),
    peArithExprList(Bs,Bs1,Ds1,Ds2,Cs1,Cs2,K1,K2).
    
nnf(X,X=0) :-
    var(X),
    !.
nnf(true,false) :-
    !.
nnf(false,true) :-
    !.
nnf(not(X),X) :-
    !.
nnf(And,Or) :-
    And =.. [and|Xs],
    !,
    nnfList(Xs,Ys),
    Or =.. [or|Ys].
nnf(Or,And) :-
    Or =.. [or|Xs],
    !,
    nnfList(Xs,Ys),
    And =.. [and|Ys].
nnf('=>'(F1,F2),F) :-
    !,
    nnf(F2,NotF2),
    F =.. [and,F1,NotF2].
nnf(If,If1) :-
    If =.. [if,B,Then,Else],
    !,
    nnfList([Then,Else],[NotThen,NotElse]),
    If1 =.. [if,B,NotThen,NotElse].
nnf(iff(B1,B2),Iff1) :-
    !,
    nnf(or(and(B1,B2),and(not(B1),not(B2))),Iff1).
nnf(X >= Y, X < Y) :-
    !.
nnf(X =< Y, X > Y) :-
    !.
nnf(X > Y, X =< Y) :-
    !.
nnf(X < Y, X >= Y) :-
    !.
nnf(X = Y, neq(X,Y)) :-
    !.
nnf(neq(X,Y), X = Y) :-
    !.

nnfList([],[]).
nnfList([X|Xs],[Y|Ys]) :-
    nnf(X,Y),
    nnfList(Xs,Ys).
    
makeOrClauses(H,[T|Ts],[(H :- T1)|Ds0],Ds1) :-
    makeArg(T,T1),
    makeOrClauses(H,Ts,Ds0,Ds1).
makeOrClauses(_,[],Ds,Ds). 

makeAndClauses(H,Ts,[(H :- Body)|Ds0],Ds0) :-
    makeArgList(Ts,Ts1),
    list2Conj(Ts1,Body).
makeAndClauses(_,[],Ds,Ds).

makeArg(X,X=1) :-
    var(X),
    !.
makeArg(not(X),X=0) :-
    var(X),
    !.
makeArg(true, 1=1) :-
    !.
makeArg(false, 0=1) :-
    !.
makeArg(iff(X,Y),X=Y) :-
    !.
makeArg(X,X).

makeArgList([],[]).
makeArgList([X|Xs],[Y|Ys]) :-
    makeArg(X,Y),
    makeArgList(Xs,Ys).



makeIfClauses(H,B,NotB,Then,Else,[(H :- (B1,Then1)),(H :- (NotB1,Else1))|Ds0],Ds0) :-
    makeArgList([B,Then,NotB,Else],[B1,Then1,NotB1,Else1]).
    
makeArithIfClauses(H,R,B,NotB,Then,Else,[(H :- (B1,Then1)),(H :- (NotB1,Else1))|Ds0],Ds0) :-
    makeArgList([B,R=Then,NotB,R=Else],[B1,Then1,NotB1,Else1]).

makeIffClauses(H,B1,B2,B3,B4,[(H :- A1,A2),(H :- A3,A4)|Ds0],Ds0) :-
    makeArgList([B1,B2,B3,B4],[A1,A2,A3,A4]).
    
makeImpliesClauses(H,NotF1,F3,[(H :- A1),(H :- A2)|Ds0],Ds0) :-
    makeArgList([NotF1,F3],[A1,A2]).
    

    
integerTrans(X,Y) :-
    integerTransform(X,Y1,Bs,[]),
    list2Conj(Bs,Bs1),
    conjunct(Y1,Bs1,Y).

integerTransform(X,X,Bs,Bs) :-
    var(X),
    !.
integerTransform(X<Y,X+1=<Y,Bs,Bs) :-
    !.
integerTransform(X>Y,X>=Y+1,Bs,Bs) :-
    !.
integerTransform(T,T1,Ds0,Ds1) :-
    T =.. [P|Xs],
    integerTransformList(Xs,Ys,Ds0,Ds1),
    T1 =.. [P|Ys].
    
integerTransformList([],[],Ds,Ds).
integerTransformList([X|Xs],[Y|Ys],Ds0,Ds2) :-
    integerTransform(X,Y,Ds0,Ds1),
    integerTransformList(Xs,Ys,Ds1,Ds2).

integerTransCls([],[]).
integerTransCls([(H:-B)|Cs],[(H1:-B2)|Cs1]) :-
    melt((H:-B),(H1:-B1)),
    integerTrans(B1,B2),
    numbervars((H1:-B2),0,_),
    integerTransCls(Cs,Cs1).





% transforms (1/2)* D = (2/3)*Y into 3*D = 4*Y, needed for PPL

rationalTransform(X,X) :-
    var(X),
    !.
rationalTransform((X,Y), (X1, Y1)) :-
    !,
    rationalTransform(X, X1),
    rationalTransform(Y, Y1).
rationalTransform(true,true) :-
    !.
rationalTransform(X,Y) :-
    constraint(X, _),
    !,
    transf(X,Y).
rationalTransform(X,X).


%--------------

conjunct(true,Bs,Bs) :-
    !.
conjunct(Bs,true,Bs) :-
    !.
conjunct((E,Es),Bs,(E,Bs1)) :-
    !,
    conjunct(Es,Bs,Bs1).
conjunct(B,Bs,(B,Bs)).
    
vmemb(X,[Y|_]) :-
    X == Y,
    !.
vmemb(X,[_|Xs]) :-
    vmemb(X,Xs).
    
writeClause((H :- B), S) :-
    writeq(S,H),
    write(S,' :-'),
    nl(S),
    writeBody(B,S),
    write(S,'.'),
    nl(S).
    
writeBody((B,Bs),S) :-
    !,
    write(S,'    '),
    writeq(S,B),
    write(S,','),
    nl(S),
    writeBody(Bs,S).
writeBody(B,S) :-
    write(S,'    '),
    writeq(S,B).
    
addBoolClauses(Ds,S) :-
    writeClauses(Ds,S).
    
writeClauses([C|Cs],S) :-
    writeClause(C,S),
    writeClauses(Cs,S).
writeClauses([],_).

newPred(P,PK,K0,K1) :-
    name(P,PN),
    name(K0,NK0),
    append(PN,NK0,PKN),
    name(PK,PKN),
    K1 is K0+1.
    
%list2Conj([A], (A)):- !.
%list2Conj([A|R], (A,R1)):- !,
%       list2Conj(R, R1).
%list2Conj([], (true)). % meaning true


addNeqClauses(S) :-
    numbervars((X,Y),0,_),
    Cls = [
                    (neq(X, Y) :- X < Y),  (neq(X, Y) :- X > Y)
                    ],
    (intDomain -> integerTransCls(Cls,Cls1); Cls1=Cls),
    writeClauses(Cls1,S).

%! melt(+X,-Y): Obtain the free variable term representation `Y` from
%    ground representation `X`. E.g.,
%
%        ?- melt(a('$VAR'(1),'$VAR'(2),'$VAR'(1)),X).
%       
%        X = a(_A,_,_A) ? 
melt(X,Y) :-
    melt1(X,Y,_Assoclist),
    !.

melt1(X,Y,S) :-
    variable(X),
    !,
    assoc(X,Y,S).
melt1(X,X,_) :-
    atomic(X),
    !.
melt1(X,Y,S) :-
    functor(X,F,N),
    functor(Y,F,N),
    meltargs(1,N,X,Y,S).

meltargs(I,N,_,_,_) :-
    I > N,
    !.
meltargs(I,N,X,Y,S) :-
    arg(I,X,Xi),
    melt1(Xi,Yi,S),
    arg(I,Y,Yi),
    I1 is I+1,
    meltargs(I1,N,X,Y,S).


assoc(X,Y,[assoc(X,Y)|_]) :-
    !.
assoc(X,Y,[_|S]) :-
    assoc(X,Y,S).

%! variable(+X): `X` is a variable in ground representation
variable('$VAR'(_)).    

