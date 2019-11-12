:- module(constraintPartition,_).
    
:- use_module(unionfind).
:- use_module(chclibs(setops)).
:- use_module(chclibs(balanced_tree)).

% Given a set of constraints, partition the variables. 
% X and Y are in the same partition iff X is constrained by Y.

constraintPartition(Cs,CP,VP) :-
    variables(Cs,Vs),
    initEqClasses(Vs,root,Es0),
    addConstraints(Cs,Es0,Es1),
    partition(Cs,Es1,Es2),
    traverseVal_tree(Es2,P),
    makePartitions(P,CP,VP).
    
initEqClasses([],Es0,Es1) :-
    make(noVar,Es0,Es1).    % add a partition for constraints with no variables
initEqClasses([X|Xs],Es0,Es2) :-
    make(X,Es0,Es1),
    !,
    initEqClasses(Xs,Es1,Es2).


addConstraints([C|Cs],Es0,Es2) :-
    addConstraint(C,Es0,Es1),
    !,
    addConstraints(Cs,Es1,Es2).
addConstraints([],Es0,Es0).

addConstraint(C,Es0,Es1) :-
    variables(C,Vs),
    mergeVars(Vs,Es0,Es1).
    
mergeVars([],Es0,Es0).
mergeVars([V|Vs],Es0,Es1) :-
    mergeEach(V,Vs,Es0,Es1).

mergeEach(_,[],Es,Es).
mergeEach(V,[W|Vs],Es0,Es2) :-
    merge(V,W,Es0,Es1,_),
    mergeEach(V,Vs,Es1,Es2).
    

partition([C|Cs],Es0,Es2) :-
    variables(C,Vs),
    updatePartition(Vs,C,Es0,Es1),
    partition(Cs,Es1,Es2).
partition([],Es,Es).

updatePartition([V|_],C,Es0,Es1) :-
    findSimple(_,V,Es0,data(Z,P)),
    updateData(P,C,P1),
    search_replace_tree(Es0,Z,data(Z,P),Es1,data(Z,P1)).
    
updateData([X|Xs],C,partition([X|Xs],[C])) :-   % first constraint added to this set
    !.
updateData(partition(Xs,Cs),C,partition(Xs,[C|Cs])).
    

makePartitions([data(_,partition(Xs,Cs))|Ps],[Cs|CP],[Xs|VP]) :-
    !,
    makePartitions(Ps,CP,VP).
makePartitions([data(_,_)|Ps],CP,VP) :-
    makePartitions(Ps,CP,VP).
makePartitions([],[],[]).
    
variables('$VAR'(N),['$VAR'(N)]) :-
    !.
variables(C,Vs) :-
    C =.. [_|Xs],
    variablesList(Xs,Vs).

    
variablesList([],[]).
variablesList([X|Xs],Vs) :-     
    variables(X,Vs1),
    variablesList(Xs,Vs2),
    setunion(Vs1,Vs2,Vs).

    
test :-
    numbervars((A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S),0,_),
    Cs = [-1*A+ -1*B+7*D+ -1*E+ -1*G+ -1*H>= -5,-2*A+ -1*C+2*D+ -3*G>= -5,-2*A+ -1*C+2*D+ -3*E>= -5,-1*A+ -2*C+ -2*D>= -7,-1*A+ -1*B+7*D+ -1*E+ -1*F+ -1*H>= -5,-2*A+ -1*C+2*D+ -3*F>= -5,-3*C+1*H>= -6,-1*C+ -2*D>= -4,-1*B+ -5*C>= -16,-5*A+ -3*B+ -4*C+11*D>= -20,-2*A+ -1*C+ -1*D>= -5,-1*D>= -1,-1*B+2*D>= -4,-2*A+2*D+ -2*G+ -1*H>= -5,-1*A+ -1*G>= -2,1*H>=0,-2*A+4*D+ -2*E+ -2*F+ -1*H>= -5,-1*C+1*D+1*E+1*F+1*H>= -1,-1*A+ -1*B+4*D+ -1*G>= -4,-2*C+1*D+1*E+1*F+1*H>= -3,-1*A+ -1*B+7*D+ -1*F+ -1*G+ -1*H>= -5,-2*A+ -1*B+4*D+ -2*F>= -6,-1*F>= -1,-1*B+5*D+ -1*H>= -4,-1*B+2*C+8*D+ -2*G+ -2*H>= -6,1*A+ -1*B+1*C+9*D+ -1*E+ -1*F+ -1*G+ -1*H>= -3,-1*A+1*B+2*C+1*D+ -2*E+ -2*F+ -2*G+ -2*H>= -6,-1*A+1*C+3*D+ -1*F+ -1*G+ -1*H>= -3,1*A>=0,-1*A+1*C+3*D+ -1*E+ -1*G+ -1*H>= -3,-1*B+1*C+3*D>= -3,-1*B+2*C+10*D+ -2*E+ -2*G+ -2*H>= -6,-1*A+1*C+2*D+ -1*E+ -1*H>= -3,-1*H>= -3,1*B+1*C+ -1*D+ -1*H>= -3,-1*B+2*C+10*D+ -2*E+ -2*F+ -2*H>= -6,-1*B+2*C+8*D+ -2*F+ -2*H>= -6,-2*B+2*C+14*D+ -2*G+ -3*H>= -9,-5*A+2*B+4*C+5*D+ -4*E+ -4*F+ -4*G+ -4*H>= -12,-1*A+1*D+ -1*E+1*H>= -1,-1*A+1*C+2*D+ -1*G+ -1*H>= -3,-5*C+ -2*D+ -2*E+ -2*G>= -16,-1*A+ -2*B+ -1*C+7*D+1*E+1*F+ -2*G+1*H>= -9,-1*C+2*D+ -2*E+ -2*G>= -4,-1*A+ -4*C+ -2*D+ -2*G>= -13,1*C+2*D+ -1*F+ -1*G+ -1*H>= -3,-1*A+ -1*C+1*D+ -2*G>= -4,-2*A+2*D+ -2*F+ -1*H>= -5,-5*A+ -4*B+ -2*C+17*D+2*E+2*F+ -4*G+2*H>= -18,1*D+ -1*E+ -1*G>= -1,-3*C+ -2*D+ -2*E>= -10,-1*A+ -4*C+ -2*D+ -2*E>= -13,-1*B+ -2*C+3*D+1*E+1*F>= -7,1*C+1*D+ -1*F+ -1*H>= -3,-2*B+2*C+14*D+ -2*E+ -3*H>= -9,-1*B+1*C+4*D+ -1*F>= -3,1*A+ -1*B+1*C+8*D+ -1*E+ -1*F+ -1*H>= -3,-2*B+1*C+12*D+ -1*F+ -2*H>= -7,-1*A+1*D+ -1*G+1*H>= -1,-4*A+ -2*B+ -4*C+13*D+4*E+4*F+ -2*G+4*H>= -12,2*A+1*B+ -4*C+4*D+4*E+4*F+1*G+4*H>=0,-2*A+ -1*H>= -5,1*B>=0,-1*A+1*B+ -4*C+4*D+4*E+4*F+1*G+7*H>=0,1*C+1*D+ -1*E+ -1*H>= -3,-2*B+1*C+13*D+ -1*E+ -1*G+ -2*H>= -7,-1*A+ -1*C+1*D+ -2*E>= -4,-2*B+1*C+12*D+ -1*E+ -2*H>= -7,-2*A+3*B+1*C+ -1*D+ -1*H>= -3,-2*A+1*C+4*D+ -1*E+ -1*F+ -2*H>= -6,-2*B+1*C+11*D+ -1*E+ -2*G+ -1*H>= -7,1*C+1*D+ -1*G+ -1*H>= -3,-1*C+2*D+ -2*E+ -2*F>= -4,-1*A+1*D+ -1*E+ -1*F>= -2,-5*C+ -2*D+ -2*E+ -2*F>= -16,1*C+2*D+ -1*E+ -1*F+ -1*H>= -3,1*C+2*D+ -1*E+ -1*G+ -1*H>= -3,-2*B+1*C+12*D+ -1*G+ -2*H>= -7,-2*B+1*C+13*D+ -1*E+ -1*F+ -2*H>= -7,-1*A+1*C+4*D+ -1*E+ -1*F+ -1*G+ -1*H>= -3,-1*A+ -1*C+1*D+ -2*F>= -4,-1*E>= -1,-2*B+1*C+12*D+ -1*E+ -1*F+ -2*G+ -1*H>= -7,-2*B+2*C+18*D+ -2*E+ -2*F+ -2*G+ -3*H>= -9,-2*B+1*C+14*D+ -1*E+ -1*F+ -1*G+ -2*H>= -7,-1*B+2*C+12*D+ -2*E+ -2*F+ -2*G+ -2*H>= -6,1*A+ -1*B+1*C+8*D+ -1*F+ -1*G+ -1*H>= -3,-2*B+ -3*C+7*D+3*E+3*F+1*G>= -11,-1*A+ -4*C+ -2*D+ -2*F>= -13,-1*B+ -1*C+3*D+1*E+1*F>= -5,-1*B+1*C+5*D+ -1*E+ -1*G>= -3,-1*C+ -2*G>= -4,-1*B+1*C+4*D+ -1*E>= -3,2*D+ -1*E+ -1*F+ -1*G>= -1,1*D+ -1*F+ -1*G>= -1,-1*A+ -1*B+6*D+ -1*F+ -1*H>= -5,1*D+ -1*E+ -1*F>= -1,-1*B+3*D+ -1*G>= -4,-2*A+ -1*B+4*D+ -2*E>= -6,-1*B+ -3*C+5*D+3*E+3*F+1*G+1*H>= -7,-2*A+2*B+1*C+ -1*H>= -3,-1*C+ -2*F>= -4,1*C+3*D+ -1*E+ -1*F+ -1*G+ -1*H>= -3,-1*B+2*C+8*D+ -2*E+ -2*H>= -6,1*A+ -1*B+1*C+8*D+ -1*E+ -1*G+ -1*H>= -3,1*A+ -1*B+1*C+7*D+ -1*G+ -1*H>= -3,-3*C+ -2*D+ -2*F>= -10,-2*B+1*C+11*D+ -1*F+ -2*G+ -1*H>= -7,-1*B+1*C+6*D+ -1*E+ -1*F+ -1*G>= -3,-1*B+1*C+5*D+ -1*E+ -1*F>= -3,-1*A+ -1*F>= -2,-2*B+1*C+10*D+ -2*G+ -1*H>= -7,-1*A+ -1*B+3*D>= -4,-1*B+1*C+5*D+ -1*F+ -1*G>= -3,-1*A+ -1*E>= -2,-1*A+1*B+ -1*D>= -1,-2*A+4*D+ -2*F+ -2*G+ -1*H>= -5,-2*B+2*C+16*D+ -2*E+ -2*F+ -3*H>= -9,-1*C+ -2*E>= -4,-2*A+4*D+ -2*E+ -2*G+ -1*H>= -5,-1*A+1*D+2*H>=0,-2*A+1*C+2*D+ -2*H>= -6,-8*A+2*B+4*C+8*D+ -4*E+ -4*F+ -4*G+ -7*H>= -21,1*A+ -1*B+1*C+7*D+ -1*E+ -1*H>= -3,-1*A+ -2*B+ -5*C+7*D+ -2*G>= -18,1*A+ -1*B+1*C+7*D+ -1*F+ -1*H>= -3,-2*B+2*C+16*D+ -2*F+ -2*G+ -3*H>= -9,-3*C+ -2*D+ -2*G>= -10,-1*A+ -1*B+6*D+ -1*E+ -1*H>= -5,-1*B+2*C+10*D+ -2*F+ -2*G+ -2*H>= -6,-2*B+1*C+13*D+ -1*F+ -1*G+ -2*H>= -7,-2*B+2*C+14*D+ -2*F+ -3*H>= -9,-4*A+4*B+2*C+1*D+ -2*E+ -2*F+ -2*G+ -2*H>= -6,-5*C+ -2*D+ -2*F+ -2*G>= -16,1*A+ -3*C+3*D+3*E+3*F+1*G+2*H>= -3,-2*B+2*C+16*D+ -2*E+ -2*G+ -3*H>= -9,-1*C+2*D+ -2*F+ -2*G>= -4,-4*A+7*B+2*C+ -2*D+ -2*E+ -2*F+ -2*G+ -2*H>= -6,-2*A+1*C+3*D+ -1*F+ -2*H>= -6,-2*B+ -5*C+6*D+ -2*G>= -18,-1*A+1*C+2*D+ -1*F+ -1*H>= -3,-2*A+1*C+3*D+ -1*E+ -2*H>= -6,-1*A+4*B+2*C+ -2*D+ -2*E+ -2*F+ -2*G+ -2*H>= -6,-2*A+1*C+3*D+ -1*G+ -2*H>= -6,-2*A+1*C+4*D+ -1*F+ -1*G+ -2*H>= -6,-2*A+1*C+4*D+ -1*E+ -1*G+ -2*H>= -6,-1*A+ -1*C+2*D+1*E+1*F+2*H>= -1,-1*A+1*D+ -1*E+ -1*G>= -2,-3*A+ -5*B+26*D+ -1*G+ -4*H>= -20,-3*A+ -5*B+25*D+ -4*H>= -20,-2*A+ -2*C+1*D+1*H>= -5,-1*G>= -1,-1*A+1*C+3*D+ -1*E+ -1*F+ -1*H>= -3,-1*A+ -1*B+6*D+ -1*G+ -1*H>= -5,-5*A+ -3*B+ -4*C+14*D+ -3*G>= -20,-1*A+ -1*D>= -2,-1*A+ -2*B+2*C+10*D+ -2*E+ -2*F+ -2*G+1*H>= -6,-1*A+1*D+ -1*F+1*H>= -1,-1*B+1*C+4*D+ -1*G>= -3,-1*A+ -1*C+1*D+1*H>= -2,-2*A+ -1*B+6*D+ -2*E+ -2*F>= -6,-3*A+ -1*B+ -3*C+5*D+1*H>= -10,-2*A+ -1*B+6*D+ -2*F+ -2*G>= -6,-1*A+ -2*C+1*D+1*H>= -4,-4*A+1*B+ -4*C+7*D+4*E+4*F+1*G+10*H>=0,-1*A+1*D+ -1*F+ -1*G>= -2,-2*A+ -1*B+6*D+ -2*E+ -2*G>= -6,-1*A+1*B+ -1*C+ -2*D+ -2*E+ -2*F+ -2*G+1*H>=0,-1*B+ -3*C+2*D>= -10,-1*A+ -1*B+ -1*C+4*D+1*E+1*F>= -5,-2*A+2*D+ -2*E+ -1*H>= -5,-2*A+ -1*B+1*C+4*D+ -1*F>= -5,-2*A+ -2*B+1*C+7*D>= -7,-2*A+ -3*B+3*C+13*D+ -1*F+ -1*G>= -9,-2*A+ -1*B+1*C+4*D+ -1*E>= -5,-2*A+ -1*B+1*C+5*D+2*H>= -3,-2*A+ -1*B+1*C+5*D+ -1*E+ -1*G>= -5,-2*A+ -3*B+3*C+13*D+ -1*E+ -1*F>= -9,-2*A+ -3*B+3*C+12*D+ -1*E>= -9,-2*A+ -3*B+3*C+13*D+ -1*E+ -1*G>= -9,-2*A+ -1*B+1*C+3*D>= -5,-4*A+ -5*B+5*C+22*D+ -2*E+ -2*F+ -2*G+1*H>= -15,-2*A+ -3*B+3*C+12*D+ -1*G>= -9,-2*A+ -1*B+1*C+5*D+ -1*F+ -1*G>= -5,-4*A+ -2*B+2*C+10*D+ -2*E+ -2*F+ -2*G+1*H>= -9,-2*A+ -1*B+1*C+4*D+ -1*G>= -5,-2*A+ -2*B+1*C+8*D+ -1*G>= -7,-2*A+ -1*B+1*C+5*D+ -1*E+ -1*F>= -5,-2*A+ -3*B+3*C+12*D+ -1*F>= -9,-2*A+ -3*B+3*C+11*D>= -9,-2*A+ -2*B+1*C+8*D+ -1*F>= -7,-2*A+ -4*B+1*C+24*D+ -1*E+ -4*H>= -15,-1*B+1*C+6*D+ -1*H>= -3,-2*A+ -1*B+1*C+6*D+ -1*E+2*H>= -3,1*E>=0,-4*A+ -2*B+2*C+18*D+ -2*F+ -5*H>= -15,-4*A+ -2*B+2*C+18*D+ -2*G+ -5*H>= -15,-2*A+ -2*B+1*C+8*D+ -1*E>= -7,-4*A+ -2*B+2*C+18*D+ -2*E+ -5*H>= -15,-2*A+ -4*B+1*C+24*D+ -1*F+ -4*H>= -15,-4*A+ -2*B+2*C+20*D+ -2*E+ -2*F+ -5*H>= -15,-4*A+ -2*B+2*C+13*D+ -2*E+ -2*F+ -2*G+4*H>= -6,-2*A+ -4*B+1*C+23*D+ -4*H>= -15,-4*A+ -2*B+2*C+20*D+ -2*E+ -2*G+ -5*H>= -15,-2*A+ -2*B+1*C+9*D+ -1*F+ -1*G>= -7,-2*A+ -2*B+1*C+9*D+ -1*E+ -1*F>= -7,-8*A+ -7*B+4*C+32*D+ -4*E+ -4*F+ -4*G+2*H>= -24,-2*A+ -2*B+1*C+9*D+ -1*E+ -1*G>= -7,1*C>=0,-4*A+ -2*B+2*C+20*D+ -2*F+ -2*G+ -5*H>= -15,-4*A+ -2*B+2*C+22*D+ -2*E+ -2*F+ -2*G+ -5*H>= -15,-2*A+ -4*B+1*C+25*D+ -1*E+ -1*F+ -4*H>= -15,-2*A+ -1*B+1*C+6*D+ -1*F+2*H>= -3,-2*A+ -4*B+1*C+25*D+ -1*E+ -1*G+ -4*H>= -15,1*D>=0,-2*A+ -4*B+1*C+25*D+ -1*F+ -1*G+ -4*H>= -15,-2*A+ -4*B+1*C+26*D+ -1*E+ -1*F+ -1*G+ -4*H>= -15,-2*A+ -4*B+1*C+24*D+ -1*G+ -4*H>= -15,-4*A+ -2*B+2*C+16*D+ -5*H>= -15,-2*A+ -1*B+1*C+6*D+ -1*G+2*H>= -3,1*F>=0,1*G>=0,A=A,B=B,C=C,D=D,E=E,F=F,G=G,H=H,I=I,J=J,K=K,L=L,M=M,N=N,O=O,P=P,Q=Q,R=R,S=S,A=A,B=B,C=C,D=D,E=E,F=F,G=G,H=H,I=I,J=J,K=K,L=L,M=M,N=N,O=O,P=P,Q=Q,R=R,S=S],
    constraintPartition(Cs,CP,VP),
    write(VP),
    nl,
    write(CP),
    nl.
