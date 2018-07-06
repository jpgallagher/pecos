% union-find operations
:- module(unionfind,[
	find/5, 
	findSimple/4,
	make/3,
	merge/5,
	link/4]).
	
:- use_module(chclibs(balanced_tree)).

find(_N,T,Es0,Es2,R) :-
	search_replace_tree(Es0,T,PT,Es1,R1),
	%N1 is N+1,
	checkRoot(_N1,PT,T,R,R1,Es1,Es2).

findSimple(_N,T,Es0,R) :-
	search_tree(Es0,T,PT),
	%N1 is N+1,
	checkRootSimple(_N1,PT,T,R,Es0).
	
checkRoot(_N1,data(T,Fs),T,data(T,Fs),data(T,Fs),Es,Es) :-
	%write(N1), write('steps for find '), nl,
	!.
checkRoot(_N,data(PT,_),_,data(R,Fs),data(R,[]),Es0,Es1) :-
	% N1 is N+1,
	find(_N1,PT,Es0,Es1,data(R,Fs)).
	
checkRootSimple(_N1,data(T,Fs),T,data(T,Fs),_) :-
	%write(N1), write('steps for simple find '), nl,
	!.
checkRootSimple(_N,data(PT,_),_,R,Es0) :-
	% N1 is N+1,
	findSimple(_N1,PT,Es0,R).
	
make(X,Es0,Es1) :-
	insert_tree(Es0,X,data(X,[]),Es1).
	
merge(X,Y,Es0,Es4,data(RX,Ts)) :-
	find(0,X,Es0,Es1,data(RX,TsX)),
	find(0,Y,Es1,Es2,data(RY,TsY)),
	!,
	mergeData(TsX,TsY,Ts),
	search_replace_tree(Es2,RY,_,Es3,data(RX,[])),
	search_replace_tree(Es3,RX,_,Es4,data(RX,Ts)).

mergeData([],Ts,Ts).
mergeData([T|Ts],[],[T|Ts]).
mergeData([T1|Ts1],[T2|Ts2],[T3|Ts3]) :-
	compareTerms(T1,T2,T3,Ts1,Ts2,Ss1,Ss2),
	mergeData(Ss1,Ss2,Ts3).

compareTerms(T,T,T,Ts1,Ts2,Ts1,Ts2).
compareTerms(T1,T2,T1,Ts1,Ts2,Ts1,[T2|Ts2]) :-
	T1 @< T2.
compareTerms(T1,T2,T2,Ts1,Ts2,[T1|Ts1],Ts2) :-
	T2 @< T1.


	
link(X,X,Es,Es) :-
	!.
link(RX,RY,Es0,Es1) :-
	search_replace_tree(Es0,RY,_,Es1,RX). 

