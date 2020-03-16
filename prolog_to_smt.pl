:- module(prolog_to_minizinc, [to_minizinc/2]).
:- set_prolog_flag('double_quotes','chars').
:- use_module(type_inference).
:- use_module(partial_evaluation).
:- use_module(library(clpfd)).


types_to_vars([A],[],Loop_vars) :-
	var(A).
types_to_vars([(Var:Type)|Rest],[Var1|Rest1],Loop_vars) :-
	type_to_var(Var:Type,Var1,Loop_vars),
	types_to_vars(Rest,Rest1,Loop_vars).

type_(A,B) :- type(A,B).
type_([list,_,T],["(Array Int ",T1,")"]) :- type_(T,T1).


type(bool,"Bool").
type(number,"Real").
type(int,"Int").

remove_var([]).
remove_var([Loop_var|Rest]) :-
	var(Loop_var),Loop_var=[],Rest=[];
	
	nonvar(Loop_var),(nonvar(Rest),remove_var(Rest);
	var(Rest),Rest=[]).

not_loop_var(Var, Loop_vars) :-
	writeln(['loop vars',Loop_vars]),
	not(memberchk(loop_var(Var),Loop_vars)).

type_to_var_(A:T,[Type],Loop_vars) :- not_loop_var(A,Loop_vars),type(T,Type),nonvar(A).
type_to_var_(A:[list,Length,T],["(List ",Type,")"],Loop_vars) :- not_loop_var(A,Loop_vars),nonvar(A),(var(Length),L="int";nonvar(Length),number(Length),number_chars(Length,Length1),L=["1..",Length1]),type_to_var_(A:T,Type,Loop_vars).
type_to_var_(A:Type,[],Loop_vars) :- writeln('matching other pattern'),(member(loop_var(A),Loop_vars);nonvar(A),writeln(A:Type);var(A),writeln(A:Type)).

type_to_var(A:T,["(declare-const ",A," ",Type,")"],Loop_vars) :- not_loop_var(A,Loop_vars),type(T,Type),nonvar(A).
type_to_var(A:[list,Length,T],["(declare-const ",A," (Array Int ",Type,"))"],Loop_vars) :- not_loop_var(A,Loop_vars),nonvar(A),(var(Length),L="int";nonvar(Length),number(Length),number_chars(Length,Length1),L=["1..",Length1]),type_to_var_(A:T,Type,Loop_vars).
type_to_var(A:Type,[],Loop_vars) :- writeln('matching other pattern'),(member(loop_var(A),Loop_vars);nonvar(A),writeln(A:Type);var(A),writeln(A:Type)).

to_minizinc(A,B) :- to_minizinc(A,B,_).

to_minizinc(Term0,Output,_) :-
	partial_evaluation:find_all_clauses(Term0,Term),
	writeln(['partial_evaluation',Term]),
	type_inference:type_inference(Term:Type,Types),writeln(Types),Loop_vars=[_|_],prolog_to_minizinc(Term,C,Loop_vars,Types),writeln(['loop variables: ',Loop_vars]),term_variables(C,Vars),writeln(Term),
	vars_to_digits(0,Vars),remove_var(Loop_vars),types_to_vars(Types,Types1,Loop_vars),C_=[Types1,"(assert ",C,")"],append_all(C_,C1),atom_chars(Output,C1).

vars_to_digits(_,[]).
vars_to_digits(Index,[Var1|Vars]) :-
	number_chars(Index,Var),
	Var1 = ['A',Var],
	Index1 is Index + 1,
	vars_to_digits(Index1,Vars).

matches_any_([],B) :- false.
matches_any_([A|A1],B) :-
	subsumes_term(A,B),A=B;matches_any_(A1,B).

matches_any(A,B) :-
	nonvar(A),matches_any_(A,B).

append_all(A,A) :- var(A).
append_all([],[]).
append_all([A|B],C) :- is_list(A),append_all(A,A1),append_all(B,B1),append(A1,B1,C).
append_all([A|B],C) :- (var(A);atom(A)),append_all(B,B1),append([A],B1,C).


prolog_to_minizinc(A,A1,_,_) :-
	number(A),number_chars(A,A1).
prolog_to_minizinc(A,A,_,_) :-
	var(A).

matches_to_outputs([Patterns|Patterns1],T,Output) :-
	Patterns = [Pattern1,Pattern2],
	matches_any(Pattern1,T),
	Pattern2 = Output;
	nonvar(Patterns1),
	matches_to_outputs(Patterns1,T,Output).

list_to_minizinc([],[],_).
list_to_minizinc([L|Rest],[Next|Output1],Types) :-
	prolog_to_minizinc(L,L1,_,Types),
	(Rest == [],Next=[L1];
	length(Rest,Length),Length>0,Next = [L1,","]),
	list_to_minizinc(Rest,Output1,Types).

prolog_to_minizinc(T,["[",T1,"]"],_,Types) :-
	list_to_minizinc(T,T1,Types).

prolog_to_minizinc(T,Output,Loop_vars,Types) :-
	matches_to_outputs([
		[[false],["false"]],
		[[true],["true"]]
	],T,Output);
	
	matches_to_outputs([
		[[append(A,B,C)],["(",A1,"++",B1,"==",C1,")"]],
		[[nth1(A,B,C)],["(= (select ",B1,"  (+ 1 ",A1,")) ",C1,"))"]],
		[[nth0(A,B,C)],["(= (select ",B1," ",A1,") ",C1,"))"]],
		[[union(A,B,C)],[("(",C1, "== ",A1," union ",B1,")")]],
		[[intersection(A,B,C)],[("(",C1, "== ",A1," intersection ",B1,")")]]
	],T,Output),
	prolog_to_minizinc(A,A1,Loop_vars,Types),
	prolog_to_minizinc(B,B1,Loop_vars,Types),
	prolog_to_minizinc(C,C1,Loop_vars,Types);
	
	matches_to_outputs([
		[[var(A),nonvar(A)],[A1]],
		[[sin(A)],["sin(",A1,")"]],
		[[cos(A)],["cos(",A1,")"]],
		[[tan(A)],["tan(",A1,")"]],
		[[asin(A)],["asin(",A1,")"]],
		[[acos(A)],["acos(",A1,")"]],
		[[atan(A)],["atan(",A1,")"]],
		[[asinh(A)],["asinh(",A1,")"]],
		[[acosh(A)],["acosh(",A1,")"]],
		[[atanh(A)],["atanh(",A1,")"]],
		[[exp(A)],["exp(",A1,")"]],
		[[A**B],["(^ ",A1," ",B1,")"]],
		[[sqrt(A)],["(^ ",A1," 0.5)"]],
		[[log(A)],["ln(",A1,")"]],
		[[abs(A)],["abs(",A1,")"]],
		[[all_distinct(A),all_different(A)],["alldifferent(",A1,")"]],
		[[number(A),float(A),rational(A),is_list(A),var(A),integer(A1)],[]]
	],T,Output),
	prolog_to_minizinc(A,A1,Loop_vars,Types);
		
	matches_to_outputs([
		[[(A;B)],["(or ",A1," ",B1,")"]],
		[[length(A,B)],["(length(",A1,") == ",B1,")"]],
		[[(A,B)],["(and ",A1," ",B1,")"]],
		[[(A+B)],["(+ ",A1," ",B1,")"]],
		[[(A/B)],["(/ ",A1," ",B1,")"]],
		[[(A>B)],["(> ",A1," ",B1,")"]],
		[[(A<B)],["(< ",A1," ",B1,")"]],
		[[(A>=B)],["(>= ",A1,"  ",B1,")"]],
		[[(A=<B)],["(<= ",A1," ",B1,")"]],
		[[A\=B,A\==B],["(!= ",A1," ",B1,")"]],
		[[(A-B)],["(- ",A1," ",B1,")"]],
		[[(A*B)],["(* ",A1," ",B1,")"]],
		[[(A->B)],["(=> ",A1," ",B1,")"]],
		[[member(A,B),memberchk(A1,B1)],["(",A1," in ",B1,")"]],
		[[A==B,(A = B),A is B],["(= ",A1," ",B1,")"]],
		[[findall(A,B,C)],["(",C1," == [",A1,"|",B1,"])"]],
		[[max_list(A,B)],["(",B1,"==max(",A1,"))"]],
		[[min_list(A,B)],["(",B1,"==min(",A1,"))"]],
		[[subset(A,B)],["(",A," subset ",A,")"]],
		[[not(A),\+(A)],["(not ",A1,")"]]
	],T,Output),
	prolog_to_minizinc(A,A1,Loop_vars,Types),
	prolog_to_minizinc(B,B1,Loop_vars,Types);
	
	T1= [list,_,_],
	matches_to_outputs([
		[[foreach(A,B),forall(A,B),\+ (call(A),\+call(B))],["(forall (",A2," ",T2,") ",B1,")"]]
	],T,Output),
	A = member(A2,_),
	writeln(['the variable',A]),
	writeln(['the types',Types]),
	%type_inference:type_inference(A2:T1,Types),
	%type_(T1,T2),
	prolog_to_minizinc(A,A1,Loop_vars,Types),
	prolog_to_minizinc(B,B1,Loop_vars,Types),
	writeln(['ADDING LOOP VARS',A]),
	get_loop_vars(A,Loop_vars).

add_loop_var([Loop_var|Loop_vars],Var) :-
	var(Loop_var),Loop_var = loop_var(Var);nonvar(Loop_var),add_loop_var(Loop_vars,Var).

add_loop_vars(_,[]).
add_loop_vars(Loop_vars,[Var|Vars]) :-
	add_loop_var(Loop_vars,Var),add_loop_vars(Loop_vars,Vars).

get_loop_vars_(T,Loop_vars) :-
	term_variables(T,Vars),
	add_loop_vars(Loop_vars,Vars),
	writeln(Vars).

get_loop_vars(Input,Loop_vars) :-
	matches_any([member(T,_),memberchk(T,_)],Input),
	get_loop_vars_(T,Loop_vars);
	matches_any([(member(T,_),Next),(memberchk(T,_),Next)],Input),
	get_loop_vars_(T,Loop_vars),
	get_loop_vars(Next,Loop_vars).
