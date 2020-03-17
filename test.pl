:- use_module(prolog_to_smt).
:- initialization(main).

main :- 
        to_minizinc(demo, Output),
		writeln(Output),
		open('output.smt',write,Stream),
        write(Stream,Output),
        nl(Stream),
        close(Stream).

demo :-
	%A>1.1,
	%B = sqrt(A),
	%A = [1,2,3],
	A = 2.0,
	C**3.0 is A**2.0.

same_length(A,B) :-
    length(A,L),
    length(B,L).

is_between(1,1,1).
is_between(1,1,2).
