:- initialization(main).



rewrite_all(_,[],_,[]).
rewrite_all(L1,[A|B],L2,[A1|B1]) :-
	rewrite_rule_(L1,A,L2,A1),rewrite_all(L1,B,L2,B1).

rewrite_rule1(_,A,_,A) :- var(A);number(A).

rewrite_rule1('c#',['Math','.','Sin','(',A,')'],'c',['sin','(',A,')']).
rewrite_rule1('c#',['Math','.','Cos','(',A,')'],'c',['cos','(',A,')']).
rewrite_rule1('c#',['Math','.','Tan','(',A,')'],'c',['tan','(',A,')']).

rewrite_rule1('java',['Math','.','sin','(',A,')'],'c',['sin','(',A,')']).
rewrite_rule1('java',['Math','.','cos','(',A,')'],'c',['cos','(',A,')']).
rewrite_rule1('java',['Math','.','tan','(',A,')'],'c',['tan','(',A,')']).

rewrite_rule1('wolfram',['Sin','[',A,']'],'c',['sin','(',A,')']).
rewrite_rule1('wolfram',['Cos','[',A,']'],'c',['cos','(',A,')']).
rewrite_rule1('wolfram',['Tan','[',A,']'],'c',['tan','(',A,')']).

rewrite_rule1('wolfram',['While','[',A,',',B,']'],'c',['while','(',A,')','{',B,'}']).

rewrite_rule1('prolog',['writeln','(',A,')'],javascript,['console','.','log','(',A,')']).

rewrite_rule1('prolog',['writeln','(',A,')'],javascript,['System','.','out','.','println','(',A,')']).
rewrite_rule1('prolog',['write','(',A,')'],javascript,['System','.','out','.','print','(',A,')']).
rewrite_rule1('prolog',['writeln','(',A,')'],python,['print','(',A,')']).
rewrite_rule1('python',['print','(',A,')'],ruby,['puts','(',A,')']).
rewrite_rule1('wolfram',['Print','[',A,']'],python,[print,'(',A,')']).

rewrite_rule1('z3',['(','ite',A,B,C,')'],javascript,[A,'?',B,':',C]).

rewrite_rule1('python',[print,'(',A,')'],z3,['(',echo,A,')']).

rewrite_rule1('c',[Type,A,=,B],python,[A,=,B]).

rewrite_rule1(L1,A,L2,A) :- rewrite_rule(L,A1),memberchk(A,A1),memberchk(L1,L),memberchk(L2,L).

rewrite_rule2(L1,A,L2,A) :- L1 == L2.

rewrite_rule2(A,B,C,D) :- rewrite_rule1(A,B,C,D).

rewrite_rule2(L1,A,L2,B) :-
	rewrite_rule1(L2,B,L1,A).
rewrite_rule2(L1,A,L3,C) :- rewrite_rule1(L1,A,L2,B),dif(L1,L2),nonvar(B),rewrite_rule2(L2,B,L3,C).

rewrite_rule(['c','minizinc','c++','perl','fortran','glsl','hack'],[['sin','(',A,')'],['cos','(',A,')'],['tan','(',A,')'],['asin','(',A,')'],['acos','(',A,')'],['atan','(',A,')']]).
rewrite_rule(['java','javascript','haxe','typescript'],[['Math','.','sin','(',A,')'],['Math','.','cos','(',A,')'],['Math','.','tan','(',A,')'],['Math','.','asin','(',A,')'],['Math','.','acos','(',A,')'],['Math','.','atan','(',A,')'],['Math','.','sinh','(',A,')'],['Math','.','cosh','(',A,')'],['Math','.','tanh','(',A,')']]).
rewrite_rule(['c#','visual basic .net'],[['Math','.','Sin','(',A,')'],['Math','.','Cos','(',A,')'],['Math','.','Tan','(',A,')'],['Math','.','Asin','(',A,')'],['Math','.','Acos','(',A,')'],['Math','.','Atan','(',A,')']]).
rewrite_rule([java,javascript,c,'c++',perl,'c#',haxe,scala],[['while','(',A,')','{',B,'}'],['if','(',A,')','{',B,'}']]).
rewrite_rule([c,'c#','java'],[Type,A,=,B]).
rewrite_rule([c,'c#','java','c++','haxe','perl'],[A,";"]).

rewrite_rule([bison,jison],[[A,'|',B]]).

rewrite_rule_(_,A,_,A) :- var(A).
rewrite_rule_(L1,A,L2,B) :-
	rewrite_rule2(L1,A_,L2,B_),
	%writeln(rewrite_rule2(L1,A_,L2,B_)),
	nonvar(A_),
	%subsumes_term(A_,A),
	copy_term(B_,B1),
	term_variables(A_,Vars_A),
	term_variables(B1,Vars_B),
	%writeln([Vars_A,Vars_B]),
	[A_,B1] = [A,B],
	rewrite_all(L1,Vars_A,L2,Vars_B).

rewrite_rule(A,B,C,D) :- rewrite_rule2(A,B,C,D);rewrite_rule2(C,D,A,B).

main :- 
        rewrite_rule('c',[int,a,'=',0],'python',D),writeln(D).
