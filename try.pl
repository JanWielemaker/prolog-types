:- use_module(type_check).

:- type write_option --->
	(   quoted(boolean)
	;   numbervars(boolean)
	).

:- pred write_term(any, list(write_option)).
:- pred foo(boolean).
:- pred test.
:- pred test2(atomic).
:- pred bar(atom).

test :-
	foo(false),
	write_term('hello world',
		   [ quoted(true),
		     numbervars(true)
		   ]).

foo(true).

test2(X) :-
	atom(X),
	bar(X).

bar(_).
