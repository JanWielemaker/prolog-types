:- use_module(type_check).

:- type write_option --->
	(   quoted(boolean)
	;   numbervars(boolean)
	).

:- pred write_term(any, list(write_option)).
:- pred foo(boolean).
:- pred test.

test :-
	foo(false),
	write_term('hello world',
		   [ quoted(true),
		     numbervars(true)
		   ]).

foo(true).
