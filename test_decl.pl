:- use_module(type_decl).
:- use_module(library(plunit)).

:- type system:atomic.
:- type system:compound.
:- type system:atom    < [system:atomic].
:- type system:number  < [system:atomic].
:- type system:integer < [system:number].
:- type system:float   < [system:number].

:- type system:list --->
	(   []
	;   [any|system:list]
	).

:- type list(X) --->
	(   []
	;   [X|list(X)]
	).

:- begin_tests(types).

test(hier, true) :-
	type_constraint(atomic, X),
	type_constraint(integer, X),
	X = 3.
test(hier, fail) :-
	type_constraint(atomic, X),
	type_constraint(integer, X),
	X = a.

:- end_tests(types).
