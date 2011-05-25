:- use_module(type_decl).
:- use_module(library(plunit)).

:- type system:any.
:- type system:atomic.
:- type system:compound.
:- type system:stream.
:- type system:atom    < [system:atomic].
:- type system:string  < [system:atomic].
:- type system:number  < [system:atomic].
:- type system:integer < [system:number].
:- type system:float   < [system:number].
:- type system:input_stream < [stream].
:- type system:output_stream < [stream].

:- type system:list    ---> [] ; [any|system:list].
:- type system:list(X) ---> [] ; [X|system:list(X)].

:- type system:boolean < [system:atom] ---> true ; false.

system:any(_).
system:stream(X) :- is_stream(X).
system:input_stream(X) :- is_stream(X), stream_property(X, input).
system:output_stream(X) :- is_stream(X), stream_property(X, output).

%	text stuff

system:char(X) :-
	atom(X),
	atom_length(X, 1).

system:code(X) :-
	integer(X),
	between(0, 0x10ffff, X).		% Unicode range

:- type system:char < [system:atom].
:- type system:code < [system:integer].

:- type system:codes = system:list(system:code).
:- type system:chars = system:list(system:char).


		 /*******************************
		 *	       TESTS		*
		 *******************************/

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
