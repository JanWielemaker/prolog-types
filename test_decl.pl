:- use_module(type_decl).
:- use_module(library(plunit)).

:- type any.				% built-in
:- type atom.
:- type string.
:- type integer.
:- type float.
:- type compound.

:- type number ---> {integer} ; {float}.
:- type atomic ---> {atom} ; {string} ; {number}.

:- type input_stream.
:- type output_stream.
:- type stream ---> {input_stream} ; {output_stream}.


:- type system:list    ---> [] ; [any|list].
:- type system:list(X) ---> [] ; [X|list(X)].

:- type system:boolean ---> true ; false.

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
