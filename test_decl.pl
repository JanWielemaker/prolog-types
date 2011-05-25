:- use_module(type_decl).
:- use_module(library(plunit)).

:- type system:any.
:- type system:atomic.
:- type system:compound.
:- type system:atom    < [system:atomic].
:- type system:string  < [system:atomic].
:- type system:number  < [system:atomic].
:- type system:integer < [system:number].
:- type system:float   < [system:number].

:- type system:stream_or_alias.
:- type system:source_sink.
:- type system:stream  < [stream_or_alias].
:- type system:atom    < [stream_or_alias].
:- type system:input_stream_or_alias  < [stream_or_alias].
:- type system:output_stream_or_alias < [stream_or_alias].

:- type system:list    ---> [] ; [any|system:list].
:- type system:list(X) ---> [] ; [X|system:list(X)].

:- type system:boolean < [system:atom] ---> true ; false.

:- type system:segments(X) ---> X ; (system:segments(X))/(system:segments(X)).
:- type system:file_path = system:segments(system:atom).

system:any(_).
system:stream(X) :- is_stream(X).
system:input_stream(X) :- is_stream(X), stream_property(X, input).
system:output_stream(X) :- is_stream(X), stream_property(X, output).
system:stream_or_alias(X) :- is_stream(X) -> true ; atom(X).
system:source_sink(X) :-
	(   file_path(X)
	->  true
	;   compound(X),			% TBD: A/B
	    functor(X, _, 1),
	    arg(1, X, A),
	    file_path(A)
	).


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
