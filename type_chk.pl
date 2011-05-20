:- module(type_chk,
	  [
	  ]).
:- use_module(type_decl).

/** <module> The type checker

The type checker is based on attributed variables to track the state of
variables.  It uses several attributes:

	* type
	Reflect the current notion of the type.  Unification can fail
	or get a common subtype.
	* instantiated
	One of =var=, =partial= or =ground=.
	* name
	If available, the name of the variable.  Used for feedback.
*/

check_clause((Head :- Body), M, Options) :-
	variable_names(Options),
	type_signature(M:Head),
	check_body(Body, M).


variable_names(Options) :-
	option(variable_names(Names), Options), !,
	maplist(set_var_name, Names).
variable_names(_).

set_var_name(Name=Var) :-
	put_attr(Var, name, Name).

check_body((A,B), M) :- !,
	check_body(A, M),
	check_body(B, M).
