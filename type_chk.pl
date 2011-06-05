:- module(type_chk,
	  [ check_goal/1
	  ]).
:- use_module(type_decl).
:- use_module(pred_decl).

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

:- meta_predicate
	check_goal(:).

check_goal(Goal) :-
	clause(Goal, Body),
	Goal = M:Head,
	check_clause((Head:-Body), M, []).

check_clause((Head :- Body), M, Options) :-
	variable_names(Options),
	head_signature(M:Head, _Det),
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
check_body(Goal, M) :-
	goal_signature(M:Goal, _Det).

