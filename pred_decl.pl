:- module(pred_decl,
	  [ (pred)/1,			% +Signature
	    signature/3,		% :Goal, -ModeTypeList, -Det
	    goal_signature/2,		% :Goal, -Det
	    head_signature/2,		% :Goal, -Det
	    op(1150, fx, pred),		% signature declaration
	    op(200, fy, --),		% argument mode: must be unbound
	    op(200, fy, ++),		% argument mode: must be ground
	    op(200, fy, ?),		% argument mode
	    op(200, fy, @)		% argument mode
	  ]).
:- use_module(type_decl).

/** <module> Predicate signatures

Defined modes:

  $ +(Type) :
  Argument satifies Type at call.
  $ ++(Type) :
  Argument satifies Type and is ground at call.
  $ -(Type) :
  Argument satisfies Type at exit.  Argument is steadfast.
  $ ?(Type) :
  Unknown.  May do anything but argument satisfies Type at exit.
  $ --(Type) :
  Argument satisfies Type at exit.  Argument must be unbound at entry.
  $ @(Type) :
  Argument is not touched, but Argument satisfies Type at exit.  This
  is used for type-checks.
  $ invalidate(Type)
  Argument must be of Type at call and may not be accessed afterwards.
  This is introduced to avoid the common reuse of invalid handles, as
  illustrated below. Such code is mode and type-safe, not uncommon and
  wrong.

Defined determinism classes:

  $ failure :
  Predicate always fails.
  $ det :
  Predicate always succeeds without a choice-point.
  $ semidet :
  Predicate fails or succeeds without a choice-point.
  $ nondet :
  Predicate produces 0 or more solutions.
  $ multi :
  Predicate produces 1 or more solutions.
*/

:- multifile
	current_signature/4.

:- meta_predicate
	signature(:,-,-),
	head_signature(:,-),
	goal_signature(:,-).

%%	pred(+Signature)
%
%	This directive provides a type,   mode and determinism signature
%	for the given Signature.

pred(Signature) :-
	throw(error(context_error(nodirective, pred(Signature)), _)).

pred_clauses((A,B), M) --> !,
	pred_clauses(A, M),
	pred_clauses(B, M).
pred_clauses(G, M) -->
	[ pred_decl:current_signature(Gen, Q, Arguments, Det) ],
	{ pred_clause(G, M, Q, Gen, Arguments, Det)
	}.

pred_clause(GoalDet, M, Q, Gen, Arguments, Det) :- !,
	goal_det(GoalDet, MGoal, Det),
	strip_module(M:MGoal, Q, Goal),
	functor(Goal, F, A),
	functor(Gen, F, A),
	Goal =.. [F|Args],
	maplist(mode_arg(M), Args, Arguments).

goal_det(Goal is Det, Goal, Det) :- !.
goal_det(Goal,        Goal, nondet).		% Or unknown/var?

mode_arg(M, Spec, mode(I,Q:Type)) :-
	mode_specifier(Spec, I, Type0), !,
	strip_module(M:Type0, M1, Type1),
	resolve_type(M1:Type1, Q:Type).
mode_arg(M, Type0, mode(?,Q:Type)) :-
	strip_module(M:Type0, M1, Type1),
	resolve_type(M1:Type1, Q:Type).

mode_specifier( +(Type),  +, Type).
mode_specifier(++(Type), ++, Type).
mode_specifier( -(Type),  -, Type).
mode_specifier(--(Type), --, Type).
mode_specifier( ?(Type),  ?, Type).
mode_specifier( @(Type),  @, Type).
mode_specifier(invalidate(Type), invalidate, Type).



		 /*******************************
		 *	     SIGNATURES		*
		 *******************************/

%%	signature(:Goal, -Arguments, -Det) is nondet.
%
%	True if Arguments provide the   moded argument specification for
%	Goal and Det is the determinism   indicator.  Note that any gaol
%	may have 0 or more signatures.

signature(M:Goal, Arguments, Det) :-
	functor(Goal, F, A),
	functor(Gen, F, A),
	(   predicate_property(M:Goal, imported_from(Q))
	->  true
	;   Q = M
	),
	current_signature(Gen, Q, Arguments, Det).


%%	head_signature(:Goal, -Det) is nondet.
%
%	This predicate uses the signature declaration on the clause-head
%	to establish the constraints and modes   for  the head variables
%	and provides the determinism information about the predicate.

head_signature(M:Goal, Det) :-
	(   signature(M:Goal, Arguments, Det),
	    Goal =.. [_|GoalArgs],
	    maplist(head_arg, Arguments, GoalArgs)
	*-> true
	;   term_variables(Goal, Vars),
	    maplist(set_instantated(argument), Vars)
	).

head_arg(mode(I,T), GoalArg) :-
	head_arg(I, T, GoalArg).

head_arg(++, Type, GoalArg) :- !,
	type_constraint(Type, GoalArg),
	term_variables(GoalArg, AttVars),
	maplist(set_instantated(ground), AttVars).
head_arg(+, Type, GoalArg) :- !,
	type_constraint(Type, GoalArg),
	term_attvars(GoalArg, AttVars),
	maplist(set_instantated(type), AttVars).
head_arg(--, Type, GoalArg) :- !,
	type_constraint(Type, GoalArg),
	var(GoalArg),
	set_instantated(unbound, GoalArg).
head_arg(_, Type, GoalArg) :-
	type_constraint(Type, GoalArg).

set_instantated(How, Var) :-
	put_attr(Var, instantiated, How).

%%	goal_signature(:Goal, -Det) is nondet.
%
%	Signature is a current  mode+type   signature  with  determinism
%	information for Goal.  Goal may be partially instantiated.

goal_signature(M:Goal, Det) :-
	signature(M:Goal, Arguments, Det),
	Goal =.. [_|GoalArgs],
	maplist(goal_arg, Arguments, GoalArgs).

goal_arg(mode(I,Type), GoalArg) :-
	type_constraint(Type, GoalArg),
	term_attvars(GoalArg, AttVars),
	\+ ( member(AttVar, AttVars),
	     get_attr(AttVar, instantiated, invalid)
	   ),
	instantiated_call(I, Type, GoalArg),
	instantiated_exit(I, GoalArg).


		 /*******************************
		 *	       MODES		*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Instantiation status:
	- ground		% Ground
	- type			% Instantiated up to type
	- unbound		% Argument must be unbound at entry
	- argument		% Predicate argument, no signature

Note that instantiated to type is the same   as ground iff type does not
contain =any= (i.e., is not a _partial_ type).

If an argument has instantiated=argument, we may add a mode attribute to
indicate the desired mode. This is used to compute the modes if they are
not known at entry.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

instantiated_call(++, _Type, GoalArg) :- !,
	term_variables(GoalArg, Vars),
	maplist(demand_ground, Vars).
instantiated_call(+, _Type, GoalArg) :- !,
	term_variables(GoalArg, Vars),
	maplist(demand_instantiated, Vars).
instantiated_call(invalidate, Type, GoalArg) :- !,
	instantiated_call(+, Type, GoalArg).
instantiated_call(--, _, GoalArg) :-
	demand_free(GoalArg).
instantiated_call(_, _, _).

%%	demand_ground(+Var) is semidet.
%
%	Demand that Var is ground. We can  do this if variable is passed
%	in as an argument.

demand_ground(Var) :-
	get_attr(Var, instantiated, ground), !.
demand_ground(Var) :-
	get_attr(Var, instantiated, type),
	get_attr(Var, type, Type),
	\+ partial_type(Type), !.
demand_ground(Var) :-
	get_attr(Var, instantiated, argument),
	put_attr(Var, mode, ++).

%%	demand_instantiated(+Var) is semidet.
%
%	Demand Var to be instantiated up-to its type.

demand_instantiated(Var) :-
	get_attr(Var, instantiated, ground), !.
demand_instantiated(Var) :-
	get_attr(Var, instantiated, type), !.
demand_instantiated(Var) :-
	get_attr(Var, instantiated, argument),
	put_attr(Var, mode, +).

%%	demand_free(+Var) is semidet.
%
%	Demand Var to be free at call.  This   is  the  case if it is an
%	entirely free variable or it is an   argument,  in which case we
%	demand this argument to have mode --.

demand_free(Var) :-
	get_attr(Var, instantiated, argument),
	put_attr(Var, mode, --).
demand_free(Var) :-
	\+ attvar(Var).


%%	instantiated_exit(+Mode, +Arg)

instantiated_exit(++, _) :- !.
instantiated_exit(+, _) :- !.
instantiated_exit(@, _) :- !.
instantiated_exit(invalidate, GoalArg) :- !,
	invalidate(GoalArg).
instantiated_exit(_, GoalArg) :-
	term_attvars(GoalArg, AttVars),
	maplist(output_var, AttVars).

output_var(Var) :-
	get_attr(Var, instantiated, ground), !.
output_var(Var) :-
	put_attr(Var, instantiated, type),
	put_attr(Var, mode, -).

invalidate(Arg) :-
	var(Arg), !,
	put_attr(Arg, instantiated, invalid).
invalidate(_).


%%	partial_type(+Type) is semidet.
%
%	True if Type only specifies the top.

partial_type(Type) :-
	current_type(Type, Constructor),
	\+ (  sub_term(Any, Constructor),
	      Any == anything
	   ).



		 /*******************************
		 *	    DETERMINISM		*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
The idea is to handle determinism as  a constraint variable. This allows
for using destructive assignment.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */






		 /*******************************
		 *	      EXPANSION		*
		 *******************************/

system:term_expansion((:- pred(Decl)), Clauses) :-
	prolog_load_context(module, M),
	phrase(pred_clauses(Decl, M), Clauses).


