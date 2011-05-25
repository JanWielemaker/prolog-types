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

Mode proposal

    $ +(Type) :
    Argument satifies Type at entrance.
    $ -(Type) :
    Argument satisfies Type at exit.  Argument is steadfast.
    $ ?(Type) :
    Unknown.  May do anything but argument satisfies Type at exit.
    $ --(Type) :
    Argument satisfies Type at exit.  Argument must be unbound at entry.
    $ @(Type) :
    Argument is not touched, but Argument satisfies Type at exit.  This
    is used for type-checks.
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
mode_specifier( @(Type),  @, Type).
mode_specifier( ?(Type),  ?, Type).


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
	signature(M:Goal, Arguments, Det),
	Goal =.. [_|GoalArgs],
	maplist(head_arg, Arguments, GoalArgs).

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

%%	goal_signature(:Goal, -Det) is nondet.
%
%	Signature is a current  mode+type   signature  with  determinism
%	information for Goal.  Goal may be partially instantiated.

goal_signature(M:Goal, Det) :-
	signature(M:Goal, Arguments, Det),
	Goal =.. [_|GoalArgs],
	maplist(goal_arg, Arguments, GoalArgs).

goal_arg(mode(I,Type), GoalArg) :-
	instantiated_call(I, GoalArg),
	type_constraint(Type, GoalArg),
	instantiated_exit(I, GoalArg).

		 /*******************************
		 *	       MODES		*
		 *******************************/

instantiated_call(++, GoalArg) :- !,
	get_attr(GoalArg, instantiated, ground).
instantiated_call(+, GoalArg) :- !,
	get_attr(GoalArg, instantiated, type).
instantiated_call(--, GoalArg) :-
	\+ get_attr(GoalArg, instantiated, _).
instantiated_call(_, _).

instantiated_exit(++, _) :- !.
instantiated_exit(+, _) :- !.
instantiated_exit(@, _) :- !.
instantiated_exit(_, GoalArg) :-
	set_instantated(type, GoalArg).

set_instantated(How, Var) :-
	put_attr(Var, instantiated, How).


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


