:- module(pred_decl,
	  [ (pred)/1,			% +Signature
	    signature/2,		% ?Signature, -Det
	    op(1150, fx, pred),		% signature declaration
	    op(200, fy, --),		% argument mode
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
	signature(:,-).

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
mode_specifier( -(Type),  -, Type).
mode_specifier(--(Type), --, Type).
mode_specifier( @(Type),  @, Type).
mode_specifier( ?(Type),  ?, Type).


%%	signature(:Goal, -Det) is nondet.
%
%	Signature is a current  mode+type   signature  with  determinism
%	information for Goal.  Goal may be partially instantiated.

signature(M:Goal, Det) :-
	functor(Goal, F, A),
	functor(Gen, F, A),
	(   predicate_property(M:Goal, imported_from(Q))
	->  true
	;   Q = M
	),
	current_signature(Gen, Q, Arguments, Det),
	Goal =.. [F|GoalArgs],
	maplist(signature_arg, Arguments, GoalArgs).

signature_arg(mode(I,T), GoalArg) :-
	signature_arg(I, T, GoalArg).

signature_arg(_, Type, GoalArg) :-
	type_constraint(Type, GoalArg).


		 /*******************************
		 *	      EXPANSION		*
		 *******************************/

system:term_expansion((:- pred(Decl)), Clauses) :-
	prolog_load_context(module, M),
	phrase(pred_clauses(Decl, M), Clauses).


