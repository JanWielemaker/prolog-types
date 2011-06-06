:- module(pred_decl,
	  [ (pred)/1,			% +Signature
	    signature/3,		% :Goal, -ModeTypeList, -Det
	    goal_signature/3,		% :Goal, -Annot, -Det
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
	goal_signature(:,-,-).


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

pred_clause(GoalDet, M, Q, Gen, ArgDecl, Det) :- !,
	goal_det(GoalDet, MGoal, Det),
	strip_module(M:MGoal, Q, Goal),
	functor(Goal, F, A),
	functor(Gen, F, A),
	map_term_arguments(mode_arg(M), Goal, ArgDecl).

goal_det(Goal is Det, Goal, Det) :- !.
goal_det(Goal,        Goal, nondet).		% Or unknown/var?

mode_arg(M, _I, Spec, mode(I,Q:Type)) :-
	mode_specifier(Spec, I, Type0), !,
	strip_module(M:Type0, M1, Type1),
	resolve_type(M1:Type1, Q:Type).
mode_arg(M, _I,	Type0, mode(?,Q:Type)) :-
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

%%	signature(:Goal, -ArgDecl, -Det) is nondet.
%
%	True if ArgDecl provide  the   moded  argument specification for
%	Goal and Det is the determinism   indicator.  Note that any goal
%	may have 0 or more signatures.

signature(M:Goal, ArgDecl, Det) :-
	functor(Goal, F, A),
	functor(Gen, F, A),
	(   predicate_property(M:Goal, imported_from(Q))
	->  true
	;   Q = M
	),
	current_signature(Gen, Q, ArgDecl, Det).


%%	head_signature(:Goal, -Det) is nondet.
%
%	This predicate uses the signature declaration on the clause-head
%	to establish the constraints and modes   for  the head variables
%	and provides the determinism information about the predicate.

head_signature(M:Goal, Det) :-
	(   signature(M:Goal, ArgDecl, Det),
	    map_term_arguments(head_arg, ArgDecl, Goal)
	*-> true
	;   term_variables(Goal, Vars),
	    maplist(set_instantated(argument), Vars)
	).

head_arg(AI, mode(I,T), GoalArg) :-
	head_arg(I, T, GoalArg, AI).

head_arg(++, Type, GoalArg, _AI) :- !,
	type_constraint(Type, GoalArg),
	term_variables(GoalArg, AttVars),
	maplist(set_instantated(ground), AttVars).
head_arg(+, Type, GoalArg, _AI) :- !,
	type_constraint(Type, GoalArg),
	term_attvars(GoalArg, AttVars),
	maplist(set_instantated(type), AttVars).
head_arg(--, Type, GoalArg, _AI) :- !,
	type_constraint(Type, GoalArg),
	var(GoalArg),
	set_instantated(unbound, GoalArg).
head_arg(_, Type, GoalArg, _AI) :-
	type_constraint(Type, GoalArg).

set_instantated(How, Var) :-
	put_attr(Var, instantiated, How).

%%	goal_signature(:Goal, -Annot, -Det) is nondet.
%
%	Signature is a current  mode+type   signature  with  determinism
%	information for Goal.  Goal may be partially instantiated.

goal_signature(M:Goal, [Det|ArgAnnot], Det) :-
	signature(M:Goal, ArgDecl, Det),
	map_term_arguments(goal_arg, ArgDecl, Goal, AnnotTerm),
	AnnotTerm =.. [_|Annot],
	append(Annot, ArgAnnot).

goal_arg(AI, mode(I,Type), GoalArg, Annot) :-
	(   type_constraint(Type, GoalArg)
	->  term_attvars(GoalArg, AttVars),
	    (   member(AttVar, AttVars),
		get_attr(AttVar, instantiated, invalid)
	    ->  Annot = [error(invalid_handle(GoalArg), argument(AI))]
	    ;   (   instantiated_call(I, Type, GoalArg)
		->  instantiated_exit(I, GoalArg),
		    Annot = []
		;   Annot = [error(mode_error(I, GoalArg), argument(AI))]
		)
	    )
	;   Annot = [error(type_error(Type, GoalArg), argument(AI))]
	).


%%	map_term_arguments(:Map, ?Term).
%%	map_term_arguments(:Map, ?Term1, ?Term2).
%%	map_term_arguments(:Map, ?Term1, ?Term2, Term3).
%
%	Maps the arguments of Term1 to Term2.   Map  is called as below,
%	where Index is the index of the  argument, and Arg1 and Arg2 are
%	arguments from the terms. Both terms   must have the same arity.
%	One of the terms can be a variable.
%
%	  ==
%	  call(Map, Index, Arg1, Arg2)
%	  ==

:- meta_predicate
	map_term_arguments(2,+),
	map_term_arguments(3,?,?),
	map_term_arguments(4,?,?,?).

map_term_arguments(Check, Term) :-
	functor(Term, _, A),
	map_term_arguments1(Check, 1, A, Term).

map_term_arguments1(Check, I, A, Term) :-
	I =< A, !,
	arg(I, Term, Arg),
	call(Check, I, Arg),
	succ(I, I2),
	map_term_arguments1(Check, I2, A, Term).
map_term_arguments1(_, _, _, _).

map_term_arguments(Check, Term1, Term2) :-
	same_arity([Term1, Term2], A),
	map_term_arguments2(Check, 1, A, Term1, Term2).

map_term_arguments2(Check, I, A, Term1, Term2) :-
	I =< A, !,
	arg(I, Term1, Arg1),
	arg(I, Term2, Arg2),
	call(Check, I, Arg1, Arg2),
	succ(I, I2),
	map_term_arguments2(Check, I2, A, Term1, Term2).
map_term_arguments2(_, _, _, _, _).

map_term_arguments(Check, Term1, Term2, Term3) :-
	same_arity([Term1, Term2, Term3], A),
	map_term_arguments3(Check, 1, A, Term1, Term2, Term3).

map_term_arguments3(Check, I, A, Term1, Term2, Term3) :-
	I =< A, !,
	arg(I, Term1, Arg1),
	arg(I, Term2, Arg2),
	arg(I, Term3, Arg3),
	call(Check, I, Arg1, Arg2, Arg3),
	succ(I, I2),
	map_term_arguments3(Check, I2, A, Term1, Term2, Term3).
map_term_arguments3(_, _, _, _, _, _).

same_arity(Terms, A) :-
	member(T, Terms),
	nonvar(T), !,
	functor(T, N, A),
	maplist(name_arity(N,A), Terms).

name_arity(N, A, T) :-
	functor(T, N, A), !.
name_arity(_, A, T) :-
	functor(T, _, A), !.


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

%%	instantiated_call(+Mode, +Type, +Arg) is semidet.

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
	demand_mode(++, Var).

%%	demand_instantiated(+Var) is semidet.
%
%	Demand Var to be instantiated up-to its type.

demand_instantiated(Var) :-
	get_attr(Var, instantiated, ground), !.
demand_instantiated(Var) :-
	get_attr(Var, instantiated, type), !.
demand_instantiated(Var) :-
	get_attr(Var, instantiated, argument),
	demand_mode(+, Var).

%%	demand_free(+Var) is semidet.
%
%	Demand Var to be free at call.  This   is  the  case if it is an
%	entirely free variable or it is an   argument,  in which case we
%	demand this argument to have mode --.

demand_free(Var) :-
	get_attr(Var, instantiated, argument),
	demand_mode(--, Var).
demand_free(Var) :-
	\+ attvar(Var).


%%	instantiated_exit(+Mode, +Arg) is det.

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
	demand_mode(-, Var).

invalidate(Arg) :-
	var(Arg), !,
	put_attr(Arg, instantiated, invalid).
invalidate(_).

%%	demand_mode(+Mode, +Var) is semidet.
%
%	Update the mode property for a new body goal.

demand_mode(Mode, Var) :-
	get_attr(Var, mode, OldMode), !,
	update_mode(OldMode, Mode, NewMode),
	(   NewMode == Mode
	->  true
	;   put_attr(Var, mode, NewMode)
	).
demand_mode(Mode, Var) :-
	put_attr(Var, mode, Mode).

update_mode(+, --, _) :- !, fail.
update_mode(M, _, M).


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


