:- module(type_decl,
	  [ (type)/1,			% +Declaration
	    current_type/2,		% :Name, ?Definition
	    subtype_of/2,		% T1, T2
	    type_constraint/2,		% +Type, +Value
	    op(1150, fx, type),
	    op(1130, xfx, --->)
	  ]).
:- use_module(library(apply)).
:- use_module(library(lists)).

/* <module> Type declarations

This module deals with Hindley-Milner declations  of types.

@tbd	Implement empty types
@tbd	Implement (a;b;c) as type argument
@tbd	Implement pred(ClosureArgs) as type argument
*/

:- meta_predicate
	current_type(:, ?),
	subtype_of(:, :).

:- multifile
	current_type/3,			% Type, Module, Constructor
	subtype_of/3.			% Type, Module, Super

qualify_type(M:Type, Q:Type) :-
	(   var(Type)
	->  Q = M
	;   current_type(Type, M, _)
	->  Q = M
	;   extend(Type, _, Test),
	    predicate_property(M:Test, imported_from(M2))
	->  Q = M2
	;   Q = M
	).

%%	current_type(:Type, ?Constructor) is nondet.
%
%	True if Type is declared as a Hindley-Milner type with the given
%	Constructor.

current_type(Type, Constructor) :-
	qualify_type(Type, M:T),
	current_type(T, M, Constructor).

%%	subtype_of(:Type, :Super) is nondet.
%
%	True if Type is a subtype of Super.
%
%	@tbd	module inheritance of types.

subtype_of(Sub, Super) :-
	qualify_type(Sub, QSub),
	qualify_type(Super, QSuper),
	qsubtype_of(QSub, QSuper).

qsubtype_of(Type, Type).
qsubtype_of(M:Type, Super) :-
	nonvar(Type), !,
	subtype_of(Type, M, Parent),
	qsubtype_of(Parent, Super).
qsubtype_of(Type, Super) :-
	nonvar(Super),
	subtype_of(Sub, SubM, Super),
	qsubtype_of(Type, SubM:Sub).

%%	constructor_value(+Constructor, -Value) is nondet.
%
%	Value is a concrete value that   appears in Constructor. Used to
%	combine hard values and finding common subtypes.

constructor_value((A;B), Value) :-
	(   constructor_value(A, Value)
	;   constructor_value(B, Value)
	).
constructor_value('$primitive', _) :- !, fail.
constructor_value(Value, Value) :-
	atomic(Value).


%%	type(+Declaration)
%
%	This directive processes a type declaration. A type <T> produces
%	the following results:
%
%	  $ A semidet predicate <T>(X) :
%	  This predicates validates that X is of type <T>
%	  $ A hook for type_constraint/2 :
%	  $ Extension to current_type/2 :

type(Declaration) :-
	throw(error(context_error(nodirective, type(Declaration)), _)).

expand_type((Type ---> Constructor), []) :-
	\+ \+ (numbervars(Type, 0, _), \+ ground(Constructor)), !,
	instantiation_error(Constructor).
expand_type((TypeSpec ---> Constructor),
	    [ QTestClause,
	      type_decl:current_type(Type, Q, Constructor),
	      (type_decl:type_constraint(Type, Q, X) :- ConstraintBody)
	    | SubTypeClauses
	    ]) :- !,
	prolog_load_context(module, M),
	subtype_clauses(TypeSpec, M, Q, Type, SubTypeClauses),
	test_clause(Type, Constructor, TestClause),
	constraint_body(M:Type, Constructor, X, ConstraintBody),
	qualify(M, Q, TestClause, QTestClause).
expand_type(TypeSpec,
	    [ type_decl:current_type(Type, Q, '$primitive')
	    | SubTypeClauses
	    ]) :-
	prolog_load_context(module, M),
	subtype_clauses(TypeSpec, M, Q, Type, SubTypeClauses).


subtype_clauses(QType < Supers, M, Q, Type, SubTypeClauses) :- !,
	strip_module(M:QType, Q, Type),
	maplist(subtype_clause(Type, Q), Supers, SubTypeClauses).
subtype_clauses(QType, M, Q, Type, []) :-
	strip_module(M:QType, Q, Type).

subtype_clause(Type, M, QSuper,
	       type_decl:subtype_of(Type, M, Q:Super)) :-
	strip_module(M:QSuper, Q, Super).

qualify(M, M, G, G) :- !.
qualify(_, Q, G, Q:G).


%%	test_clause(+Type, +TypeConstructor, -Clause) is det.
%
%	Clause is a semidet  unary  predicate   that  tests  that a term
%	satisfies Type.

test_clause(Type, Constructor, (Head :- Body)) :-
	extend(Type, X, Head),
	test_body(Constructor, X, Body).

test_body((C1;C2), X, (B1->true;B2)) :- !,
	test_type(C1, X, B1),
	test_body(C2, X, B2).
test_body(Type, X, B) :-
	test_type(Type, X, B).

test_type(Atom, X, (X == Atom)) :-
	atomic(Atom), !.
test_type(Term, X, (nonvar(X),X=T2,TArgs)) :-
	functor(Term, Name, Arity),
	functor(T2, Name, Arity),
	Term =.. [Name|TypeArgs],
	T2   =.. [Name|Args],
	maplist(type_arg, TypeArgs, Args, TArgList),
	list_to_conj(TArgList, TArgs).

type_arg(Any, _, B) :-
	Any == any, !,
	B = true.
type_arg(Var, X, Call) :-
	var(Var), !,
	Call = call(Var, X).
type_arg(Type, X, B) :-
	extend(Type, X, B).


%%	constraint_clause(+Type, +TypeConstructor, -Body) is det.
%
%	This clause is called from   type_constraint/2, iff the argument
%	is a compound term.

constraint_body(M:_Type, Constructor, X, Body) :-
	constructor_constraint(Constructor, M, X, Body).

constructor_constraint((C1;C2), M, X, B) :- !,
	constraint_type(C1, M, X, B1),
	constructor_constraint(C2, M, X, B2),
	one_of(B1, B2, B).
constructor_constraint(Type, M, X, B) :-
	constraint_type(Type, M, X, B).

one_of(true, B, B) :- !.
one_of(B, true, B) :- !.
one_of(B1, B2, (B1->true;B2)).

constraint_type(Atom, _, _, true) :-
	atomic(Atom), !.
constraint_type(Term, M, X, (X = T2, TArgs)) :-
	functor(Term, Name, Arity),
	functor(T2, Name, Arity),
	Term =.. [Name|TypeArgs],
	T2   =.. [Name|Args],
	maplist(constraint_type_arg(M), TypeArgs, Args, TArgList),
	list_to_conj(TArgList, TArgs).

constraint_type_arg(_, Any, _, B) :-
	Any == any, !,
	B = true.
constraint_type_arg(M, Type, X, Call) :-
	strip_module(M:Type, Q, PT),
	Call = type_decl:type_constraint(Q:PT, X).


:- meta_predicate
	type_constraint(:,?).
:- multifile
	type_constraint/3.

%%	type_constraint(:Type, +Value) is semidet.
%
%	Create a contraint that limits Value to  be of Type. If Value is
%	ground, this is the same call(Type,Value).   If Value is partial
%	with respect to Type,  create   constraint(s)  on  the remaining
%	variable(s) that establish the type relation.

type_constraint(Type, Value) :-
	qualify_type(Type, QType),
	qtype_constraint(QType, Value).

qtype_constraint(Type, Var) :-
	var(Var), !,
	(   get_attr(Var, type, Type2)
	->  common_subtype(Type, Type2, NewType),
	    (	NewType == Type2
	    ->	true
	    ;	put_attr(Var, type, NewType)
	    )
	;   put_attr(Var, type, Type)
	).
qtype_constraint(M:Type, Value) :-
	compound(Value), !,
	type_constraint(Type, M, Value).
qtype_constraint(Type, Value) :-
	call(Type, Value).

%%	common_subtype(+T1, +T2, -T) is nondet.
%
%	T is a common subtype of T1 and T2. The findall and member is to
%	provide early determinism.
%
%	@tbd	Remove subtypes of already present types

common_subtype(T, T, T) :- !.
common_subtype(T1, T2, T) :-
	findall(T, gen_common_subtype(T1,T2,T), TL),
	member(T, TL).

gen_common_subtype(T1, T2, T) :-
	qsubtype_of(T, T1),
	qsubtype_of(T, T2).
gen_common_subtype(T1, T2, T) :-
	(   sub_atomic_general(T1, T2, T)
	;   sub_atomic_general(T2, T1, T)
	).

sub_atomic_general(T1, M:T2, T) :-
	qsubtype_of(T1, system:atomic),
	current_type(T2, M, Constructor),
	findall(V, constructor_value(Constructor, V), Vs0),
	sort(Vs0, Vs),
	Vs \== [],
	(   Vs = [V]
	->  T = system:(=(V))
	;   T = lists:member(Vs)
	).

%%	(type):attr_unify_hook(Type, Val) is semidet.
%
%	Unification hook for the type constraint.

(type):attr_unify_hook(system:(=(Value)), Val) :- !,
	(   get_attr(Val, type, Type)
	->  call(Type, Value)
	;   nonvar(Val)
	->  Val == Value
	).
(type):attr_unify_hook(lists:member(Set), Val) :- !,
	(   get_attr(Val, type, Type)
	->  (   Type = lists:member(Set2)
	    ->	ord_intersection(Set, Set2, NewSet),
		NewSet \== [],
		put_attr(Val, type, lists:member(NewSet))
	    ;	include(call(Type), Set, NewSet),
		NewSet \== [],
		put_attr(Val, type, lists:member(NewSet))
	    )
	;   nonvar(Val)
	->  memberchk(Val, Set)
	).
(type):attr_unify_hook(Type, Val) :-
	type_constraint(Type, Val).		% qtype_constraint?

(type):attribute_goals(Var) -->
	{ get_attr(Var, type, Type) },
	type_goals(Type, Var).

type_goals(Type, Var) -->
	[ type_constraint(Type, Var) ].

		 /*******************************
		 *	       UTIL		*
		 *******************************/

extend(T, _, _) :-
	var(T), !,
	instantiation_error(T).
extend(M:T, Var, M:T2) :-
	extend(T, Var, T2).
extend(T, Var, T2) :-
	T =.. List,
	append(List, [Var], List2),
	T2 =.. List2.

extend(_, T, _, _) :-
	var(T), !,
	instantiation_error(T).
extend(Prefix, M:T, Var, M:T2) :-
	extend(Prefix, T, Var, T2).
extend(Prefix, T, Var, T2) :-
	T =.. [Name|List],
	append(List, [Var], List2),
	atom_concat(Prefix, Name, PrefixName),
	T2 =.. [PrefixName|List2].

list_to_conj([], true).
list_to_conj([G], G) :- !.
list_to_conj([true|T], G) :- !,
	list_to_conj(T, G).
list_to_conj([H|T], (H,G)) :-
	list_to_conj(T, G).


		 /*******************************
		 *	      HOOK		*
		 *******************************/

system:term_expansion((:- type(Type)), Clauses) :-
	expand_type(Type, Clauses).
