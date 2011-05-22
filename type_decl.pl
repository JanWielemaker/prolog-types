:- module(type_decl,
	  [ (type)/1,			% +Declaration
	    (pred)/1,			% +Signature
	    current_type/2,		% :Name, ?Definition
	    subtype_of/2,		% T1, T2
	    type_constraint/2,		% +Type, +Value
	    op(1150, fx, type),
	    op(1130, xfx, --->),
	    op(1150, fx, pred),		% signature declaration
	    op(200, fy, ?),		% argument mode
	    op(200, fy, @)		% argument mode
	  ]).
:- use_module(library(apply)).

/* <module> Type declarations

This module deals with Hindley-Milner declations  of types and predicate
signatures.

@tbd	Implement empty types
@tbd	Implement (a;b;c) as type argument
@tbd	Implement pred(ClosureArgs) as type argument
*/

:- meta_predicate
	current_type(:, ?).

:- multifile
	current_type/3,			% Type, Module, Constructor
	subtype_of/3.			% Type, Module, Super

%%	current_type(:Type, ?Constructor) is nondet.
%
%	True if Type is declared as a Hindley-Milner type with the given
%	Constructor.

current_type(M:T, Constructor) :-
	current_type(T, M, Constructor).

%%	subtype_of(:Type, Super) is nondet.
%
%	True if Type is a subtype of Super.
%
%	@tbd	module inheritance of types.

subtype_of(Type, Type).
subtype_of(M:Type, Super) :-
	nonvar(Type), !,
	subtype_of(Type, M, Parent),
	subtype_of(Parent, Super).
subtype_of(Type, SM:Super) :-
	nonvar(Super),
	subtype_of(Sub, SubM, SM:Super),
	subtype_of(Type, SubM:Sub).


%%	type(+Declaration)
%
%	This directive processes a type declaration. A type <T> produces
%	the following results:
%
%	  $ A semidet predicate <T>(X) :
%	  This predicates validates that X is of type <T>
%	  $ A hook for partial/2 :
%	  $ A hook for type_constraint/2 :
%	  $ Extension to current_type/2 :

type(Declaration) :-
	throw(error(context_error(nodirective, type(Declaration)), _)).

expand_type((Type ---> Constructor), []) :-
	\+ \+ (numbervars(Type, 0, _), \+ ground(Constructor)), !,
	instantiation_error(Constructor).
expand_type((TypeSpec ---> Constructor),
	    [ QTestClause,
	      QTestPartialClause,
	      type_decl:current_type(Type, M, Constructor),
	      type_decl:partial(Head, Q, Q:PartialHead),
	      (type_decl:type_constraint(Head, Q, X) :- ConstraintBody)
	    | SubTypeClauses
	    ]) :- !,
	prolog_load_context(module, M),
	subtype_clauses(TypeSpec, M, Q, Type, SubTypeClauses),
	test_clause(Type, Constructor, TestClause),
	test_partial_clause(Type, Constructor, TestPartialClause),
	constraint_body(M:Type, Constructor, X, ConstraintBody),
	qualify(M, Q, TestClause, QTestClause),
	qualify(M, Q, TestPartialClause, QTestPartialClause),
	extend(Type, X, Head),
	extend(partial_, Type, X, PartialHead).
expand_type(TypeSpec,
	    [ type_decl:current_type(Type, M, primitive)
	    | SubTypeClauses
	    ]) :-
	prolog_load_context(module, M),
	subtype_clauses(TypeSpec, M, _, Type, SubTypeClauses).


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


%%	test_clause(+Type, +TypeConstructor, -Body) is det.

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


%%	test_partial_clause(+Type, +TypeConstructor, -Body) is det.

test_partial_clause(Type, Constructor, (Head :- Body)) :-
	extend(partial_, Type, X, Head),
	test_partial_body(Constructor, X, Body).

test_partial_body((C1;C2), X, (B1->true;B2)) :- !,
	test_partial_type(C1, X, B1),
	test_partial_body(C2, X, B2).
test_partial_body(Type, X, B) :-
	test_partial_type(Type, X, B).

test_partial_type(Atom, X, (var(X) -> true ; X == Atom)) :-
	atomic(Atom), !.
test_partial_type(Term, X, (var(X) -> true ; X=T2,TArgs)) :-
	functor(Term, Name, Arity),
	functor(T2, Name, Arity),
	Term =.. [Name|TypeArgs],
	T2   =.. [Name|Args],
	maplist(partial_type_arg, TypeArgs, Args, TArgList),
	list_to_conj(TArgList, TArgs).

partial_type_arg(Any, _, B) :-
	Any == any, !,
	B = true.
partial_type_arg(Var, X, Call) :-
	var(Var), !,
	Call = type_decl:partial(Var, X).
partial_type_arg(Type, X, B) :-
	extend(partial_, Type, X, B).

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
	Call = type_decl:type_constraint(M:Type, X).


:- public partial/2.
:- meta_predicate
	partial(:,?),
	type_constraint(:,?).
:- multifile
	partial/3,
	type_constraint/3.

partial(_, X) :-
	var(X), !.
partial(M:T, X) :-
	partial(T, M, X).

%%	type_constraint(+Type, +Value) is semidet.
%
%	Create a contraint that limits Value to  be of Type. If Value is
%	ground, this is the same call(Type,Value).   If Value is partial
%	with respect to Type,  create   constraint(s)  on  the remaining
%	variable(s) that establish the type relation.

type_constraint(Type, Var) :-
	var(Var), !,
	(   get_attr(Var, type, Type2)
	->  (   Type2 \== Type
	    ->	subtype_of(NewType, Type),
		subtype_of(NewType, Type2),
		put_attr(Var, type, NewType)
	    ;	true
	    )
	;   put_attr(Var, type, Type)
	).
type_constraint(M:Type, Value) :-
	compound(Value), !,
	type_constraint(Type, M, Value).
type_constraint(value(Fixed), Value) :- !,
	Value == Fixed.
type_constraint(Type, Value) :-
	call(Type, Value).

%%	(type):attr_unify_hook(Type, Val) is semidet.
%
%	Unification hook for the type constraint.

(type):attr_unify_hook(Type, Val) :-
	type_constraint(Type, Val).

%%	pred(+Signature)
%
%	This directive provides a type,   mode and determinism signature
%	for the given Signature.

pred(Signature) :-
	throw(error(context_error(nodirective, pred(Signature)), _)).


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
