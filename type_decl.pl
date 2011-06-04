:- module(type_decl,
	  [ (type)/1,			% +Declaration
	    current_type/2,		% :Name, ?Definition
	    resolve_type/2,		% :TypeIn, -TypeOut
	    type_constraint/2,		% +Type, +Value
	    normalise_type/2,		% +TypeIn, -TypeOut
	    op(1150, fx, type),
	    op(1130, xfx, --->)
	  ]).
:- use_module(library(apply)).
:- use_module(library(lists)).

/* <module> Type declarations

This module deals with Hindley-Milner declations  of types.

@tbd	Implement (a;b;c) as type argument
@tbd	Implement pred(ClosureArgs) as type argument
*/

:- meta_predicate
	current_type(:, ?),
	subtype_of(:, :),
	resolve_type(:, -).

:- multifile
	current_type/3,			% Type, Module, Constructor
	subtype_of/3,			% Type, Module, Super
	type_alias/3.			% Type, Module, Alias

%%	resolve_type(:Type, -QType) is det.
%
%	@tbd	Ok in mode (+,-), but not in other modes
%	@tbd	Handling aliases here is dubious.

resolve_type(M0:Type0, M:Type) :-
	qualify_outer_type(M0:Type0, M:Type1),
	(   functor(Type1, F, Arity), Arity>0
	->  Type1 =.. [F|A1],
	    maplist(resolve_type(M0), A1, A),
	    Type  =.. [F|A]
	;   Type = Type1
	).

resolve_type(M0, Type0, Type) :-
	strip_module(M0:Type0, M1, Type1),
	resolve_type(M1:Type1, Type).

qualify_outer_type(M:Type, Q:TypeOut) :-
	(   var(Type)
	->  Q = M, TypeOut = Type
	;   current_type(Type, M, _)
	->  Q = M, TypeOut = Type
	;   type_alias(Type, M, Alias)
	->  resolve_type(Alias, Q:TypeOut)
	;   extend(Type, _, Test),
	    predicate_property(M:Test, imported_from(M2))
	->  (   type_alias(Type, M2, Alias)
	    ->	resolve_type(Alias, Q:TypeOut)
	    ;	Q = M2, TypeOut = Type
	    )
	;   Q = M, TypeOut = Type
	).

%%	current_type(:Type, ?Constructor) is nondet.
%
%	True if Type is declared as a Hindley-Milner type with the given
%	Constructor.

current_type(Type, Constructor) :-
	resolve_type(Type, M:T),
	current_type(T, M, Constructor).

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
	    ]) :- !,
	prolog_load_context(module, M),
	strip_module(M:TypeSpec, Q, Type),
	test_clause(Type, Constructor, TestClause),
	constraint_body(M:Type, Constructor, X, ConstraintBody),
	qualify(M, Q, TestClause, QTestClause).
expand_type(MAlias = MType,
	    [ type_decl:type_alias(Alias, QA, QT:QType),
	      (AliasHead :- TypeHead)
	    ]) :- !,
	prolog_load_context(module, M),
	strip_module(M:MAlias, QA, Alias),
	strip_module(M:MType, QT, QType),
	extend(QA:Alias, X, AliasHead),
	extend(QT:QType, X, TypeHead).
expand_type(TypeSpec,
	    [ type_decl:current_type(Type, Q, '$primitive')
	    ]) :-
	prolog_load_context(module, M),
	strip_module(M:TypeSpec, Q, Type).

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
test_type(Var, X, B) :-
	var(Var),
	type_arg(Var, X, B).
test_type({Type}, X, Goal) :- !,
	extend(Type, X, Goal).
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
constraint_type(Var, M, X, B) :-
	var(Var), !,
	B = type_decl:type_constraint(M:Var, X).
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
	resolve_type(Type, QType),
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
qtype_constraint(system:any, _) :- !.
qtype_constraint(M:Type, Value) :-
	compound(Value), !,
	type_constraint(Type, M, Value).
qtype_constraint(Type, Value) :-
	call(Type, Value).

%%	normalise_type(:TypeIn, :TypeOut) is det.
%
%	TypeOut is a normalised form of  TypeIn.   Fails  if no term can
%	satisfy  TypeIn,  i.e.,  TypeIn  is    inconsistent.   The  type
%	representation is as follows:
%
%	  * =(Value)
%	  True if Term is Value (Value is atomic)
%	  * compound(Name, Arity, ArgTypes)
%	  True if Term is a compound of Name/Arity and ArgTypes describe
%	  the types of the arguments
%	  * anything
%	  Always true
%	  * nothing
%	  Always false.  This means the type is inconsistent.
%	  * primitive(:Test)
%	  Type is built-in and Test validates that an object is
%	  of the Type.
%	  * union(Type1,Type2)
%	  Type disjunction
%	  * intersection(Type1,Type2)
%	  Type intersection
%	  * not(Type)
%	  Type negation
%
%	We first translate the type to   disjunctive  normal form (DNF),
%	after which we evaluate the conjunctions and combine them.  For
%	the conjunctions.
%
%	Note  that  TypeIn  is   fully    (module)   qualified.   Module
%	qualifications are immediately attached to   Type?  in the above
%	definitions, _not_ to the other terms.

normalise_type(TypeIn, TypeOut) :-
	nnf(TypeIn, NNF),
	dnf(NNF, DNF1),
	simplify_conj(DNF1, DNF1),
	simplify_disj(DNF1, TypeOut).

%%	nnf(+Formula, -NNF)
%
%	Rewrite to Negative Normal Form, meaning negations only appear
%	around literals.

nnf(not(not(A0)), A) :- !,
	nnf(A0, A).
nnf(not(intersection(A0,B0)), union(A,B)) :- !,
	nnf(not(A0), A),
	nnf(not(B0), B).
nnf(not(union(A0,B0)), intersection(A,B)) :- !,
	nnf(not(A0), A),
	nnf(not(B0), B).
nnf(A, A).


%%	dnf(+NNF, -DNF)
%
%	Convert a formula in NNF to Disjunctive Normal Form (DNF)

dnf(union(A0,B0), union(A, B)) :- !,
	dnf(A0, A),
	dnf(B0, B).
dnf(intersection(A0,B0), DNF):- !,
	dnf(A0, A1),
	dnf(B0, B1),
	dnf1(intersection(A1,B1), DNF).
dnf(DNF, DNF).

dnf1(intersection(A0, union(B,C)), union(P,Q)) :- !,
	dnf1(intersection(A0,B), P),
	dnf1(intersection(A0,C), Q).
dnf1(intersection(union(B,C), A0), union(P,Q)) :- !,
	dnf1(intersection(A0,B), P),
	dnf1(intersection(A0,C), Q).
dnf1(DNF, DNF).

%%	simplify_conj(+DNFIn, -DNFOut) is det.
%
%	Simplifies the (inner) intersection  and   negations  inside the
%	(outer) union.

simplify_conj(union(A0,B0), union(A,B)) :- !,
	simplify_conj(A0, A),
	simplify_conj(B0, B).
simplify_conj(A0, A) :-
	intersection_list(A0, L0),
	simplify_list(conj, L0, L),
	intersection_list(A, L).

:- meta_predicate
	simplify_list(3, +, -).

simplify_list(Reduce, L0, L) :-
	select(A1, L0, L1),
	select(A2, L1, L2),
	call(Reduce, A1, A2, A), !,
	simplify_list(Reduce, [A|L2], L).
simplify_list(_, L, L).

intersection_list(Intersection, List) :-
	nonvar(Intersection), !,
	phrase(intersection_list(Intersection), List).
intersection_list(Intersection, List) :-
	list_intersection(List, Intersection).

intersection_list(intersection(A,B)) -->
	intersection_list(A),
	intersection_list(B).
intersection_list(A) -->
	[A].

list_intersection([One], One) :- !.
list_intersection([H|T], intersection(H,R)) :-
	list_intersection(T, R).


conj(X, X, X).
conj(anything, X, X).
conj(nothing, _, nothing).
conj(=(V), primitive(Test), Type) :-
	(   call(Test, V)
	->  Type = =(V)
	;   Type = nothing
	).
conj(=(V), not(primitive(Test)), Type) :-
	(   call(Test, V)
	->  Type = nothing
	;   Type = =(V)
	).
conj(not(=(_)), primitive(Test), primitive(Test)). % Simplified
conj(compound(N,A,T), primitive(compound), compound(N,A,T)).
conj(compound(N,A,AV1), compound(N,A,AV2), compound(N,A,AV)) :-
	maplist(normalise_type, intersection(AV1,AV2), AV).

%%	simplify_disj(+UnionIn, -UnionOut) is det.
%
%	Simplify the outer union of the DNF.

simplify_disj(UnionIn, UnionOut) :-
	union_list(UnionIn, L0),
	simplify_list(disj, L0, L),
	union_list(UnionOut, L).

union_list(Intersection, List) :-
	nonvar(Intersection), !,
	phrase(union_list(Intersection), List).
union_list(Intersection, List) :-
	list_union(List, Intersection).

union_list(union(A,B)) -->
	union_list(A),
	union_list(B).
union_list(A) -->
	[A].

list_union([One], One) :- !.
list_union([H|T], intersection(H,R)) :-
	list_intersection(T, R).

disj(X, X, X).
disj(anything, _, anything).
disj(nothing, X, X).


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
