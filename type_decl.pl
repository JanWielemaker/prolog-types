:- module(type_decl,
	  [ (type)/1,			% +Declaration
	    current_type/2,		% :Name, ?Definition
	    resolve_type/2,		% :TypeIn, -TypeOut
	    type_constraint/2,		% +Type, +Value
	    type_test/2,		% +Type, +Value
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
	resolve_type(:, -),
	type_constraint(:, ?),
	type_test(:, ?).

:- multifile
	current_type/3,			% Type, Module, Constructor
	subtype_of/3,			% Type, Module, Super
	type_alias/3.			% Type, Module, Alias

%%	resolve_type(:Type, -QType) is det.
%
%	Resolve module qualifications in a type declaration.

resolve_type(M:T, Type) :-
	var(T), !,
	Type = M:T.
resolve_type(_:(=(Value)), =(Value)) :- !.
resolve_type(_:any, anything) :- !.
resolve_type(M0:not(Type0), not(Type)) :- !,
	resolve_primive_type_arg(M0, Type0, Type).
resolve_type(M0:union(A0,B0), union(A,B)) :- !,
	resolve_primive_type_arg(M0, A0, A),
	resolve_primive_type_arg(M0, B0, B).
resolve_type(M0:intersection(A0,B0), intersection(A,B)) :- !,
	resolve_primive_type_arg(M0, A0, A),
	resolve_primive_type_arg(M0, B0, B).
resolve_type(M0:Type0, M:Type) :-
	qualify_outer_type(M0:Type0, M:Type1),
	(   functor(Type1, F, Arity), Arity>0
	->  Type1 =.. [F|A1],
	    maplist(resolve_type(M0), A1, A),
	    Type  =.. [F|A]
	;   Type = Type1
	).

resolve_primive_type_arg(M, Type0, Type) :-
	functor(Type0, F, Arity),
	Arity > 0, !,
	Type0 =.. [F|A1],
	maplist(resolve_type(M), A1, A),
	Type  =.. [F|A].
resolve_primive_type_arg(M, Type0, Type) :-
	qualify_outer_type(M:Type0, Type).


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

type_expansion((Type ---> Constructor), []) :-
	\+ \+ (numbervars(Type, 0, _), \+ ground(Constructor)), !,
	instantiation_error(Constructor).
type_expansion((TypeSpec ---> Constructor),
	    [ type_decl:current_type(Type, Q, Representation)
	    | TestClauses
	    ]) :- !,
	prolog_load_context(module, M),
	strip_module(M:TypeSpec, Q, Type),
	type_represention(Constructor, Q, Representation),
	(   atom(Type),
	    current_predicate(Q:Type/1)
	->  TestClauses = []
	;   TestClauses = [(TestHead :- TestBody)],
	    test_body(Representation, X, TestBody),
	    extend(Q:Type, X, TestHead)
	).
type_expansion(MAlias = MType,
	    [ type_decl:type_alias(Alias, QA, QT:QType),
	      (AliasHead :- TypeHead)
	    ]) :- !,
	prolog_load_context(module, M),
	strip_module(M:MAlias, QA, Alias),
	strip_module(M:MType, QT, QType),
	extend(QA:Alias, X, AliasHead),
	extend(QT:QType, X, TypeHead).
type_expansion(TypeSpec,
	    [ type_decl:current_type(Type, Q, primitive(Q:Type))
	    ]) :-
	prolog_load_context(module, M),
	strip_module(M:TypeSpec, Q, Type).


%%	type_represention(+Constructor, +Module, -Representation)
%
%	Translate  the  surface  Constructor   representation  into  the
%	internal type representation.
%
%	@tbd	Module resolution is not correct

type_represention((A0;B0), M, union(A,B)) :- !,
	type_repr(A0, M, A),
	type_represention(B0, M, B).
type_represention(A0, M, A) :-
	type_repr(A0, M, A).

type_repr({Type}, M, Q:Type) :- !,
	strip_module(M:Type, Q, Type).
type_repr(Value, _, =(Value)) :-
	atomic(Value), !.
type_repr(A0, M, A) :-
	type_arg(M, A0, A).

type_arg(_, Var, type(Var)) :-			% parametric type: do not qualify
	var(Var), !.
type_arg(_, any, anything) :- !.
type_arg(M, Type, M:Type) :-
	atom(Type), !.
type_arg(M, Compound, compound(N,A,ArgTypes)) :-
	compound(Compound),
	functor(Compound, N, A),
	Compound =.. [N|ArgTypes0],
	maplist(compound_arg(M), ArgTypes0, ArgTypes).

compound_arg(_, Var, type(Var)) :-		% parametric type: do not qualify
	var(Var), !.
compound_arg(_, any, anything) :- !.
compound_arg(M, Type, type(M:Type)).


%%	test_body(+Type, -Body) is det.
%
%	Clause is a semidet  unary  predicate   that  tests  that a term
%	satisfies Type.

test_body(union(C1,C2), X, (B1->true;B2)) :- !,
	test_body(C1, X, B1),
	test_body(C2, X, B2).
test_body(intersection(C1,C2), X, (B1->true;B2)) :- !,
	test_body(C1, X, B1),
	test_body(C2, X, B2).
test_body(not(C0), X, \+(C)) :- !,
	test_body(C0, X, C).
test_body(anything, _, true).
test_body(=(Value), X, (X == Value)).
test_body(type(Type), X, Goal) :-
	(   qcallable(Type)
	->  extend(Type, X, Goal)
	;   Goal = type_test(Type, X)
	).
test_body(compound(Name,Arity,ArgTypes), X, (nonvar(X),X=T2,TArgs)) :-
	functor(T2, Name, Arity),
	T2   =.. [Name|Args],
	maplist(test_body, ArgTypes, Args, TArgList),
	list_to_conj(TArgList, TArgs).

qcallable(_:C) :- !, callable(C).
qcallable(C) :- callable(C).


:- meta_predicate
	type_constraint(:,?).

%%	type_constraint(:Type, +Value) is semidet.
%
%	Create a contraint that limits Value to  be of Type. If Value is
%	ground, this is the  same   type_test(Type,Value).  If  Value is
%	partial with respect  to  Type,   create  constraint(s)  on  the
%	remaining variable(s) that establish the type relation.

type_constraint(Type, Value) :-
	resolve_type(Type, QType),
	qtype_constraint(QType, Value).

qtype_constraint(anything, _) :- !.
qtype_constraint(nothing, _) :- !, fail.
qtype_constraint(Type, Var) :-
	var(Var), !,
	(   get_attr(Var, type, Type2)
	->  (   Type = Type2
	    ->	true
	    ;	normalise_type(intersection(Type, Type2), NewType),
		put_attr(Var, type, NewType)
	    )
	;   put_attr(Var, type, Type)
	).
qtype_constraint(=(Value), Value).
qtype_constraint(primitive(Test), Value) :-
	type_test(Test, Value).
qtype_constraint(compound(N,A,ArgTypes), Value) :-
	compound(Value), !,
	functor(Value, N, A),
	Value =.. [N|Args],
	maplist(qtype_constraint, ArgTypes, Args).
qtype_constraint(union(T1,T2), Value) :-
	(   qtype_constraint(T1, Value)
	;   qtype_constraint(T2, Value)
	).
qtype_constraint(intersection(T1,T2), Value) :-
	qtype_constraint(T1, Value),
	qtype_constraint(T2, Value).
qtype_constraint(not(T1), Value) :-
	\+ qtype_constraint(T1, Value).
qtype_constraint(type(T), Value) :-
	current_type(T, Type),
	qtype_constraint(Type, Value).
qtype_constraint(M:T, Value) :-
	current_type(M:T, Type),
	qtype_constraint(Type, Value).


%%	type_test(:Type, +Value) is semidet.
%
%	True if Value satisfies type.

type_test(_:Any, _) :-
	Any == any, !.
type_test(Type, Value) :-
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
	expand_type(TypeIn, TypeExpanded),
	nnf(TypeExpanded, NNF),
	dnf(NNF, DNF1),
	simplify_conj(DNF1, DNF2),
	simplify_disj(DNF2, TypeOut).

expand_type(type(T), Expanded) :- !,
	current_type(T, Exp0),
	expand_type(Exp0, Expanded).
expand_type(M:T, Expanded) :- !,
	current_type(M:T, Exp0),
	expand_type(Exp0, Expanded).
expand_type(union(A0,B0), union(A,B)) :- !,
	expand_type(A0, A),
	expand_type(B0, B).
expand_type(intersection(A0,B0), intersection(A,B)) :- !,
	expand_type(A0, A),
	expand_type(B0, B).
expand_type(not(A0), not(A)) :- !,
	expand_type(A0, A).
expand_type(T, T).


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

intersection_list(intersection(A,B)) --> !,
	intersection_list(A),
	intersection_list(B).
intersection_list(A) -->
	[A].

list_intersection([One], One) :- !.
list_intersection([H|T], intersection(H,R)) :-
	list_intersection(T, R).


%%	conj(+T1,+T2,-T)
%
%	Simplification rules for intersection of  basic types. Note that
%	we assume that primitive types are  disjoint.

conj(X, X, X).
conj(not(X), X, nothing).
conj(anything, X, X).
conj(nothing, _, nothing).
conj(X, Y, nothing) :-
	disjoint(X,Y).
conj(not(X), Y, Y) :-
	disjoint(X,Y).
conj(=(V), primitive(Test), Type) :-
	(   type_test(Test, V)
	->  Type = =(V)
	;   Type = nothing
	).
conj(=(V), not(primitive(Test)), Type) :-
	(   type_test(Test, V)
	->  Type = nothing
	;   Type = =(V)
	).
conj(primitive(P1), primitive(P2), T) :-
	primitive_intersection(P1, P2, P3),
	T = primitive(P3).
conj(primitive(Test),Type,NewType) :-
	phrase(primitive_values(Type), Values),
	include(Test, Values, ValidValues),
	value_union(ValidValues, NewType).
conj(not(=(_)), primitive(Test), primitive(Test)). % Simplified
conj(compound(N,A,T), primitive(system:compound), compound(N,A,T)).
conj(compound(N,A,AV1), compound(N,A,AV2), compound(N,A,AV)) :-
	maplist(normalise_type, intersection(AV1,AV2), AV).

%%	disjoint(X,Y) is semidet.
%
%	True if X and Y are disjoint types.

disjoint(primitive(X), primitive(Y)) :-
	X \== Y,
	\+ primitive_intersection(X,Y,_),
	\+ primitive_intersection(Y,X,_).
disjoint(compound(_,_,_), primitive(T)) :- T \== compound.

%%	primitive_intersection(P1,P2,P3)
%
%	True if P3 is the primitive intersection between P1 and P2

primitive_intersection(system:integer,	system:code,   system:code).
primitive_intersection(system:atom,	system:char,   system:char).
primitive_intersection(system:compound,	system:option, system:option).

primitive_values(=(X)) -->
	[X].
primitive_values(union(A,B)) -->
	primitive_values(A),
	primitive_values(B).

value_union([], nothing).
value_union([H|T], union(=(H),R)) :-
	value_union(T, R).


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

union_list(union(A,B)) --> !,
	union_list(A),
	union_list(B).
union_list(A) -->
	[A].

list_union([One], One) :- !.
list_union([H|T], union(H,R)) :-
	list_union(T, R).

disj(X, X, X).
disj(anything, _, anything).
disj(nothing, X, X).
disj(intersection(X,_),X,X).
disj(intersection(_,X),X,X).

%%	(type):attr_unify_hook(Type, Val) is semidet.
%
%	Unification hook for the type constraint.

(type):attr_unify_hook(Type, Val) :-
	qtype_constraint(Type, Val).

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
	type_expansion(Type, Clauses).

