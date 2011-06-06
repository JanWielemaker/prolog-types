:- use_module(type_decl).
:- use_module(pred_decl).

:- [test_decl].

:- type system:read_mode ---> read.
:- type system:write_mode ---> write ; append ; update.

:- pred system:open(++any, +read_mode, -input_stream) is det.
:- pred system:open(++any, +write_mode, -output_stream) is det.
:- pred system:read(+input_stream, -any) is det.
:- pred system:write(+output_stream, -any) is det.
:- pred system:close(invalidate(stream)) is det.

:- pred system:true  is det.
:- pred system:fail  is failure.
:- pred system:false is failure.

:- pred system:atom_codes(+atom, -codes) is det.
:- pred system:atom_codes(-atom, +codes) is det.
:- pred system:number_codes(+number, -codes) is det.
:- pred system:number_codes(-number, +codes) is det.


		 /*******************************
		 *	     PlAYGROUND		*
		 *******************************/

%:- pred t1(++any, -any) is det.

t1(library(In), Term) :-
	open(In, read, Stream),
	read(Stream, Term),
	close(Stream).

t2(In, Term-Term2) :-
	open(In, read, Stream),
	read(Stream, Term),
	close(Stream),
	read(Stream, Term2).			% error


%:- pred to_codes(+atom, -codes) is det.
%:- pred to_codes(+not(atom), -codes) is failure.

to_codes(In, Out) :-
	atom(In),
	atom_codes(In, Out).

:- pred atomic_codes(+atomic, -codes) is det.

atomic_codes(In, Out) :-
	atom(In), !,
	atom_codes(In, Out).
atomic_codes(In, Out) :-
	number_codes(In, Out).


		 /*******************************
		 *	PROTOTYPE CHECKING	*
		 *******************************/

:- meta_predicate
	check(:, -, -).

%%	check(:Goal, -Annot, Det) is nondet.
%
%	Check type, mode and determinism for Goal.

check(M:Head, Annot, Det) :-
	(   predicate_property(M:Head, imported_from(Q))
	->  true
	;   Q = M
	),
	clause(Q:Head, Body),
	head_signature(Q:Head, _Det),
	check_body(Body, Q, Annot, Det).

check_body(Body, M, Annot, Det) :-
	check_conjunction(Body, M, Annot, Det).


%%	check_conjunction(+Body, +Module, -Annot, -Determinism) is nondet.
%
%	Check a conjunction of goals. Annot  has the same goal structure
%	as the input, and holds  annotations   about  the goals in Body.
%	Each annotation is a list. Elements of the list include.
%
%	  * Determinism of the sub-goal (normal determinism indicators)
%	  * Type error as argtype(ArgN, Var, Expected, Found)
%	  * not_reached for code that cannot be reached

check_conjunction((A,B), M, (CA,CB), Det) :- !,
	check_conjunction(A, M, CA, DetA),
	(   DetA == failure
	->  Det = DetA,
	    CB = [not_reached]
	;   check_conjunction(B, M, CB, DetB),
	    det_conj(DetA, DetB, Det)
	).
check_conjunction(!, _, [cut], Det) :- !,
	Det = cut.
check_conjunction(TypeTest, M, [semidet], Det) :- % type-test
	functor(TypeTest, N, A),
	succ(TA, A),
	functor(Type, N, TA),
	current_type(M:Type, _), !,
	arg(A, TypeTest, Var),
	(   type_constraint(M:Type, Var),
	    Det = det,
	    pred_decl:demand_mode(+, Var)
	;   type_constraint(not(M:Type), Var),
	    Det = failure
	).
check_conjunction(A, M, CA, Det) :-
	goal_signature(M:A, CA, Det).


det_conj(_,	  cut,	   cut) :- !.
det_conj(cut,	  Det,	   Det) :- !.
det_conj(det,	  det,	   det) :- !.
det_conj(det,	  semidet, semidet) :- !.
det_conj(semidet, det,	   semidet) :- !.
det_conj(_,	  nondet,  nondet) :- !.
det_conj(nondet,  _,	   nondet) :- !.
