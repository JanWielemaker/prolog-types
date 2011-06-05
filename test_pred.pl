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
	read(Stream, Term2).


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
	check(:, -).

%%	check(:Goal, Det) is nondet.
%
%	Check type, mode and determinism for Goal.

check(M:Head, Det) :-
	(   predicate_property(M:Head, imported_from(Q))
	->  true
	;   Q = M
	),
	clause(Q:Head, Body),
	head_signature(Q:Head, _Det),
	check_body(Body, Q, Det).

%%	check_body(+Goal, +Module, -Determinism) is nondet.
%
%	@tbd	Deal with cycles. Something is a cycle if we find the
%		same goal with the same argument types, but I fear it
%		is not that simple.

check_body((A,B), M, Det) :- !,
	check_body(A, M, DetA),
	(   DetA == failure
	->  Det = DetA
	;   check_body(B, M, DetB),
	    det_conj(DetA, DetB, Det)
	).
check_body(!, _, Det) :- !,
	Det = cut.
check_body(TypeTest, M, semidet) :-
	functor(TypeTest, N, A),
	succ(TA, A),
	functor(Type, N, TA),
	current_type(M:Type, _), !,
	arg(A, TypeTest, Var),
	type_constraint(M:Type, Var).
check_body(A, M, Det) :-
	goal_signature(M:A, Det).


det_conj(_,	  cut,	   cut) :- !.
det_conj(cut,	  Det,	   Det) :- !.
det_conj(det,	  det,	   det) :- !.
det_conj(det,	  semidet, semidet) :- !.
det_conj(semidet, det,	   semidet) :- !.
det_conj(_,	  nondet,  nondet) :- !.
det_conj(nondet,  _,	   nondet) :- !.
