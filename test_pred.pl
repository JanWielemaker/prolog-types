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

% :- pred atomic_codes(+atomic, -codes) is det.

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

%%	error_free_models(+Body, +Module, -Models) is det.
%
%	Models is a list of model(Goal,  M,   Det)  models for Body that
%	contain no errors.

error_free_models(Body, M, Models) :-
	findall(Model, error_free_model(Body, M, Model), Models).

error_free_model(Body, M, model(Body, Anot, Det)) :-
	check_conjunction(Body, M, Anot, Det),
	\+ ( sub_term(Error, Anot),
	     subsumes_term(error(_,_), Error)
	   ).


%%	check_conjunction(+Body, +Module, -Annot, -Determinism) is nondet.
%
%	Check a conjunction of goals. Annot  has the same goal structure
%	as the input, and holds  annotations   about  the goals in Body.
%	Each annotation is a list. Elements of the list include.
%
%	  * Determinism of the sub-goal (normal determinism indicators)
%	  * errors:
%	    - error(type_error(Expected, Found), argument(I))
%	    - error(mode_error(Mode, Found), argument(I))
%	    - error(invalid(Found), argument(I))
%	  * not_reached for code that cannot be reached
%
%	Determinism   qualifies   the   overall   determinism   of   the
%	conjunction.

check_conjunction((A,B), M, (CA,CB), Det) :- !,
	check_conjunction(A, M, CA, DetA),
	(   never(DetA)
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
check_conjunction(once(Goal), M, C, Det) :- !,
	check_conjunction(Goal, M, C, Det0),
	prune_det(Det0, Det).
check_conjunction(call(Goal), M, C, Det) :- !,
	check_conjunction(Goal, M, C, Det0),
	detcut_det(Det0, Det).
check_conjunction((If->Then;_Else), M, (CIf->CThen;CElse), Det) :- !,
	check_conjunction(If, M, CIf, CDet0),
	prune_det(CDet0, CDet),
	(   always(CDet)
	->  check_conjunction(Then, M, CThen, ThenDet),
	    det_conj(CDet, ThenDet, Det),
	    CElse = not_reached
	;   never(CDet)
	).					% TBD: Other cases
check_conjunction((A;B), M, (CA;CB), Det) :- !,
	error_free_models(A, M, AModels),
	error_free_models(B, M, BModels),
	member(model(A, CA, ADet), AModels),
	member(model(B, CB, BDet), BModels),
	det_disj(ADet, BDet, Det).
check_conjunction((If->Then), M, (CIf->CThen), Det) :- !,
	check_conjunction(If, M, CIf, CDet0),
	prune_det(CDet0, CDet),
	(   never(CDet)
	->  Det = CDet,
	    CThen = [not_reached]
	;   check_conjunction(Then, M, CThen, DetThen),
	    det_conj(CDet, DetThen, Det)
	).
check_conjunction(A, M, CA, Det) :-
	goal_signature(M:A, CA, Det),
	Det \== no_signature.			% TBD


%%	det_conj(+D1, +D2, -D) is det.
%
%	Combine  the  determinism  information  from   two  goals  in  a
%	conjunction. This also keeps information   about  pruning by the
%	cut, by keeping track of cuts   and  by determining whether this
%	cut is called always or sometimes.
%
%	@param	D1,D2,D are either a plain determinism or combined det
%		and cut term (Det-Cut). Cut is one of =cut= or
%		=may_cut=.

det_conj(D1, D2, D) :-
	det_table(D1, D2, Df), !,
	D = Df.

det_table(D1-Cut,  D2-_,    D-Cut) :- !,
	det(D1, D2, D).
det_table(D1-Cut,  D2,	    D-Cut) :- !,
	det(D1, D2, D).
det_table(cut,	    D,      D-cut) :- !.
det_table(D1,       D2-Cut, D) :- !,
	det(D1, D2, Df),
	(   Df = _-_
	->  D = Df
	;   always(Df)
	->  D = Df-Cut
	;   D = Df-may_cut
	).
det_table(D1,      D2,      D) :-
	det(D1, D2, D).

det(X,	     X,	      X).
det(det,     cut,     det-cut).
det(multi,   cut,     det-cut).
det(_,	     cut,     det-may_cut).
det(cut,     Det,     Det-cut).

det(det,     semidet, semidet).
det(semidet, det,     semidet).
det(det,     multi,   multi).
det(multi,   det,     multi).
det(_,	     nondet,  nondet).
det(nondet,  _,	      nondet).

always(det).
always(multi).

never(failure).

%%	prune_det(+DetIn, -DetOut)
%
%	Prune as in the if-then-else condition evaluation, once/1, etc.

prune_det(DetCut, Pruned) :-
	detcut_det(DetCut, Det),
	prune(Det, Pruned).

prune(multi, det).
prune(nondet, semidet).
prune(X, X).

detcut_det(D-_, Df) :- !, Df = D.
detcut_det(D, D).

%%	det_disj(D1, D2, D) is det.
%
%	Combine  disjunctive  determinism  indicators.    The  predicate
%	det_disj_table/3   deals   with   the     determinism   problem,
%	disregarding cuts.

det_disj(D-cut, _, D-cut) :- !.		% not that this makes the 2nd unreachable
det_disj(D1-C, DC2, D-C) :- !,
	detcut_det(DC2, D2),
	det_disj_table(D1, D2, D).
det_disj(D1, D2-C2, D-C) :- !,
	(   never(D1)
	->  C = C2
	;   C = may_cut
	),
	det_disj_table(D1, D2, D).
det_disj(D1, D2, D) :-
	det_disj_table(D1, D2, D).

%%	det_disj_table(+DetA, +DetB, --Det)
%
%	Det is the combined determinism of two disjunctive branches.  To
%	validate this table, use:
%
%	  ==
%	  ?- forall((det(X),det(Y)),
%		    (det_disj_table(X,Y,Z),
%		     format('~w ~w ~w~n', [X,Y,Z]))).
%	  ==

det_disj_table(failure,	Det,	 Det).
det_disj_table(Det,	failure, Det).
det_disj_table(det,	_,	 multi).
det_disj_table(_,	det,	 multi).
det_disj_table(multi,	_,	 multi).
det_disj_table(_,	multi,	 multi).
det_disj_table(nondet,	nondet,	 nondet).
det_disj_table(semidet,	_,	 nondet).
det_disj_table(_,	semidet, nondet).

det(failure).
det(det).
det(semidet).
det(nondet).
det(multi).
