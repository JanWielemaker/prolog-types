:- use_module(type_decl).
:- use_module(pred_decl).

:- [test_decl].

:- type system:read_mode ---> read.
:- type system:write_mode ---> write ; append ; update.

:- pred system:open(++any, +read_mode, -input_stream) is det.
:- pred system:open(++any, +write_mode, -output_stream) is det.
:- pred system:read(+input_stream, -any) is det.
:- pred system:write(+output_stream, -any) is det.
:- pred system:close(+stream) is det.


		 /*******************************
		 *	     PlAYGROUND		*
		 *******************************/

:- pred test(++any, -any) is det.

test(library(In), Term) :-
	open(In, read, Stream),
	read(Stream, Term),
	close(Stream).

:- meta_predicate
	check(:).

check(Head) :-
	clause(Head, Body),
	head_signature(Head, _Det),
	check_body(Body, _IsDet).

check_body((A,B), Det) :- !,
	check_body(A, Det),
	check_body(B, Det).
check_body(A, Det) :-
	goal_signature(A, Det).
