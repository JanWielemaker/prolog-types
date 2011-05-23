:- module(signature_decl,
	  [ (pred)/1,			% +Signature
	    op(1150, fx, pred),		% signature declaration
	    op(200, fy, ?),		% argument mode
	    op(200, fy, @)		% argument mode
	  ]).

/** <module> Predicate signatures
*/

%%	pred(+Signature)
%
%	This directive provides a type,   mode and determinism signature
%	for the given Signature.

pred(Signature) :-
	throw(error(context_error(nodirective, pred(Signature)), _)).



