:- module(types,
          [
          ]).
:- use_module(type_decl).

/** <module> Type checker


*/

/*
:- pred append(+list(X), ?list(X), -list(X)) is det.
:- pred append(?list(X), ?list(X), -list(X)) is nondet.
*/

head_signature(M:G) :-
    signature(G, M, head, _).

body_signature(M:G, semidet) :-
    current_type(M:G, _Constructor),
    !,
    arg(1, G, Var),
    type(M:G, Var).
body_signature(M:G, Det) :-
    signature(G, M, body, Det).

signature(append(A,B,C), lists, Where, det) :-
    arg_mode_type(A, +, list(X), Where),
    arg_mode_type(B, ?, list(X), Where),
    arg_mode_type(C, -, list(X), Where).

arg_mode_type(Var, Mode, Type, Where) :-
    mode(Mode, Where, Var),
    type(Type, Var).

%!  mode(+Mode, +Where, +Argument) is semidet.
%
%   Mode matching depends on the  location   (head  or  body). If we
%   match the head, Mode specifies  the   expectations  we  can make
%   about Argument. If we match in the body,  we use it to select an
%   appropriate signature.
%
%   Modes:
%
%     | +  | Nonvar at call                              |
%     | ++ | Ground at call                              |
%     | @  | Untouched by predicate                      |
%     | -  | Unknown at call, fully instantiated at exit |

mode(+, head, Var) :-
    !,
    term_variables(Var, Vars),
    maplist(set_instantiated(ground), Vars).
mode(_, head, _) :- !.
mode(+, body, Var) :-
    !,
    get_attr(Var, instantiated, ground).
mode(@, _, _) :- !.
mode(_, body, Var) :-
    put_attr(Var, instantiated, ground).    % For now

set_instantiated(Instantiated, Var) :-
    put_attr(Var, instantiated, Instantiated).


%!  type(+Type, +Argument) is semidet.
%
%   Apply a type to a variable. If  the   value  is given, this is a
%   type-test. If the value  is   partially  instantiated, match the
%   term with the type to determine the   type of the unbound parts.
%   Finally, if Argument is unbound, put a type constraint on it.

type(Type, Argument) :-
    ground(Argument),
    !,
    call(Type, Argument).
type(Type, Argument) :-
    nonvar(Argument),
    !,
    type_constraint(Type, Argument).
type(Type, Var) :-
    get_attr(Var, type, VarType),
    !,
    unify_types(Type, VarType, NewType),
    (   VarType == NewType
    ->  true
    ;   put_attr(Var, type, NewType)
    ).
type(Type, Var) :-
    put_attr(Var, type, Type).

unify_types(Type, Type, Type) :- !.
unify_types(Type1, Type2, Intersect) :-
    subtype_of(Intersect, Type1),
    subtype_of(Intersect, Type2).
