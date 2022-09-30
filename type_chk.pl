/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        jan@swi-prolog.org
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2022, SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(type_chk,
          [ check_goal/1
          ]).
:- use_module(type_decl).
:- use_module(pred_decl).

/** <module> The type checker

The type checker is based on attributed variables to track the state of
variables.  It uses several attributes:

        * type
        Reflect the current notion of the type.  Unification can fail
        or get a common subtype.
        * instantiated
        One of =var=, =partial= or =ground=.
        * name
        If available, the name of the variable.  Used for feedback.
*/

:- meta_predicate
    check_goal(:).

check_goal(Goal) :-
    clause(Goal, Body),
    Goal = M:Head,
    check_clause((Head:-Body), M, []).

check_clause((Head :- Body), M, Options) :-
    variable_names(Options),
    head_signature(M:Head, _Det),
    check_body(Body, M).


variable_names(Options) :-
    option(variable_names(Names), Options),
    !,
    maplist(set_var_name, Names).
variable_names(_).

set_var_name(Name=Var) :-
    put_attr(Var, name, Name).

check_body((A,B), M) :-
    !,
    check_body(A, M),
    check_body(B, M).
check_body(Goal, M) :-
    goal_signature(M:Goal, _Det).

