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

:- module(prolog_system_types,
          []).
:- use_module(pred_decl).
:- use_module(type_decl).

% Basic system types. Note that this also   tells  the system that e.g.,
% the predicate atomic/1 exists  and  succeeds   iff  the  argument is a
% atomic.  There are some exceptions.  See comments.

:- type system:atomic.
:- type system:atom       < [system:atomic].
:- type system:module     < [system:atom].      % current_module/1
:- type system:number     < [system:atomic].
:- type system:stream     < [system:atomic].    % is_stream/1
:- type system:db_ref     < [system:atomic].
:- type system:clause_ref < [system:db_ref].
:- type system:record_ref < [system:db_ref].
:- type system:integer    < [system:number].
:- type system:float      < [system:number].
:- type system:thread     < [system:integer,system:atom]. % ???
:- type system:mutex      < [system:integer,system:atom]. % ???

% Derived types

:- type system:boolean < [system:atom] --->
    (   true
    ;   false
    ).

% Option lists of various predicates

:- type system:write_option --->
    (   attributes((ignore;dots;write;portray))
    ;   backquoted_string(system:boolean)
    ;   blobs((write;portray))
    ;   character_escapes(system:boolean)
    ;   ignore_ops(system:boolean)
    ;   max_depth(system:integer)
    ;   module(system:module)
    ;   numbervars(system:boolean)
    ;   partial(system:boolean)
    ;   portray(system:boolean)
    ;   portray_goal(pred(any,list(system:write_option)))
    ;   priority(system:integer)
    ;   quoted(system:boolean)
    ;   spacing((standard;next_argument))
    ).


                 /*******************************
                 *           PREDICATES         *
                 *******************************/

:- pred system:write(@any) is det.
:- pred system:write(+system:stream, @any) is det.
:- pred system:write_term(@any, +list(system:write_option)) is det.
:- pred system:write_term(+system:stream, @any, +list(system:write_option)) is det.

:- pred system:sort(+system:list(X), -system:list(X)) is det.
:- pred system:msort(+system:list(X), -system:list(X)) is det.
:- pred system:keysort(+system:list(system:pair(K,V)), -system:list(system:pair(K,V))) is det.

:- pred system: =(-X,-X) is det.        % ????
:- pred system: =(+X,-X) is det.
:- pred system: =(+X,-X) is det.
:- pred system: =(+any,+any) is semidet.

:- pred system:  ==(?any,?any) is semidet.
:- pred system: =@<(?any,?any) is semidet.
:- pred system: >@=(?any,?any) is semidet.

:- pred system:  is(-number,@evaluable) is det.
:- pred system: =:=(@evaluable,@evaluable) is semidet.
:- pred system: =\=(@evaluable,@evaluable) is semidet.
:- pred system:   <(@evaluable,@evaluable) is semidet.
:- pred system:   >(@evaluable,@evaluable) is semidet.
:- pred system:  =<(@evaluable,@evaluable) is semidet.
:- pred system:  >=(@evaluable,@evaluable) is semidet.

:- pred system:findall(?X, @pred, -list(X)) is det.
:- pred system:setof(?X, @pred, -list(X)) is semidet. % TBD: existential qualification
:- pred system:bagof(?X, @pred, -list(X)) is semidet.


                 /*******************************
                 *          FUNCTIONS           *
                 *******************************/

:- func +(X) -> X.
:- func +(integer,integer) -> integer .
:- func +(number,float) -> float .
:- func +(float,number) -> float .

