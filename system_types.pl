:- module(prolog_system_types,
	  []).
:- use_module(type_decl).

% Basic system types

:- type system:atomic.
:- type system:atom	  < [system:atomic].
:- type system:module	  < [system:atom].
:- type system:number	  < [system:atomic].
:- type system:stream	  < [system:atomic].
:- type system:db_ref	  < [system:atomic].
:- type system:clause_ref < [system:db_ref].
:- type system:record_ref < [system:db_ref].
:- type system:integer	  < [system:number].
:- type system:float	  < [system:number].

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
	;   portray_goal(pred(any,list(write_option)))
	;   priority(system:integer)
	;   quoted(system:boolean)
	;   spacing((standard,next_argument))
	).

		 /*******************************
		 *	     PREDICATES		*
		 *******************************/

:- pred system:write(@any) is det.
:- pred system:write(+system:stream, @any) is det.
:- pred system:write_term(@any, +list(system:write_option)) is det.
:- pred system:write_term(+system:stream, @any, +list(system:write_option)) is det.
