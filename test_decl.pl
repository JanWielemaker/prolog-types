:- use_module(type_decl).

system:stream(X)	:- is_stream(X).
system:input_stream(X)	:- is_stream(X), stream_property(X, input).
system:output_stream(X)	:- is_stream(X), stream_property(X, output).
system:list(X)		:- is_list(X).
system:char(X)		:- atom(X), atom_length(X,1).
system:code(X)		:- integer(X), between(-1,0x10ffff,X).
system:option(X)	:- (   X = (Name=_Value) -> atom(Name)
			   ;   compound(X), functor(X, _, 1)
			   ).

% disjoint primitives
:- type system:atom.
:- type system:string.
:- type system:integer.
:- type system:float.
:- type system:compound.
:- type system:input_stream.
:- type system:output_stream.
:- type system:option.

% derived primitives (domain restriction)
:- type system:char.
:- type system:code.

% union system types
:- type system:number ---> {integer} ; {float}.
:- type system:atomic ---> {atom} ; {string} ; {number}.
:- type system:callable ---> {atom} ; {compound}.
:- type system:stream ---> {input_stream} ; {output_stream}.
:- type system:boolean ---> true ; false.

% widely used terms
:- type system:list ---> [] ; [any|list].
:- type system:list(X) ---> [] ; [X|list(X)].

:- type system:pair ---> any-any.
:- type system:pair(X,Y) ---> X-Y.

% widely used list types
:- type system:codes   = list(code).
:- type system:chars   = list(char).
:- type system:options = list(option).

% aliases
:- type system:module_name = atom.


		 /*******************************
		 *    SYSTEM PREDICATE OPTIONS	*
		 *******************************/

:- type system:write_option_attributes ---> ignore ; dots ; write ; portray.
:- type system:write_option_blobs ---> write ; portray.
:- type system:write_option_spacing ---> standard ; next_argument ; portray.

:- type system:write_option --->
      (   attributes(write_option_attributes)
      ;   backquoted_string(boolean)
      ;   blobs(write_option_blobs)
      ;   character_escapes(boolean)
      ;   ignore_ops(boolean)
      ;   max_depth(integer)
      ;   module(module_name)
      ;   numbervars(boolean)
      ;   partial(boolean)
      ;   portray(boolean)
%     ;   portray_goal(pred(any,list(write_option)))
      ;   priority(integer)
      ;   quoted(boolean)
      ;   spacing(write_option_spacing)
      ).
