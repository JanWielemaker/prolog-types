:- use_module(type_decl).

:- type system:atomic.
:- type system:atom.
:- type system:number  < [system:atomic].
:- type system:integer < [system:number].
:- type system:float   < [system:float].

:- type system:list --->
	(   []
	;   [any|system:list]
	).

:- type list(X) --->
	(   []
	;   [X|list(X)]
	).

