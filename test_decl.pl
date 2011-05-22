:- use_module(type_decl).

:- type system:list --->
	(   []
	;   [any|system:list]
	).

:- type list(X) --->
	(   []
	;   [X|list(X)]
	).

