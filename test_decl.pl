:- use_module(type_decl).

:- type list --->
	(   []
	;   [any|list]
	).

:- type list(X) --->
	(   []
	;   [X|list(X)]
	).

