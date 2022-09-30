# Adding types to SWI-Prolog

Docs: https://lirias.kuleuven.be/bitstream/123456789/197561/1/shorticlp08.pdf

This is an old playground project for adding typing to Prolog.  I have
copied it to Github to make sure  the code is not lost. The core ideas
of this projects were (and are)

  - Aim at describing as much as possible of normal Prolog practices.
  - Do not try to be exhaustive
  - Do not proof type correctness, but try to proof type errors

To achieve these, we envision the following steps

  - Design a type annotation that is concise, natural and captures
    most from normal Prolog programming practice.
  - Implement a _constraint_ based type annotation, i.e., by adding
    a type to a variable this variable is associated with constraints
    that prevent it to get a value that does not satisfy the type.
  - When two type constraint variables are unified, compute the
    intersection of the types.  If this is empty we have a type
    error.
  - When two disjunctive paths provide type constraints for a variable
    the joined type is the disjunction of the types in these paths.
  - Implement a type checker based on abstract execution using the
    above type constraints.

## What we want from a type declarations

  - Allow exporting types and provide visibility of types silimar to
    predicates and operators.

  - Access predicates:
    - <type>(X) is semidet.
    - type_constraint(:Type, X)

  - A type hierarchy as a multiple-inheritance hierarchy.

  - Interesting challenges:

	type_constraint(atom, X),
	type_constraint(list, X)
		--> X = []

	type_constraint(compound, X),
	type_constraint(list, X)
		--> X = [_|T], type_constraint(list, T).

	- Atomic types: see whether type decl has actual values that
	  match.  Then, replace by eq-constraint?
	- Compound:

### Hindley-Milner types

```
  :- type list --->
	( []
	; [_|list]
	).
  :- type list(X) --->
	( []
	; [X|list]
	).
  :- type boolean --->
	( true
	; false
	).
  :- type write_option --->
	( quoted(boolean)
	; ...
	).
```

#### Type inheritance

```
  :- type boolean < [atom] --->
	( true
	; false
	).
  :- type integer < [number].
  :- type atom < [atomic].
  :- type number < [atomic].
  :- type stream.
```


## We also need modes

  - +
    Input argument.  Satisfies the given type at entry
  - -
    Output argument.  Satisfies the given type at exit
  - ?
    Input/output argument.  Satisfies the given type at exit
  - @ :
    Input argument.  Left unmodified.

# Attributed approach

Attributes:

  - name
  - type
  - instantiated

# License

This code is available under the BSD-2 clause license.