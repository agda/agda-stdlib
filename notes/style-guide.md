Style guide for the standard library
====================================

This is very much a work-in-progress and is not exhaustive.

## Module imports

* All module imports should be at the top of the file immediately after the module declaration.

* When only using a few items from a module, the items should be enumerated in the import with `using`
  in order to make dependencies clearer.

## Indentation

* The top-level contents of a top-level module should have zero indentation. Every subsequent
  level of indentation should use 2 spaces.

* `where` blocks should be indented two spaces in and their contents should be aligned with the `where`.

## Implicit and explicit arguments

* Functions arguments should be implicit if they can "almost always" be inferred. If there are common
  cases where they cannot be inferred then they should be left explicit.

* If there are lots of implicit arguments that are common to a set of proofs they should be
  extracted by using an anonymous module (or possibly the new `variable` keyword in Agda 2.6.0).

## Naming conventions

* Names should be descriptive - i.e. given the name of a proof and the module it lives in
  then users should be able to make a reasonable guess at what it contains.

* Datatype names should be capitalised and function names should be lowercase.

* Collections of elements are usually indicated by appending an `s` (e.g. if you are naming your
  variables `x` and `y` then a lists should be named `xs` and `ys`).

#### Preconditions and postconditions

* Preconditions should only be included in names of results if "important" (mostly judgement call).

* Preconditions of results should be prepended to a description of the result by using the
  symbol `⇒` in names (e.g. `asym⇒antisym`)

* Preconditions and postconditions should be combined using the symbols `∨` and `∧` (e.g. `i*j≡0⇒i≡0∨j≡0`)

* Try to avoid the need for bracketing but if necessary use square brackets (e.g. `[m∸n]⊓[n∸m]≡0`)

#### Operators and relations

* Operators and relations names should use mixfix notation where applicable (e.g. `_+_`, `_<_`)

* Common properties such as those in rings/orders/equivalences etc. have defined abbreviations
  (e.g. commutativity is shortened to `comm`). `Data.Nat.Properties` is a good place to look for examples.

* Properties should be by prefixed by the relevant operator/relation (e.g. commutativity of `_+_` is named `+-comm`)

* If the relevant unicode characters are available, negated forms of relations should be used over
  the `¬` symbol (e.g. `m+n≮n` should be used instead of `¬m+n<n`).

#### Functions and relations over specific datatypes

* When defining a new relation over a datatype (e.g. `Data.List.Relation.Binary.Pointwise`)
  it is often common to define how to introduce and eliminate that relation over various simple functions
  (e.g. `map`) over that datatype:
  ```agda
  map⁺ : Pointwise (λ a b → R (f a) (g b)) as bs → Pointwise R (map f as) (map g bs)
  map⁻ : Pointwise R (map f as) (map g bs) → Pointwise (λ a b → R (f a) (g b)) as bs
  ```
  Such elimination and introduction proofs are called the name of the function superscripted with either
  a `+` or `-` accordingly.

## Other miscellaneous points

* `where` blocks are preferred rather than the `let` construction.

* If a type is split over two lines then the arrow should go at the end of the first line rather than
  the beginning of the second line, i.e.
  ```
  foo : VeryLongType →
                B
  ```
  rather than
  ```
  foo : VeryLongType
                → B
  ```
