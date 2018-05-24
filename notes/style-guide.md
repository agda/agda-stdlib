Style guide for the standard library
====================================

This is very much a work-in-progress.

### General

* Names should be descriptive - i.e. given the name of a proof and the module it lives in
  then users should be able to make a reasonable guess at what it contains.

### Preconditions and postconditions

* Preconditions should only be included in names of results if "important" (mostly judgement call).

* Preconditions of results should be prepended to a description of the result by using the
  symbol `⇒` in names (e.g. `asym⇒antisym`)
  
* Preconditions and postconditions should be combined using the symbols `∨` and `∧` (e.g. `i*j≡0⇒i≡0∨j≡0`)

* Try to avoid the need for bracketing but if necessary use square brackets (e.g. `[m∸n]⊓[n∸m]≡0`)

### Operators and relations

* Operators and relations should be defined using the misfix notation (e.g. `_+_`, `_<_`)

* Common properties such as those in rings/orders/equivalences etc. have defined abbreviations 
  (e.g. commutativity is shortened to `comm`). `Data.Nat.Properties` is a good place to look for examples.

* Properties should be by prefixed by the relevant operator/relation (e.g. commutativity of `_+_` is named `+-comm`)

* If the relevant unicode characters are available, negated forms of relations should be used over 
  the `¬` symbol (e.g. `m+n≮n` should be used instead of `¬m+n<n`).
