Style guide for the standard library
====================================

This is very much a work-in-progress and is not exhaustive.

## File structure

#### Module imports

* All module imports should be at the top of the file immediately after
  the module declaration.

* If the module takes parameters that require imports from other files
  then those imports only may be placed above the module declaration.

* If it is important that certain names only come into scope later in
  the file then the module should still be imported at the top of the
  file but it can be given a shorter name using `as` and then opened
  later on in the file when needed, e.g.
  ```agda
  import Data.List.Relation.Binary.Equality.SetoidEquality as SetoidEq
  ...
  ...
  open SetoidEq
  ```

* The list of module imports should be in alphabetical order.

* When only using a few items from a module, the items should be
  enumerated in the import with `using` in order to make dependencies
  clearer.

#### Indentation

* The contents of a top-level module should have zero indentation.

* Every subsequent nested scope should then indent by 2 spaces.

* `where` blocks should be indented two spaces in and their contents
  should be aligned with the `where`.

* If the type of a term does not fit on one line then the subsequent
  lines of the type should all be aligned with the first character
  of the first line of type, e.g.
  ```agda
  map-cong₂ : ∀ {a b} {A : Set a} {B : Set b} →
                      ∀ {f g : A → B} {xs} →
              All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  ```

* As can be seen in the example above, function arrows at line breaks
  should  always go at the end of the line rather the beginning of the
  next line.

#### Reasoning layout

* The `begin` clause should go on the same line as the rest of the proof.

* Every subsequent combinator `_≡⟨_⟩_` should go on it's own line,
  indented by two spaces.

* The relation sign (e.g. `≡`) for each line should be aligned if possible.

* For example:
  ```agda
  +-comm : Commutative _+_
  +-comm zero    n = sym (+-identityʳ n)
  +-comm (suc m) n = begin
    suc m + n    ≡⟨⟩
    suc (m + n)  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)  ≡⟨ sym (+-suc n m) ⟩
    n + suc m    ∎
  ```

#### Record layout

* The `record` declaration should go on the same line.

* The next line with the first record item should start a single `{` after it.

* Every subsequent item of the record should go on it's own line
  starting with a `;`.

* The final line should end with `}` on it's own.

* For example:
  ```agda
  ≤-isPreorder : IsPreorder _≡_ _≤_
  ≤-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ≤-reflexive
    ; trans         = ≤-trans
    }
  ```

#### Other

* Non-trivial proofs in `private` blocks are generally discouraged.

* `where` blocks are preferred rather than the `let` construction.

* The `with` syntax is preferred over the use of `case` from the `Function`
  module.

## Types

#### Implicit and explicit arguments

* Functions arguments should be implicit if they can "almost always"
  be inferred. If there are common cases where they cannot be inferred
  then they should be left explicit.

* If there are lots of implicit arguments that are common to a collection
  of proofs they should be extracted by using an anonymous module.

* Implicit of type `Level` and `Set` can be generalised using `variable`s.
  At the moment the policy is *not* to generalise over any other types in
  order to minimise the amount of information that users have to keep in
  their head concurrently.

## Naming conventions

* Names should be descriptive - i.e. given the name of a proof and the
  module it lives in then users should be able to make a reasonable
  guess at what it contains.

* Terms from other modules should only be renamed to avoid name clashes,
  otherwise all names should be used as defined.

* Datatype names should be capitalised and function names should be
  lowercase.

#### Variables

* Natural variables are named `m`, `n`, `o`, ... (default `n`)

* Integer varaibles are named `i`, `j`, `k`, ... (default `i`)

* Rational variables are named `p`, `q`, `r`, ... (default `p`)

* When naming proofs, the variables should occur in order, e.g.
  `m≤n+m` rather than `n≤m+n`.

* Collections of elements are usually indicated by appending an `s`
  (e.g. if you are naming your variables `x` and `y` then lists
  should be named `xs` and `ys`).


#### Preconditions and postconditions

* Preconditions should only be included in names of results if
  "important" (mostly judgement call).

* Preconditions of results should be prepended to a description
  of the result by using the symbol `⇒` in names (e.g. `asym⇒antisym`)

* Preconditions and postconditions should be combined using the symbols
  `∨` and `∧` (e.g. `m*n≡0⇒m≡0∨n≡0`)

* Try to avoid the need for bracketing but if necessary use square
  brackets (e.g. `[m∸n]⊓[n∸m]≡0`)

#### Operators and relations

* Operators and relations names should use mixfix notation where
  applicable (e.g. `_+_`, `_<_`)

* Common properties such as those in rings/orders/equivalences etc.
  have defined abbreviations (e.g. commutativity is shortened to `comm`).
  `Data.Nat.Properties` is a good place to look for examples.

* Properties should be by prefixed by the relevant operator/relation
  (e.g. commutativity of `_+_` is named `+-comm`)

* If the relevant unicode characters are available, negated forms of
  relations should be used over the `¬` symbol (e.g. `m+n≮n` should be
  used instead of `¬m+n<n`).

#### Functions and relations over specific datatypes

* When defining a new relation over a datatype
  (e.g. `Data.List.Relation.Binary.Pointwise`)
  it is often common to define how to introduce and eliminate that
  relation over various simple functions (e.g. `map`) over that datatype:
  ```agda
  map⁺ : Pointwise (λ a b → R (f a) (g b)) as bs →
                 Pointwise R (map f as) (map g bs)

  map⁻ : Pointwise R (map f as) (map g bs) →
                 Pointwise (λ a b → R (f a) (g b)) as bs
  ```
  Such elimination and introduction proofs are called the name of the
  function superscripted with either a `+` or `-` accordingly.
