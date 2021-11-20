Version 2.0-dev
===============

The library has been tested using Agda 2.6.2.

Highlights
----------

* A golden testing library in `Test.Golden`. This allows you to run a set
  of tests and make sure their output matches an expected `golden` value.
  The test runner has many options: filtering tests by name, dumping the
  list of failures to a file, timing the runs, coloured output, etc.
  Cf. the comments in `Test.Golden` and the standard library's own tests
  in `tests/` for documentation on how to use the library.

Bug-fixes
---------

* In `System.Exit`, the `ExitFailure` constructor is now carrying an integer
  rather than a natural. The previous binding was incorrectly assuming that
  all exit codes where non-negative.

* In `/-monoˡ-≤` in `Data.Nat.DivMod` the parameter `o` was implicit but not inferrable.
  It has been changed to be explicit.

* In `Function.Definitions` the definitions of `Surjection`, `Inverseˡ`,
  `Inverseʳ` were not being re-exported correctly and therefore had an unsolved
  meta-variable whenever this module was explicitly parameterised. This has
  been fixed.

Non-backwards compatible changes
--------------------------------

#### Removed deprecated names

* All modules and names that were deprecated prior to v1.0 have been removed.

### Improvements to pretty printing and regexes

* In `Text.Pretty`, `Doc` is now a record rather than a type alias. This
  helps Agda reconstruct the `width` parameter when the module is opened
  without it being applied. In particular this allows users to write
  width-generic pretty printers and only pick a width when calling the
  renderer by using this import style:
  ```
  open import Text.Pretty using (Doc; render)
  --                      ^-- no width parameter for Doc & render
  open module Pretty {w} = Text.Pretty w hiding (Doc; render)
  --                 ^-- implicit width parameter for the combinators

  pretty : Doc w
  pretty = ? -- you can use the combinators here and there won't be any
             -- issues related to the fact that `w` cannot be reconstructed
             -- anymore

  main = do
    -- you can now use the same pretty with different widths:
    putStrLn $ render 40 pretty
    putStrLn $ render 80 pretty
  ```

* In `Text.Regex.Search` the `searchND` function finding infix matches has
  been tweaked to make sure the returned solution is a local maximum in terms
  of length. It used to be that we would make the match start as late as
  possible and finish as early as possible. It's now the reverse.

  So `[a-zA-Z]+.agdai?` run on "the path _build/Main.agdai corresponds to"
  will return "Main.agdai" when it used to be happy to just return "n.agda".


### Refactoring of algebraic lattice hierarchy

* In order to improve modularity and consistency with `Relation.Binary.Lattice`, 
  the structures & bundles for `Semilattice`, `Lattice`, `DistributiveLattice`
  & `BooleanAlgebra` have been moved out of the `Algebra` modules and into their
  own hierarchy in `Algebra.Lattice`.

* All submodules, (e.g. `Algebra.Properties.Semilattice` or `Algebra.Morphism.Lattice`)
  have been moved to the corresponding place under `Algebra.Lattice` (e.g.
  `Algebra.Lattice.Properties.Semilattice` or `Algebra.Lattice.Morphism.Lattice`). See
  the `Deprecated modules` section below for full details.

* Changed definition of `IsDistributiveLattice` and `IsBooleanAlgebra` so that they are 
  no longer right-biased which hinders compositionality. More concretely, `IsDistributiveLattice`
  now has fields:
  ```agda
  ∨-distrib-∧ : ∨ DistributesOver ∧
  ∧-distrib-∨ : ∧ DistributesOver ∨
  ```
  instead of
  ```agda
  ∨-distribʳ-∧ : ∨ DistributesOverʳ ∧
  ```
  and `IsBooleanAlgebra` now has fields:
  ```
  ∨-complement : Inverse ⊤ ¬ ∨
  ∧-complement : Inverse ⊥ ¬ ∧
  ```
  instead of:
  ```agda
  ∨-complementʳ : RightInverse ⊤ ¬ ∨
  ∧-complementʳ : RightInverse ⊥ ¬ ∧
  ```

* To allow construction of these structures via their old form, smart constructors
  have been added to a new module `Algebra.Lattice.Structures.Biased`, which are by
  re-exported automatically by `Algebra.Lattice`. For example, if before you wrote:
  ```agda
  ∧-∨-isDistributiveLattice = record
    { isLattice    = ∧-∨-isLattice
    ; ∨-distribʳ-∧ = ∨-distribʳ-∧
    }
  ```
  you can use the smart constructor `isDistributiveLatticeʳʲᵐ` to write:
  ```agda
  ∧-∨-isDistributiveLattice = isDistributiveLatticeʳʲᵐ (record
    { isLattice    = ∧-∨-isLattice
    ; ∨-distribʳ-∧ = ∨-distribʳ-∧
    })
  ```
  without having to prove full distributivity.

* Added new `IsBoundedSemilattice`/`BoundedSemilattice` records.

* Added new aliases `Is(Meet/Join)(Bounded)Semilattice` for `Is(Bounded)Semilattice`
  which can be used to indicate meet/join-ness of the original structures.


#### Proofs of non-zeroness/positivity/negativity as instance arguments

* Many numeric operations in the library require their arguments to be non-zero,
  and various proofs require their arguments to be non-zero/positive/negative etc.
  As discussed on the [mailing list](https://lists.chalmers.se/pipermail/agda/2021/012693.html),
  the previous way of constructing and passing round these proofs was extremely clunky and lead
  to messy and difficult to read code. We have therefore changed every occurrence where we need
  a proof of non-zeroness/positivity/etc. to take it as an irrelevant
  [instance argument](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).
  See the mailing list for a fuller explanation of the motivation and implementation.

* For example, whereas the type signature of division used to be:
  ```
  _/_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
  ```
  it is now:
  ```
  _/_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
  ```
  which means that as long as an instance of `NonZero n` is in scope then you can write
  `m / n` without having to explicitly provide a proof, as instance search will fill it in
  for you. The full list of such operations changed is as follows:
    - In `Data.Nat.DivMod`: `_/_`, `_%_`, `_div_`, `_mod_`
	- In `Data.Nat.Pseudorandom.LCG`: `Generator`
	- In `Data.Integer.DivMod`: `_divℕ_`, `_div_`, `_modℕ_`, `_mod_`
	- In `Data.Rational`: `mkℚ+`, `normalize`, `_/_`, `1/_`
	- In `Data.Rational.Unnormalised`: `_/_`, `1/_`, `_÷_`

* At the moment, there are 4 different ways such instance arguments can be provided,
  listed in order of convenience and clarity:
    1. *Automatic basic instances* - the standard library provides instances based on the constructors of each
	   numeric type in `Data.X.Base`. For example, `Data.Nat.Base` constains an instance of `NonZero (suc n)` for any `n`
	   and `Data.Integer.Base` contains an instance of `NonNegative (+ n)` for any `n`. Consequently,
	   if the argument is of the required form, these instances will always be filled in by instance search
	   automatically, e.g.
	   ```
	   0/n≡0 : 0 / suc n ≡ 0
	   ```
	2. *Take the instance as an argument* - You can provide the instance argument as a parameter to your function
	   and Agda's instance search will automatically use it in the correct place without you having to
	   explicitly pass it, e.g.
	   ```
	   0/n≡0 : .{{_ : NonZero n}} → 0 / n ≡ 0
	   ```
	3. *Define the instance locally* - You can define an instance argument in scope (e.g. in a `where` clause)
	   and Agda's instance search will again find it automatically, e.g.
	   ```
	   instance
	     n≢0 : NonZero n
	     n≢0 = ...

	   0/n≡0 : 0 / n ≡ 0
	   ```
	4. *Pass the instance argument explicitly* - Finally, if all else fails you can pass the
	   instance argument explicitly into the function using `{{ }}`, e.g.
	   ```
	   0/n≡0 : ∀ n (n≢0 : NonZero n) → ((0 / n) {{n≢0}}) ≡ 0
	   ```
	   Suitable constructors for `NonZero`/`Positive` etc. can be found in `Data.X.Base`.

* A full list of proofs that have changed to use instance arguments is available at the end of this file.
  Notable changes to proofs are now discussed below.

* Previously one of the hacks used in proofs was to explicitly refer to everything in the correct form,
  e.g. if the argument `n` had to be non-zero then you would refer to the argument as `suc n` everywhere
  instead of `n`, e.g.
  ```
  n/n≡1 : ∀ n → suc n / suc n ≡ 1
  ```
  This made the proofs extremely difficult to use if your term wasn't in the right form.
  After being updated to use instance arguments instead, the proof above becomes:
  ```
  n/n≡1 : ∀ n {{_ : NonZero n}} → n / n ≡ 1
  ```
  However, note that this means that if you passed in the value `x` to these proofs before, then you
  will now have to pass in `suc x`. The proofs for which the arguments have changed form in this way
  are highlighted in the list at the bottom of the file.

* Finally, the definition of `_≢0` has been removed from `Data.Rational.Unnormalised.Base`
  and the following proofs about it have been removed from `Data.Rational.Unnormalised.Properties`:
  ```
  p≄0⇒∣↥p∣≢0 : ∀ p → p ≠ 0ℚᵘ → ℤ.∣ (↥ p) ∣ ≢0
  ∣↥p∣≢0⇒p≄0 : ∀ p → ℤ.∣ (↥ p) ∣ ≢0 → p ≠ 0ℚᵘ
  ```

### Implementation of division and modulus for `ℤ`

* The previous implementations of `_divℕ_`, `_div_`, `_modℕ_`, `_mod_`
  in `Data.Integer.DivMod` internally converted to the unary `Fin` datatype
  resulting in poor performance. The implementation has been updated to
  use the corresponding operations from `Data.Nat.DivMod` which are
  efficiently implemented using the Haskell backend.

### Strict functions

* The module `Strict` has been deprecated in favour of `Function.Strict`
  and the definitions of strict application, `_$!_` and `_$!′_`, have been
  moved from `Function.Base` to `Function.Strict`.

* The contents of `Function.Strict` is now re-exported by `Function`.

### Other

* The constructors `+0` and `+[1+_]` from `Data.Integer.Base` are no longer
  exported by `Data.Rational.Base`. You will have to open `Data.Integer(.Base)`
  directly to use them.

* The first two arguments of `m≡n⇒m-n≡0` (now `i≡j⇒i-j≡0`) in `Data.Integer.Base`
  have been made implicit.

* The relations `_≤_` `_≥_` `_<_` `_>_` in `Data.Fin.Base` have been
  generalised so they can now relate `Fin` terms with different indices.
  Should be mostly backwards compatible, but very occasionally when proving
  properties about the orderings themselves the second index must be provided
  explicitly.

* The operation `SymClosure` on relations in
  `Relation.Binary.Construct.Closure.Symmetric` has been reimplemented
  as a data type `SymClosure _⟶_ a b` that is parameterized by the
  input relation `_⟶_` (as well as the elements `a` and `b` of the
  domain) so that `_⟶_` can be inferred, which it could not from the
  previous implementation using the sum type `a ⟶ b ⊎ b ⟶ a`.

* In `Algebra.Morphism.Structures`, `IsNearSemiringHomomorphism`,
  `IsSemiringHomomorphism`, and `IsRingHomomorphism` have been redeisgned to
  build up from `IsMonoidHomomorphism`, `IsNearSemiringHomomorphism`, and
  `IsSemiringHomomorphism` respectively, adding a single property at each step.
  This means that they no longer need to have two separate proofs of
  `IsRelHomomorphism`. Similarly, `IsLatticeHomomorphism` is now built as
  `IsRelHomomorphism` along with proofs that `_∧_` and `_∨_` are homorphic.

  Also, `⁻¹-homo` in `IsRingHomomorphism` has been renamed to `-‿homo`.

* Moved definition of `_>>=_` under `Data.Vec.Base` to its submodule `CartesianBind`
  in order to keep another new definition of `_>>=_`, located in `DiagonalBind`
  which is also a submodule of `Data.Vec.Base`.

* The constructors `+0` and `+[1+_]` from `Data.Integer.Base` are no longer 
  exported by `Data.Rational.Base`. You will have to open `Data.Integer(.Base)`
  directly to use them.

Deprecated modules
------------------

### Deprecation of old function hierarchy

* The module `Function.Related` has been deprecated in favour of `Function.Related.Propositional`
  whose code uses the new function hierarchy. This also opens up the possibility of a more
  general `Function.Related.Setoid` at a later date. Several of the names have been changed
  in this process to bring them into line with the camelcase naming convention used
  in the rest of the library:
  ```agda
  reverse-implication ↦ reverseImplication
  reverse-injection   ↦ reverseInjection
  left-inverse        ↦ leftInverse

  Symmetric-kind      ↦ SymmetricKind
  Forward-kind        ↦ ForwardKind
  Backward-kind       ↦ BackwardKind
  Equivalence-kind    ↦ EquivalenceKind
  ```

### Moving `Algebra.Lattice` files

* As discussed above the following files have been moved:
  ```agda
  Algebra.Properties.Semilattice               ↦ Algebra.Lattice.Properties.Semilattice
  Algebra.Properties.Lattice                   ↦ Algebra.Lattice.Properties.Lattice
  Algebra.Properties.DistributiveLattice       ↦ Algebra.Lattice.Properties.DistributiveLattice
  Algebra.Properties.BooleanAlgebra            ↦ Algebra.Lattice.Properties.BooleanAlgebra
  Algebra.Properties.BooleanAlgebra.Expression ↦ Algebra.Lattice.Properties.BooleanAlgebra.Expression
  Algebra.Morphism.LatticeMonomorphism         ↦ Algebra.Lattice.Morphism.LatticeMonomorphism
  ```

Deprecated names
----------------

* In `Data.Integer.Properties` references to variables in names have
  been made consistent so that `m`, `n` always refer to naturals and
  `i` and `j` always refer to integers:
  ```
  n≮n            ↦  i≮i
  ∣n∣≡0⇒n≡0      ↦  ∣i∣≡0⇒i≡0
  ∣-n∣≡∣n∣       ↦  ∣-i∣≡∣i∣
  0≤n⇒+∣n∣≡n     ↦  0≤i⇒+∣i∣≡i
  +∣n∣≡n⇒0≤n     ↦  +∣i∣≡i⇒0≤i
  +∣n∣≡n⊎+∣n∣≡-n ↦  +∣i∣≡i⊎+∣i∣≡-i
  ∣m+n∣≤∣m∣+∣n∣  ↦  ∣i+j∣≤∣i∣+∣j∣
  ∣m-n∣≤∣m∣+∣n∣  ↦  ∣i-j∣≤∣i∣+∣j∣
  signₙ◃∣n∣≡n    ↦  signᵢ◃∣i∣≡i
  ◃-≡            ↦  ◃-cong
  ∣m-n∣≡∣n-m∣    ↦  ∣i-j∣≡∣j-i∣
  m≡n⇒m-n≡0      ↦  i≡j⇒i-j≡0
  m-n≡0⇒m≡n      ↦  i-j≡0⇒i≡j
  m≤n⇒m-n≤0      ↦  i≤j⇒i-j≤0
  m-n≤0⇒m≤n      ↦  i-j≤0⇒i≤j
  m≤n⇒0≤n-m      ↦  i≤j⇒0≤j-i
  0≤n-m⇒m≤n      ↦  0≤i-j⇒j≤i
  n≤1+n          ↦  i≤suc[i]
  n≢1+n          ↦  i≢suc[i]
  m≤pred[n]⇒m<n  ↦  i≤pred[j]⇒i<j
  m<n⇒m≤pred[n]  ↦  i<j⇒i≤pred[j]
  -1*n≡-n        ↦  -1*i≡-i
  m*n≡0⇒m≡0∨n≡0  ↦  i*j≡0⇒i≡0∨j≡0
  ∣m*n∣≡∣m∣*∣n∣  ↦  ∣i*j∣≡∣i∣*∣j∣
  m≤m+n          ↦  i≤i+j
  n≤m+n          ↦  i≤j+i
  m-n≤m          ↦  i≤i-j

  +-pos-monoʳ-≤    ↦  +-monoʳ-≤
  +-neg-monoʳ-≤    ↦  +-monoʳ-≤
  *-monoʳ-≤-pos    ↦  *-monoʳ-≤-nonNeg
  *-monoˡ-≤-pos    ↦  *-monoˡ-≤-nonNeg
  *-monoʳ-≤-neg    ↦  *-monoʳ-≤-nonPos
  *-monoˡ-≤-neg    ↦  *-monoˡ-≤-nonPos
  *-cancelˡ-<-neg  ↦  *-cancelˡ-<-nonPos
  *-cancelʳ-<-neg  ↦  *-cancelʳ-<-nonPos

  ```

* In `Data.Nat.Properties`:
  ```
  suc[pred[n]]≡n  ↦  suc-pred
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```
  ↥[p/q]≡p         ↦  ↥[n/d]≡n
  ↧[p/q]≡q         ↦  ↧[n/d]≡d
  *-monoˡ-≤-pos    ↦  *-monoˡ-≤-nonNeg
  *-monoʳ-≤-pos    ↦  *-monoʳ-≤-nonNeg
  *-monoˡ-≤-neg    ↦  *-monoˡ-≤-nonPos
  *-monoʳ-≤-neg    ↦  *-monoʳ-≤-nonPos
  *-cancelˡ-<-pos  ↦  *-cancelˡ-<-nonNeg
  *-cancelʳ-<-pos  ↦  *-cancelʳ-<-nonNeg
  ```

* In `Data.Rational.Properties`:
  ```
  *-monoʳ-≤-neg    ↦  *-monoʳ-≤-nonPos
  *-monoˡ-≤-neg    ↦  *-monoˡ-≤-nonPos
  *-monoʳ-≤-pos    ↦  *-monoʳ-≤-nonNeg
  *-monoˡ-≤-pos    ↦  *-monoˡ-≤-nonNeg
  *-cancelˡ-<-pos  ↦  *-cancelˡ-<-nonNeg
  *-cancelʳ-<-pos  ↦  *-cancelʳ-<-nonNeg
  *-cancelˡ-<-neg  ↦  *-cancelˡ-<-nonPos
  *-cancelʳ-<-neg  ↦  *-cancelʳ-<-nonPos
  ```

* In `Data.List.Properties`:
  ```agda
  zipWith-identityˡ  ↦  zipWith-zeroˡ
  zipWith-identityʳ  ↦  zipWith-zeroʳ
  ```

* In `Function.Construct.Composition`:
  ```
  _∘-⟶_   ↦   _⟶-∘_
  _∘-↣_   ↦   _↣-∘_
  _∘-↠_   ↦   _↠-∘_
  _∘-⤖_  ↦   _⤖-∘_
  _∘-⇔_   ↦   _⇔-∘_
  _∘-↩_   ↦   _↩-∘_
  _∘-↪_   ↦   _↪-∘_
  _∘-↔_   ↦   _↔-∘_
  ```

  * In `Function.Construct.Identity`:
  ```
  id-⟶   ↦   ⟶-id
  id-↣   ↦   ↣-id
  id-↠   ↦   ↠-id
  id-⤖  ↦   ⤖-id
  id-⇔   ↦   ⇔-id
  id-↩   ↦   ↩-id
  id-↪   ↦   ↪-id
  id-↔   ↦   ↔-id
  ```

* In `Function.Construct.Symmetry`:
  ```
  sym-⤖   ↦   ⤖-sym
  sym-⇔   ↦   ⇔-sym
  sym-↩   ↦   ↩-sym
  sym-↪   ↦   ↪-sym
  sym-↔   ↦   ↔-sym
  ```

* In `Data.Fin.Base`:
two new, hopefully more memorable, names `↑ˡ` `↑ʳ` for the 'left', resp. 'right' injection of a Fin m into a 'larger' type, `Fin (m + n)`, resp. `Fin (n + m)`, with argument order to reflect the position of the Fin m argument.
  ```
  inject+   ↦   flip _↑ˡ_
  raise     ↦   _↑ʳ_
  ```

* In `Data.Fin.Properties`:
  ```
  toℕ-raise       ↦ toℕ-↑ʳ
  toℕ-inject+ n i ↦ sym (toℕ-↑ˡ i n)
  splitAt-inject+ m n i ↦ splitAt-↑ˡ m i n
  splitAt-raise ↦ splitAt-↑ʳ
  Fin0↔⊥        ↦ 0↔⊥
  ```

* In `Data.Vec.Properties`:
  ```
  []≔-++-inject+       ↦ []≔-++-↑ˡ
  ```
  Additionally, `[]≔-++-↑ʳ`, by analogy.

* In `Foreign.Haskell.Either` and `Foreign.Haskell.Pair`:
  ```
  toForeign   ↦ Foreign.Haskell.Coerce.coerce
  fromForeign ↦ Foreign.Haskell.Coerce.coerce
  ```


New modules
-----------

* Morphisms between module-like algebraic structures:
  ```
  Algebra.Module.Morphism.Construct.Composition
  Algebra.Module.Morphism.Construct.Identity
  Algebra.Module.Morphism.Definitions
  Algebra.Module.Morphism.Structures
  ```

* Identity morphisms and composition of morphisms between algebraic structures:
  ```
  Algebra.Morphism.Construct.Composition
  Algebra.Morphism.Construct.Identity
  ```

* A small library for function arguments with default values:
  ```
  Data.Default
  ```

* A small library for a non-empty fresh list:
  ```
  Data.List.Fresh.NonEmpty
  ```

* Show module for unnormalised rationals:
  ```
  Data.Rational.Unnormalised.Show
  ```

* Properties of bijections:
  ```
  Function.Consequences
  Function.Properties.Bijection
  Function.Properties.RightInverse
  Function.Properties.Surjection
  ```

* In order to improve modularity, the contents of `Relation.Binary.Lattice` has been 
  split out into the standard:
  ```
  Relation.Binary.Lattice.Definitions
  Relation.Binary.Lattice.Structures
  Relation.Binary.Lattice.Bundles
  ```
  All contents is re-exported by `Relation.Binary.Lattice` as before.

* Both versions of equality on predications are equivalences
  ```
  Relation.Unary.Relation.Binary.Equality
  ```

* Polymorphic verstions of some unary relations
  ```
  Relation.Unary.Polymorphic
  ```

* Various system types and primitives:
  ```
  System.Clock.Primitive
  System.Clock
  System.Console.ANSI
  System.Directory.Primitive
  System.Directory
  System.FilePath.Posix.Primitive
  System.FilePath.Posix
  System.Process.Primitive
  System.Process
  ```

* A golden testing library with test pools, an options parser, a runner:
  ```
  Test.Golden
  ```

* New interfaces for using Haskell datatypes:
  ```
  Foreign.Haskell.List.NonEmpty
  ```

Other minor changes
-------------------

* The module `Algebra` now publicly re-exports the contents of
  `Algebra.Structures.Biased`.

* Added new definitions to `Algebra.Bundles`:
  ```agda
  record UnitalMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Quasigroup  c ℓ : Set (suc (c ⊔ ℓ))
  record Loop c ℓ : Set (suc (c ⊔ ℓ))
  ```
  and the existing record `Lattice` now provides
  ```agda
  ∨-commutativeSemigroup : CommutativeSemigroup c ℓ
  ∧-commutativeSemigroup : CommutativeSemigroup c ℓ
  ```
  and their corresponding algebraic subbundles.

* Added new proofs to `Algebra.Consequences.Setoid`:
  ```agda
  comm+idˡ⇒id              : Commutative _•_ → LeftIdentity  e _•_ → Identity e _•_
  comm+idʳ⇒id              : Commutative _•_ → RightIdentity e _•_ → Identity e _•_
  comm+zeˡ⇒ze              : Commutative _•_ → LeftZero      e _•_ → Zero     e _•_
  comm+zeʳ⇒ze              : Commutative _•_ → RightZero     e _•_ → Zero     e _•_
  comm+invˡ⇒inv            : Commutative _•_ → LeftInverse  e _⁻¹ _•_ → Inverse e _⁻¹ _•_
  comm+invʳ⇒inv            : Commutative _•_ → RightInverse e _⁻¹ _•_ → Inverse e _⁻¹ _•_
  comm+distrˡ⇒distr        : Commutative _•_ → _•_ DistributesOverˡ _◦_ → _•_ DistributesOver _◦_
  comm+distrʳ⇒distr        : Commutative _•_ → _•_ DistributesOverʳ _◦_ → _•_ DistributesOver _◦_
  distrib+absorbs⇒distribˡ : Associative _•_ → Commutative _◦_ → _•_ Absorbs _◦_ → _◦_ Absorbs _•_ → _◦_ DistributesOver _•_ → _•_ DistributesOverˡ _◦_
  ```

* Added new functions to `Algebra.Construct.DirectProduct`:
  ```agda
  rawSemiring : RawSemiring a ℓ₁ → RawSemiring b ℓ₂ → RawSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  rawRing : RawRing a ℓ₁ → RawRing b ℓ₂ → RawRing (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero a ℓ₁ →
                                    SemiringWithoutAnnihilatingZero b ℓ₂ →
                                    SemiringWithoutAnnihilatingZero (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  semiring : Semiring a ℓ₁ → Semiring b ℓ₂ → Semiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  commutativeSemiring : CommutativeSemiring a ℓ₁ → CommutativeSemiring b ℓ₂ →
                        CommutativeSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  ring : Ring a ℓ₁ → Ring b ℓ₂ → Ring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  commutativeRing : CommutativeRing a ℓ₁ → CommutativeRing b ℓ₂ →
                    CommutativeRing (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
 ```

* Added new definitions to `Algebra.Structures`:
  ```agda
  record IsUnitalMagma (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  record IsQuasigroup  (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  record IsLoop (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  ```
  and the existing record `IsLattice` now provides
  ```
  ∨-isCommutativeSemigroup : IsCommutativeSemigroup ∨
  ∧-isCommutativeSemigroup : IsCommutativeSemigroup ∧
  ```
  and their corresponding algebraic substructures.

* Added new functions in `Data.Fin.Base`:
  ```
  finToFun  : Fin (n ^ m) → (Fin m → Fin n)
  funToFin  : (Fin m → Fin n) → Fin (n ^ m)
  quotient  : Fin (n * k) → Fin n
  remainder : Fin (n * k) → Fin k
  ```

* Added new proofs and `Inverse` bundles in `Data.Fin.Properties`:
  ```
  1↔⊤                : Fin 1 ↔ ⊤
  ↑ˡ-injective       : i ↑ˡ n ≡ j ↑ˡ n → i ≡ j
  ↑ʳ-injective       : n ↑ʳ i ≡ n ↑ʳ j → i ≡ j
  finTofun-funToFin  : funToFin ∘ finToFun ≗ id
  funTofin-funToFun  : finToFun (funToFin f) ≗ f
  ^↔→                : Extensionality _ _ → Fin (n ^ m) ↔ (Fin m → Fin n)
  ```

* Added new proofs in `Data.Integer.Properties`:
  ```agda
  sign-cong′ : s₁ ◃ n₁ ≡ s₂ ◃ n₂ → s₁ ≡ s₂ ⊎ (n₁ ≡ 0 × n₂ ≡ 0)
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  n+1+m≢m   : n + suc m ≢ m
  m*n≡0⇒m≡0 : .{{_ : NonZero n}} → m * n ≡ 0 → m ≡ 0
  ```

* Added new proofs in `Data.Nat.DivMod`:
  ```agda
  m%n≤n : .{{_ : NonZero n}} → m % n ≤ n
  ```

* Added new rounding functions in `Data.Rational.Base`:
  ```agda
  floor ceiling truncate round ⌊_⌋ ⌈_⌉ [_] : ℚ → ℤ
  fracPart : ℚ → ℚ
  ```

* Added new definitions and proofs in `Data.Rational.Properties`:
  ```agda
  +-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
  +-*-rawSemiring : RawSemiring 0ℓ 0ℓ
  toℚᵘ-isNearSemiringHomomorphism-+-* : IsNearSemiringHomomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
  toℚᵘ-isNearSemiringMonomorphism-+-* : IsNearSemiringMonomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
  toℚᵘ-isSemiringHomomorphism-+-* : IsSemiringHomomorphism +-*-rawSemiring ℚᵘ.+-*-rawSemiring toℚᵘ
  toℚᵘ-isSemiringMonomorphism-+-* : IsSemiringMonomorphism +-*-rawSemiring ℚᵘ.+-*-rawSemiring toℚᵘ
  ```

* Added new rounding functions in `Data.Rational.Unnormalised.Base`:
  ```agda
  floor ceiling truncate round ⌊_⌋ ⌈_⌉ [_] : ℚᵘ → ℤ
  fracPart : ℚᵘ → ℚᵘ
  ```

* Added new definitions in `Data.Rational.Unnormalised.Properties`:
  ```agda
  +-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
  +-*-rawSemiring : RawSemiring 0ℓ 0ℓ
  ```

* Added new proof to `Data.Product.Properties`:
  ```agda
  map-cong : f ≗ g → h ≗ i → map f h ≗ map g i
  ```

* Added new definitions to `Data.Product.Properties` and
  `Function.Related.TypeIsomorphisms` for convenience:
  ```
  Σ-≡,≡→≡ : (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) → subst B p (proj₂ p₁) ≡ proj₂ p₂) → p₁ ≡ p₂
  Σ-≡,≡←≡ : p₁ ≡ p₂ → (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) → subst B p (proj₂ p₁) ≡ proj₂ p₂)
  ×-≡,≡→≡ : (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂) → p₁ ≡ p₂
  ×-≡,≡←≡ : p₁ ≡ p₂ → (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂)
  ```

* Added new proofs in `Data.String.Properties`:
  ```
  ≤-isDecTotalOrder-≈ : IsDecTotalOrder _≈_ _≤_
  ≤-decTotalOrder-≈   :  DecTotalOrder _ _ _
  ```

* Added new proofs in `Data.Sum.Properties`:
  ```
  map-assocˡ : (f : A → C) (g : B → D) (h : C → F) →
    map (map f g) h ∘ assocˡ ≗ assocˡ ∘ map f (map g h)
  map-assocʳ : (f : A → C) (g : B → D) (h : C → F) →
    map f (map g h) ∘ assocʳ ≗ assocʳ ∘ map (map f g) h
  ```

* Added new definitions in `Data.Vec.Base`:
  ```agda
  diagonal : ∀ {n} → Vec (Vec A n) n → Vec A n
  DiagonalBind._>>=_ : ∀ {n} → Vec A n → (A → Vec B n) → Vec B n
  ```

* Added new instance in `Data.Vec.Categorical`:
  ```agda
  monad : RawMonad (λ (A : Set a) → Vec A n)
  ```

* Added new proofs in `Data.Vec.Properties`:
  ```agda
  map-const : ∀ {n} (xs : Vec A n) (x : B) → map {n = n} (const x) xs ≡ replicate x
  map-⊛ : ∀ {n} (f : A → B → C) (g : A → B) (xs : Vec A n) → (map f xs ⊛ map g xs) ≡ map (f ˢ g) xs
  ⊛-is->>= : ∀ {n} (fs : Vec (A → B) n) (xs : Vec A n) → (fs ⊛ xs) ≡ (fs DiagonalBind.>>= flip map xs)
  transpose-replicate : ∀ {m n} (xs : Vec A m) → transpose (replicate {n = n} xs) ≡ map replicate xs
  []≔-++-↑ʳ : ∀ {m n y} (xs : Vec A m) (ys : Vec A n) i → (xs ++ ys) [ m ↑ʳ i ]≔ y ≡ xs ++ (ys [ i ]≔ y)
  ```

* Added new proofs in `Function.Construct.Symmetry`:
  ```
  bijective     : Bijective ≈₁ ≈₂ f → Symmetric ≈₂ → Transitive ≈₂ → Congruent ≈₁ ≈₂ f → Bijective ≈₂ ≈₁ f⁻¹
  isBijection   : IsBijection ≈₁ ≈₂ f → Congruent ≈₂ ≈₁ f⁻¹ → IsBijection ≈₂ ≈₁ f⁻¹
  isBijection-≡ : IsBijection ≈₁ _≡_ f → IsBijection _≡_ ≈₁ f⁻¹
  bijection     : Bijection R S → Congruent IB.Eq₂._≈_ IB.Eq₁._≈_ f⁻¹ → Bijection S R
  bijection-≡   : Bijection R (setoid B) → Bijection (setoid B) R
  sym-⤖        : A ⤖ B → B ⤖ A
  ```

* Added new operations in `Function.Strict`:
  ```
  _!|>_  : (a : A) → (∀ a → B a) → B a
  _!|>′_ : A → (A → B) → B
  ```

* Added new definition to the `Surjection` module in `Function.Related.Surjection`:
  ```
  f⁻ = proj₁ ∘ surjective
  ```

* Added new operations in `IO`:
  ```
  Colist.forM  : Colist A → (A → IO B) → IO (Colist B)
  Colist.forM′ : Colist A → (A → IO B) → IO ⊤

  List.forM  : List A → (A → IO B) → IO (List B)
  List.forM′ : List A → (A → IO B) → IO ⊤
  ```

* Added new operations in `IO.Base`:
  ```
  lift! : IO A → IO (Lift b A)
  _<$_  : B → IO A → IO B
  _=<<_ : (A → IO B) → IO A → IO B
  _<<_  : IO B → IO A → IO B
  lift′ : Prim.IO ⊤ → IO {a} ⊤

  when   : Bool → IO {a} ⊤ → IO ⊤
  unless : Bool → IO {a} ⊤ → IO ⊤

  whenJust  : Maybe A → (A → IO {a} ⊤) → IO ⊤
  untilJust : IO (Maybe A) → IO A
  ```

* Added new operations in `Relation.Binary.Construct.Closure.Equivalence`:
  ```
  fold   : IsEquivalence _∼_ → _⟶_ ⇒ _∼_ → EqClosure _⟶_ ⇒ _∼_
  gfold  : IsEquivalence _∼_ → _⟶_ =[ f ]⇒ _∼_ → EqClosure _⟶_ =[ f ]⇒ _∼_
  return : _⟶_ ⇒ EqClosure _⟶_
  join   : EqClosure (EqClosure _⟶_) ⇒ EqClosure _⟶_
  _⋆     : _⟶₁_ ⇒ EqClosure _⟶₂_ → EqClosure _⟶₁_ ⇒ EqClosure _⟶₂_
  ```

* Added new operations in `Relation.Binary.Construct.Closure.Symmetric`:
  ```
  fold   : Symmetric _∼_ → _⟶_ ⇒ _∼_ → SymClosure _⟶_ ⇒ _∼_
  gfold  : Symmetric _∼_ → _⟶_ =[ f ]⇒ _∼_ → SymClosure _⟶_ =[ f ]⇒ _∼_
  return : _⟶_ ⇒ SymClosure _⟶_
  join   : SymClosure (SymClosure _⟶_) ⇒ SymClosure _⟶_
  _⋆     : _⟶₁_ ⇒ SymClosure _⟶₂_ → SymClosure _⟶₁_ ⇒ SymClosure _⟶₂_
  ```

* Added new proofs in `Relation.Binary.PropositionalEquality.Properties`:
  ```
  subst-application′ : subst Q eq (f x p) ≡ f y (subst P eq p)
  sym-cong : sym (cong f p) ≡ cong f (sym p)
  ```

* Added new proofs in `Relation.Binary.HeterogeneousEquality`:
  ```
  subst₂-removable : subst₂ _∼_ eq₁ eq₂ p ≅ p
  ```

* Equality of predicates
  ```
  _≐_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  _≐′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  ```

* Added new operations in `System.Exit`:
  ```
  isSuccess : ExitCode → Bool
  isFailure : ExitCode → Bool
  ```

* Added new functions in `Data.List.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All P ∪ Any Q ]
  ```

* Added new functions in `Data.List.Fresh.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All {R = R} P ∪ Any Q ]
  ```

* Added new functions in `Data.Vec.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All P ∪ Any Q ]
  ```

* Added new operations in
  `Relation.Binary.PropositionalEquality.Properties`:
  ```
  J : {A : Set a} {x : A} (B : (y : A) → x ≡ y → Set b)
      {y : A} (p : x ≡ y) → B x refl → B y p
  dcong : ∀ {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y}
        → (p : x ≡ y) → subst B p (f x) ≡ f y
  dcong₂ : ∀ {A : Set a} {B : A → Set b} {C : Set c}
           (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
         → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
         → f x₁ y₁ ≡ f x₂ y₂
  dsubst₂ : ∀ {A : Set a} {B : A → Set b} (C : (x : A) → B x → Set c)
            {x₁ x₂ y₁ y₂} (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
          → C x₁ y₁ → C x₂ y₂
  ddcong₂ : ∀ {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
           (f : (x : A) (y : B x) → C x y) {x₁ x₂ y₁ y₂}
           (p : x₁ ≡ x₂) (q : subst B p y₁ ≡ y₂)
         → dsubst₂ C p q (f x₁ y₁) ≡ f x₂ y₂
  ```

* Added vector associativity proof to 
  `Data/Vec/Relation/Binary/Equality/Setoid.agda`:
  ```
  ++-assoc : ∀ {n m k} (xs : Vec A n) → (ys : Vec A m) 
      → (zs : Vec A k) → (xs ++ ys) ++ zs ≋ xs ++ (ys ++ zs)
  ```

NonZero/Positive/Negative changes
---------------------------------

This is a full list of proofs that have changed form to use irrelevant instance arguments:

* In `Data.Nat.Properties`:
  ```
  *-cancelʳ-≡ : ∀ m n {o} → m * suc o ≡ n * suc o → m ≡ n
  *-cancelˡ-≡ : ∀ {m n} o → suc o * m ≡ suc o * n → m ≡ n
  *-cancelʳ-≤ : ∀ m n o → m * suc o ≤ n * suc o → m ≤ n
  *-cancelˡ-≤ : ∀ {m n} o → suc o * m ≤ suc o * n → m ≤ n
  *-monoˡ-<   : ∀ n → (_* suc n) Preserves _<_ ⟶ _<_
  *-monoʳ-<   : ∀ n → (suc n *_) Preserves _<_ ⟶ _<_

  m≤m*n          : ∀ m {n} → 0 < n → m ≤ m * n
  m≤n*m          : ∀ m {n} → 0 < n → m ≤ n * m
  m<m*n          : ∀ {m n} → 0 < m → 1 < n → m < m * n
  suc[pred[n]]≡n : ∀ {n} → n ≢ 0 → suc (pred n) ≡ n
  ```

* In `Data.Nat.Coprimality`:
  ```
  Bézout-coprime : ∀ {i j d} → Bézout.Identity (suc d) (i * suc d) (j * suc d) → Coprime i j
  ```

* In `Data.Nat.Divisibility`
  ```agda
  m%n≡0⇒n∣m : ∀ m n → m % suc n ≡ 0 → suc n ∣ m
  n∣m⇒m%n≡0 : ∀ m n → suc n ∣ m → m % suc n ≡ 0
  m%n≡0⇔n∣m : ∀ m n → m % suc n ≡ 0 ⇔ suc n ∣ m
  ∣⇒≤       : ∀ {m n} → m ∣ suc n → m ≤ suc n
  >⇒∤        : ∀ {m n} → m > suc n → m ∤ suc n
  *-cancelˡ-∣ : ∀ {i j} k → suc k * i ∣ suc k * j → i ∣ j
  ```

* In `Data.Nat.DivMod`:
  ```
  m≡m%n+[m/n]*n : ∀ m n → m ≡ m % suc n + (m / suc n) * suc n
  m%n≡m∸m/n*n   : ∀ m n → m % suc n ≡ m ∸ (m / suc n) * suc n
  n%n≡0         : ∀ n → suc n % suc n ≡ 0
  m%n%n≡m%n     : ∀ m n → m % suc n % suc n ≡ m % suc n
  [m+n]%n≡m%n   : ∀ m n → (m + suc n) % suc n ≡ m % suc n
  [m+kn]%n≡m%n  : ∀ m k n → (m + k * (suc n)) % suc n ≡ m % suc n
  m*n%n≡0       : ∀ m n → (m * suc n) % suc n ≡ 0
  m%n<n         : ∀ m n → m % suc n < suc n
  m%n≤m         : ∀ m n → m % suc n ≤ m
  m≤n⇒m%n≡m     : ∀ {m n} → m ≤ n → m % suc n ≡ m

  m/n<m         : ∀ m n {≢0} → m ≥ 1 → n ≥ 2 → (m / n) {≢0} < m
  ```

* In `Data.Nat.GCD`
  ```
  GCD-* : ∀ {m n d c} → GCD (m * suc c) (n * suc c) (d * suc c) → GCD m n d
  gcd[m,n]≤n : ∀ m n → gcd m (suc n) ≤ suc n
  ```

* In `Data.Integer.Properties`:
  ```
  sign-◃    : ∀ s n → sign (s ◃ suc n) ≡ s
  sign-cong : ∀ {s₁ s₂ n₁ n₂} → s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
  -◃<+◃     : ∀ m n → Sign.- ◃ (suc m) < Sign.+ ◃ n
  m⊖1+n<m   : ∀ m n → m ⊖ suc n < + m

  *-cancelʳ-≡     : ∀ i j k → k ≢ + 0 → i * k ≡ j * k → i ≡ j
  *-cancelˡ-≡     : ∀ i j k → i ≢ + 0 → i * j ≡ i * k → j ≡ k
  *-cancelʳ-≤-pos : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n

  ≤-steps     : ∀ n → i ≤ j → i ≤ + n + j
  ≤-steps-neg : ∀ n → i ≤ j → i - + n ≤ j
  n≤m+n       : ∀ n → i ≤ + n + i
  m≤m+n       : ∀ n → i ≤ i + + n
  m-n≤m       : ∀ i n → i - + n ≤ i

  *-cancelʳ-≤-pos    : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
  *-cancelˡ-≤-pos    : ∀ m j k → + suc m * j ≤ + suc m * k → j ≤ k
  *-cancelˡ-≤-neg    : ∀ m {j k} → -[1+ m ] * j ≤ -[1+ m ] * k → j ≥ k
  *-cancelʳ-≤-neg    : ∀ {n o} m → n * -[1+ m ] ≤ o * -[1+ m ] → n ≥ o
  *-cancelˡ-<-nonNeg : ∀ n → + n * i < + n * j → i < j
  *-cancelʳ-<-nonNeg : ∀ n → i * + n < j * + n → i < j
  *-monoʳ-≤-nonNeg   : ∀ n → (_* + n) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonNeg   : ∀ n → (+ n *_) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonPos   : ∀ i → NonPositive i → (i *_) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonPos   : ∀ i → NonPositive i → (_* i) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos      : ∀ n → (+[1+ n ] *_) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos      : ∀ n → (_* +[1+ n ]) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg      : ∀ n → (-[1+ n ] *_) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg      : ∀ n → (_* -[1+ n ]) Preserves _<_ ⟶ _>_
  *-cancelˡ-<-nonPos : ∀ n → NonPositive n → n * i < n * j → i > j
  *-cancelʳ-<-nonPos : ∀ n → NonPositive n → i * n < j * n → i > j

  *-distribˡ-⊓-nonNeg : ∀ m j k → + m * (j ⊓ k) ≡ (+ m * j) ⊓ (+ m * k)
  *-distribʳ-⊓-nonNeg : ∀ m j k → (j ⊓ k) * + m ≡ (j * + m) ⊓ (k * + m)
  *-distribˡ-⊓-nonPos : ∀ i → NonPositive i → ∀ j k → i * (j ⊓ k) ≡ (i * j) ⊔ (i * k)
  *-distribʳ-⊓-nonPos : ∀ i → NonPositive i → ∀ j k → (j ⊓ k) * i ≡ (j * i) ⊔ (k * i)
  *-distribˡ-⊔-nonNeg : ∀ m j k → + m * (j ⊔ k) ≡ (+ m * j) ⊔ (+ m * k)
  *-distribʳ-⊔-nonNeg : ∀ m j k → (j ⊔ k) * + m ≡ (j * + m) ⊔ (k * + m)
  *-distribˡ-⊔-nonPos : ∀ i → NonPositive i → ∀ j k → i * (j ⊔ k) ≡ (i * j) ⊓ (i * k)
  *-distribʳ-⊔-nonPos : ∀ i → NonPositive i → ∀ j k → (j ⊔ k) * i ≡ (j * i) ⊓ (k * i)
  ```

* In `Data.Integer.Divisibility`:
  ```
  *-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
  *-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
  ```

* In `Data.Integer.Divisibility.Signed`:
  ```
  *-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
  *-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```agda
  ≤-steps : ∀ {p q r} → NonNegative r → p ≤ q → p ≤ r + q
  p≤p+q   : ∀ {p q} → NonNegative q → p ≤ p + q
  p≤q+p   : ∀ {p} → NonNegative p → ∀ {q} → q ≤ p + q

  *-cancelʳ-≤-pos    : ∀ {r} → Positive r → ∀ {p q} → p * r ≤ q * r → p ≤ q
  *-cancelˡ-≤-pos    : ∀ {r} → Positive r → ∀ {p q} → r * p ≤ r * q → p ≤ q
  *-cancelʳ-≤-neg    : ∀ r → Negative r → ∀ {p q} → p * r ≤ q * r → q ≤ p
  *-cancelˡ-≤-neg    : ∀ r → Negative r → ∀ {p q} → r * p ≤ r * q → q ≤ p
  *-cancelˡ-<-nonNeg : ∀ {r} → NonNegative r → ∀ {p q} → r * p < r * q → p < q
  *-cancelʳ-<-nonNeg : ∀ {r} → NonNegative r → ∀ {p q} → p * r < q * r → p < q
  *-cancelˡ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → r * p < r * q → q < p
  *-cancelʳ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → p * r < q * r → q < p
  *-monoˡ-≤-nonNeg   : ∀ {r} → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-nonNeg   : ∀ {r} → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonPos   : ∀ r → NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonPos   : ∀ r → NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos      : ∀ {r} → Positive r → (_* r) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos      : ∀ {r} → Positive r → (r *_) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg      : ∀ r → Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg      : ∀ r → Negative r → (r *_) Preserves _<_ ⟶ _>_

  pos⇒1/pos : ∀ p (p>0 : Positive p) → Positive ((1/ p) {{pos⇒≢0 p p>0}})
  neg⇒1/neg : ∀ p (p<0 : Negative p) → Negative ((1/ p) {{neg⇒≢0 p p<0}})

  *-distribʳ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊓ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊓ r) ≃ (p * q) ⊓ (p * r)
  *-distribˡ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊔ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊔ r) * p ≃ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊔ r) ≃ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊔ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊓ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊓ r) * p ≃ (q * p) ⊔ (r * p)
  ```

* In `Data.Rational.Properties`:
  ```
  *-cancelʳ-≤-pos    : ∀ r → Positive r → ∀ {p q} → p * r ≤ q * r → p ≤ q
  *-cancelˡ-≤-pos    : ∀ r → Positive r → ∀ {p q} → r * p ≤ r * q → p ≤ q
  *-cancelʳ-≤-neg    : ∀ r → Negative r → ∀ {p q} → p * r ≤ q * r → p ≥ q
  *-cancelˡ-≤-neg    : ∀ r → Negative r → ∀ {p q} → r * p ≤ r * q → p ≥ q
  *-cancelˡ-<-nonNeg : ∀ r → NonNegative r → ∀ {p q} → r * p < r * q → p < q
  *-cancelʳ-<-nonNeg : ∀ r → NonNegative r → ∀ {p q} → p * r < q * r → p < q
  *-cancelˡ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → r * p < r * q → p > q
  *-cancelʳ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → p * r < q * r → p > q
  *-monoʳ-≤-nonNeg   : ∀ r → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonNeg   : ∀ r → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-nonPos   : ∀ r → NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoˡ-≤-nonPos   : ∀ r → NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos      : ∀ r → Positive r → (_* r) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos      : ∀ r → Positive r → (r *_) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg      : ∀ r → Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg      : ∀ r → Negative r → (r *_) Preserves _<_ ⟶ _>_

  *-distribˡ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊓ (p * r)
  *-distribʳ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊓ (r * p)
  *-distribˡ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊔ (r * p)

  pos⇒1/pos : ∀ p (p>0 : Positive p) → Positive ((1/ p) {{pos⇒≢0 p p>0}})
  neg⇒1/neg : ∀ p (p<0 : Negative p) → Negative ((1/ p) {{neg⇒≢0 p p<0}})
  1/pos⇒pos : ∀ p .{{_ : NonZero p}} → (1/p : Positive (1/ p)) → Positive p
  1/neg⇒neg : ∀ p .{{_ : NonZero p}} → (1/p : Negative (1/ p)) → Negative p
  ```
