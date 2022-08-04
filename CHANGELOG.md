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

* A new tactic `cong!` available from `Tactic.Cong` which automatically
  infers the argument to `cong` for you via anti-unification.

* Improved the `solve` tactic in `Tactic.RingSolver` to work in a much
  wider range of situations.

- Added `⌊log₂_⌋` and `⌈log₂_⌉` on Natural Numbers.

Bug-fixes
---------

* In `System.Exit`, the `ExitFailure` constructor is now carrying an integer
  rather than a natural. The previous binding was incorrectly assuming that
  all exit codes where non-negative.

* In `/-monoˡ-≤` in `Data.Nat.DivMod` the parameter `o` was implicit but not inferrable.
  It has been changed to be explicit.

* In `+-distrib-/-∣ʳ` in `Data.Nat.DivMod` the parameter `m` was implicit but not inferrable,
  while `n` is explicit but inferrable.  They have been changed.

* In `Function.Definitions` the definitions of `Surjection`, `Inverseˡ`,
  `Inverseʳ` were not being re-exported correctly and therefore had an unsolved
  meta-variable whenever this module was explicitly parameterised. This has
  been fixed.

* Add module `Algebra.Module` that re-exports the contents of
  `Algebra.Module.(Definitions/Structures/Bundles)`

* In `Algebra.Definitions.RawSemiring` the record `prime` add `p∤1 : p ∤ 1#` to the field.

* In `Data.List.Relation.Ternary.Appending.Setoid` we re-export specialised versions of
  the constructors using the setoid's carrier set. Prior to that, the constructor were
  re-exported in their full generality which would lead to unsolved meta variables at
  their use sites.

Non-backwards compatible changes
--------------------------------

#### Removed deprecated names

* All modules and names that were deprecated in v1.2 and before have been removed.

#### Moved `Codata` modules to `Codata.Sized`

* Due to the change in Agda 2.6.2 where sized types are no longer compatible
  with the `--safe` flag, it has become clear that a third variant of codata
  will be needed using coinductive records. Therefore all existing modules in
  `Codata` which used sized types have been moved inside a new folder named
  `Sized`, e.g. `Codata.Stream` has become `Codata.Sized.Stream`.

#### Moved `Category` modules to `Effect`

* As observed by Wen Kokke in Issue #1636, it no longer really makes sense
  to group the modules which correspond to the variety of concepts of
  (effectful) type constructor arising in functional programming (esp. in haskell)
  such as `Monad`, `Applicative`, `Functor`, etc, under `Category.*`, as this
  obstructs the importing of the `agda-categories` development into the Standard Library,
  and moreover needlessly restricts the applicability of categorical concepts to this
  (highly specific) mode of use. Correspondingly, modules grouped under `*.Categorical.*`
  which exploited these structures for effectful programming have been renamed `*.Effectful`.

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

#### Function hierarchy

* The switch to the new function hierarchy is complete and the following definitions
  now use the new definitions instead of the old ones:
  * `Data.Fin.Properties`
    * `∀-cons-⇔`
    * `⊎⇔∃`
  * `Data.Fin.Subset.Properties`
    * `out⊆-⇔`
    * `in⊆in-⇔`
    * `out⊂in-⇔`
    * `out⊂out-⇔`
    * `in⊂in-⇔`
    * `x∈⁅y⁆⇔x≡y`
    * `∩⇔×`
    * `∪⇔⊎`
    * `∃-Subset-[]-⇔`
    * `∃-Subset-∷-⇔`
  * `Data.List.Countdown`
    * `empty`
  * `Data.List.Fresh.Relation.Unary.Any`
    * `⊎⇔Any`
  * `Data.List.Relation.Binary.Lex`
    * `[]<[]-⇔`
    * `∷<∷-⇔`
  * `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`
    * `∷⁻¹`
    * `∷ʳ⁻¹`
    * `Sublist-[x]-bijection`
  * `Data.List.Relation.Binary.Sublist.Setoid.Properties`
    * `∷⁻¹`
    * `∷ʳ⁻¹`
    * `[x]⊆xs⤖x∈xs`
  * `Data.Maybe.Relation.Binary.Connected`
    * `just-equivalence`
  * `Data.Maybe.Relation.Binary.Pointwise`
    * `just-equivalence`
  * `Data.Maybe.Relation.Unary.All`
    * `just-equivalence`
  * `Data.Maybe.Relation.Unary.Any`
    * `just-equivalence`
  * `Data.Nat.Divisibility`
    * `m%n≡0⇔n∣m`
  * `Data.Nat.Properties`
    * `eq?`
  * `Data.Vec.Relation.Binary.Lex.Core`
    * `P⇔[]<[]`
    * `∷<∷-⇔`
  * `Data.Vec.Relation.Binary.Pointwise.Extensional`
    * `equivalent`
    * `Pointwise-≡↔≡`
  * `Data.Vec.Relation.Binary.Pointwise.Inductive`
    * `Pointwise-≡↔≡`
  * `Relation.Binary.Construct.Closure.Reflexive.Properties`
    * `⊎⇔Refl`
  * `Relation.Binary.Construct.Closure.Transitive`
    * `equivalent`
  * `Relation.Nullary.Decidable`
    * `map`

* The names of the fields in the records of the new hierarchy have been
  changed from `f`, `g`, `cong₁`, `cong₂` to `to`, `from`, `to-cong`, `from-cong`.

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

### Change in reduction behaviour of rationals

* Currently arithmetic expressions involving rationals (both normalised and 
  unnormalised) undergo disastorous exponential normalisation. For example, 
  `p + q` would often be normalised by Agda to 
  `(↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) / (↧ₙ p ℕ.* ↧ₙ q)`. While the normalised form
  of `p + q + r + s + t + u + v` would be ~700 lines long. This behaviour
  often chokes both type-checking and the display of the expressions in the IDE.

* To avoid this expansion and make non-trivial reasoning about rationals actually feasible:
  1. the records `ℚᵘ` and `ℚ` have both had the `no-eta-equality` flag enabled
  2. definition of arithmetic operations have trivial pattern matching added to
     prevent them reducing, e.g.
     ```agda
     p + q = (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) / (↧ₙ p ℕ.* ↧ₙ q)
     ```
     has been changed to
     ```
     p@record{} + q@record{} = (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) / (↧ₙ p ℕ.* ↧ₙ q)
     ```

* As a consequence of this, some proofs that relied on this reduction behaviour
  or on eta-equality may no longer go through. There are several ways to fix this:
  1. The principled way is to not rely on this reduction behaviour in the first place. 
	 The `Properties` files for rational numbers have been greatly expanded in `v1.7` 
	 and `v2.0`, and we believe most proofs should be able to be built up from existing
	 proofs contained within these files.
  2. Alternatively, annotating any rational arguments to a proof with either
	 `@record{}` or `@(mkℚ _ _ _)` should restore the old reduction behaviour for any
	 terms involving those parameters.
  3. Finally, if the above approaches are not viable then you may be forced to explicitly
	 use `cong` combined with a lemma that proves the old reduction behaviour.

### Change in the definition of `Prime`

* The definition of `Prime` in `Data.Nat.Primality` was:
  ```agda
  Prime 0             = ⊥
  Prime 1             = ⊥
  Prime (suc (suc n)) = (i : Fin n) → 2 + toℕ i ∤ 2 + n
  ```
  which was very hard to reason about as not only did it involve conversion
  to and from the `Fin` type, it also required that the divisor was of the form
  `2 + toℕ i`, which has exactly the same problem as the `suc n` hack described
  above used for non-zeroness.

* To make it easier to use, reason about and read, the definition has been
  changed to:
  ```agda
  Prime 0 = ⊥
  Prime 1 = ⊥
  Prime n = ∀ {d} → 2 ≤ d → d < n → d ∤ n
  ```

### Renaming of `Reflection` modules

* Under the `Reflection` module, there were various impending name clashes
  between the core AST as exposed by Agda and the annotated AST defined in
  the library.

* While the content of the modules remain the same, the modules themselves
  have therefore been renamed as follows:
  ```
  Reflection.Annotated              ↦ Reflection.AnnotatedAST
  Reflection.Annotated.Free         ↦ Reflection.AnnotatedAST.Free

  Reflection.Abstraction            ↦ Reflection.AST.Abstraction
  Reflection.Argument               ↦ Reflection.AST.Argument
  Reflection.Argument.Information   ↦ Reflection.AST.Argument.Information
  Reflection.Argument.Quantity      ↦ Reflection.AST.Argument.Quantity
  Reflection.Argument.Relevance     ↦ Reflection.AST.Argument.Relevance
  Reflection.Argument.Modality      ↦ Reflection.AST.Argument.Modality
  Reflection.Argument.Visibility    ↦ Reflection.AST.Argument.Visibility
  Reflection.DeBruijn               ↦ Reflection.AST.DeBruijn
  Reflection.Definition             ↦ Reflection.AST.Definition
  Reflection.Instances              ↦ Reflection.AST.Instances
  Reflection.Literal                ↦ Reflection.AST.Literal
  Reflection.Meta                   ↦ Reflection.AST.Meta
  Reflection.Name                   ↦ Reflection.AST.Name
  Reflection.Pattern                ↦ Reflection.AST.Pattern
  Reflection.Show                   ↦ Reflection.AST.Show
  Reflection.Traversal              ↦ Reflection.AST.Traversal
  Reflection.Universe               ↦ Reflection.AST.Universe

  Reflection.TypeChecking.Monad             ↦ Reflection.TCM
  Reflection.TypeChecking.Monad.Categorical ↦ Reflection.TCM.Categorical
  Reflection.TypeChecking.Monad.Format      ↦ Reflection.TCM.Format
  Reflection.TypeChecking.Monad.Syntax      ↦ Reflection.TCM.Instances
  Reflection.TypeChecking.Monad.Instances   ↦ Reflection.TCM.Syntax
  ```

* A new module `Reflection.AST` that re-exports the contents of the
  submodules has been addeed.

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

### Changes to ring structures

* Several ring-like structures now have the multiplicative structure defined by
  its laws rather than as a substructure, to avoid repeated proofs that the
  underlying relation is an equivalence. These are:
  * `IsNearSemiring`
  * `IsSemiringWithoutOne`
  * `IsSemiringWithoutAnnihilatingZero`
  * `IsRing`
* To aid with migration, structures matching the old style ones have been added
  to `Algebra.Structures.Biased`, with conversionFunctions:
  * `IsNearSemiring*` and `isNearSemiring*`
  * `IsSemiringWithoutOne*` and `isSemiringWithoutOne*`
  * `IsSemiringWithoutAnnihilatingZero*` and `isSemiringWithoutAnnihilatingZero*`
  * `IsRing*` and `isRing*`

### Proof-irrelevant empty type

* The definition of ⊥ has been changed to
  ```agda
  private
    data Empty : Set where

  ⊥ : Set
  ⊥ = Irrelevant Empty
  ```
  in order to make ⊥ proof irrelevant. Any two proofs of `⊥` or of a negated
  statements are now *judgementally* equal to each other.

* Consequently we have modified the following definitions:
  + In `Relation.Nullary.Decidable.Core`, the type of `dec-no` has changed
    ```agda
    dec-no : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
      ↦ dec-no : (p? : Dec P) (¬p : ¬ P) → p? ≡ no ¬p
    ```
  + In `Relation.Binary.PropositionalEquality`, the type of `≢-≟-identity` has changed
    ```agda
    ≢-≟-identity : x ≢ y → ∃ λ ¬eq → x ≟ y ≡ no ¬eq
      ↦ ≢-≟-identity : (x≢y : x ≢ y) → x ≟ y ≡ no x≢y
    ```

### Other

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

* The functions `split`, `flatten` and `flatten-split` have been removed from
  `Data.List.NonEmpty`. In their place `groupSeqs` and `ungroupSeqs`
  have been added to `Data.List.NonEmpty.Base` which morally perform the same
  operations but without computing the accompanying proofs. The proofs can be
  found in `Data.List.NonEmpty.Properties` under the names `groupSeqs-groups`
  and `ungroupSeqs` and `groupSeqs`.

* The constructors `+0` and `+[1+_]` from `Data.Integer.Base` are no longer
  exported by `Data.Rational.Base`. You will have to open `Data.Integer(.Base)`
  directly to use them.

* The types of the proofs `pos⇒1/pos`/`1/pos⇒pos` and `neg⇒1/neg`/`1/neg⇒neg` in
  `Data.Rational(.Unnormalised).Properties` have been switched, as the previous
  naming scheme didn't correctly generalise to e.g. `pos+pos⇒pos`. For example
  the types of `pos⇒1/pos`/`1/pos⇒pos` were:
  ```
  pos⇒1/pos : ∀ p .{{_ : NonZero p}} .{{Positive (1/ p)}} → Positive p
  1/pos⇒pos : ∀ p .{{_ : Positive p}} → Positive (1/ p)
  ```
  but are now:
  ```
  pos⇒1/pos : ∀ p .{{_ : Positive p}} → Positive (1/ p)
  1/pos⇒pos : ∀ p .{{_ : NonZero p}} .{{Positive (1/ p)}} → Positive p
  ```
* `Opₗ` and `Opᵣ` have moved from `Algebra.Core` to `Algebra.Module.Core`.

* In `Data.Nat.GeneralisedArithmetic`, the `s` and `z` arguments to the following
  functions have been made explicit:
  * `fold-+`
  * `fold-k`
  * `fold-*`
  * `fold-pull`

* In `Data.Fin.Properties`:
  + the `i` argument to `opposite-suc` has been made explicit;
  + `pigeonhole` has been strengthened: wlog, we return a proof that
    `i < j` rather than a mere `i ≢ j`.

* In `Codata.Guarded.Stream` the following functions have been modified to have simpler definitions:
  * `cycle`
  * `interleave⁺`
  * `cantor`
  Furthermore, the direction of interleaving of `cantor` has changed. Precisely, suppose `pair` is the cantor pairing function, then `lookup (pair i j) (cantor xss)` according to the old definition corresponds to `lookup (pair j i) (cantor xss)` according to the new definition. For a concrete example see the one included at the end of the module.

Major improvements
------------------

### Improvements to ring solver tactic

* The ring solver tactic has been greatly improved. In particular:
  1. When the solver is used for concrete ring types, e.g. ℤ, the equality can now use
	 all the ring operations defined natively for that type, rather than having
	 to use the operations defined in `AlmostCommutativeRing`. For example
	 previously you could not use `Data.Integer.Base._*_` but instead had to
	 use `AlmostCommutativeRing._*_`.
  2. The solver now supports use of the subtraction operator `_-_` whenever
     it is defined immediately in terms of `_+_` and `-_`. This is the case for
	 `Data.Integer` and `Data.Rational`.

### Moved `_%_` and `_/_` operators to `Data.Nat.Base`

* Previously the division and modulus operators were defined in `Data.Nat.DivMod`
  which in turn meant that using them required importing `Data.Nat.Properties`
  which is a very heavy dependency.

* To fix this, these operators have been moved to `Data.Nat.Base`. The properties
  for them still live in `Data.Nat.DivMod` (which also publicly re-exports them
  to provide backwards compatability).

* Beneficieries of this change include `Data.Rational.Unnormalised.Base` whose
  dependencies are now significantly smaller.

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

### Moving `Relation.Binary.Properties.XLattice` files

* The following files have been moved:
  ```agda
  Relation.Binary.Properties.BoundedJoinSemilattice.agda  ↦ Relation.Binary.Lattice.Properties.BoundedJoinSemilattice.agda
  Relation.Binary.Properties.BoundedLattice.agda          ↦ Relation.Binary.Lattice.Properties.BoundedLattice.agda
  Relation.Binary.Properties.BoundedMeetSemilattice.agda  ↦ Relation.Binary.Lattice.Properties.BoundedMeetSemilattice.agda
  Relation.Binary.Properties.DistributiveLattice.agda     ↦ Relation.Binary.Lattice.Properties.DistributiveLattice.agda
  Relation.Binary.Properties.JoinSemilattice.agda         ↦ Relation.Binary.Lattice.Properties.JoinSemilattice.agda
  Relation.Binary.Properties.Lattice.agda                 ↦ Relation.Binary.Lattice.Properties.Lattice.agda
  Relation.Binary.Properties.MeetSemilattice.agda         ↦ Relation.Binary.Lattice.Properties.MeetSemilattice.agda
  ```

### Deprecation of `Data.Nat.Properties.Core`

* The module `Data.Nat.Properties.Core` has been deprecated, and its one entry moved to `Data.Nat.Properties`

### Moving `Algebra.Module.Morphism.Linear.Properties` to `Algebra.Module.Morphism.Properties`

Deprecated names
----------------

* In `Data.Fin.Base`: two new, hopefully more memorable, names `↑ˡ` `↑ʳ`
  for the 'left', resp. 'right' injection of a Fin m into a 'larger' type,
  `Fin (m + n)`, resp. `Fin (n + m)`, with argument order to reflect the
  position of the `Fin m` argument.
  ```
  inject+  ↦  flip _↑ˡ_
  raise    ↦  _↑ʳ_
  ```

* In `Data.Fin.Properties`:
  ```
  toℕ-raise        ↦ toℕ-↑ʳ
  toℕ-inject+      ↦ toℕ-↑ˡ
  splitAt-inject+  ↦ splitAt-↑ˡ m i n
  splitAt-raise    ↦ splitAt-↑ʳ
  Fin0↔⊥           ↦ 0↔⊥
  eq?              ↦ inj⇒≟
  ```

* In `Data.Fin.Permutation.Components`:
  ```
  reverse            ↦ Data.Fin.Base.opposite
  reverse-prop       ↦ Data.Fin.Properties.opposite-prop
  reverse-involutive ↦ Data.Fin.Properties.opposite-involutive
  reverse-suc        ↦ Data.Fin.Properties.opposite-suc
  ```

* In `Data.Integer.DivMod` the operator names have been renamed to
  be consistent with those in `Data.Nat.DivMod`:
  ```
  _divℕ_  ↦ _/ℕ_
  _div_   ↦ _/_
  _modℕ_  ↦ _%ℕ_
  _mod_   ↦ _%_
  ```

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

  ^-semigroup-morphism ↦ ^-isMagmaHomomorphism
  ^-monoid-morphism    ↦ ^-isMonoidHomomorphism
  ```

* In `Data.List.Properties`:
  ```agda
  zipWith-identityˡ  ↦  zipWith-zeroˡ
  zipWith-identityʳ  ↦  zipWith-zeroʳ
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

  positive⇒nonNegative  ↦ pos⇒nonNeg
  negative⇒nonPositive  ↦ neg⇒nonPos
  negative<positive     ↦ neg<pos
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

  negative<positive     ↦ neg<pos
  ```

* In `Data.Vec.Properties`:
  ```
  []≔-++-inject+  ↦ []≔-++-↑ˡ
  []≔-++-raise    ↦ []≔-++-↑ʳ
  idIsFold        ↦ id-is-foldr
  sum-++-commute  ↦ sum-++
  ```
  and the type of the proof `zipWith-comm` has been generalised from:
  ```
  zipWith-comm : ∀ {f : A → A → B} (comm : ∀ x y → f x y ≡ f y x) (xs ys : Vec A n) → zipWith f xs ys ≡ zipWith f ys xs
  ```
  to
  ```
  zipWith-comm : ∀ {f : A → B → C} {g : B → A → C}  (comm : ∀ x y → f x y ≡ g y x) (xs : Vec A n) ys → zipWith f xs ys ≡ zipWith g ys xs
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

* In `Foreign.Haskell.Either` and `Foreign.Haskell.Pair`:
  ```
  toForeign   ↦ Foreign.Haskell.Coerce.coerce
  fromForeign ↦ Foreign.Haskell.Coerce.coerce
  ```

* In `Relation.Binary.Properties.Preorder`:
  ```
  invIsPreorder ↦ converse-isPreorder
  invPreorder   ↦ converse-preorder
  ```

### Renamed Data.Erased to Data.Irrelevant

* This fixes the fact we had picked the wrong name originally. The erased modality
  corresponds to @0 whereas the irrelevance one corresponds to `.`.

New modules
-----------

* Algebraic structures when freely adding an identity element:
```
  Algebra.Construct.Add.Identity
```

* Operations for module-like algebraic structures:
  ```
  Algebra.Module.Core
  ```

* Constructive algebraic structures with apartness relations:
  ```
  Algebra.Apartness
  Algebra.Apartness.Bundles
  Algebra.Apartness.Structures
  Algebra.Apartness.Properties.CommutativeHeytingAlgebra
  Relation.Binary.Properties.ApartnessRelation
  ```

* Algebraic structures obtained by flipping their binary operations:
  ```
  Algebra.Construct.Flip.Op
  ```

* Morphisms between module-like algebraic structures:
  ```
  Algebra.Module.Morphism.Construct.Composition
  Algebra.Module.Morphism.Construct.Identity
  Algebra.Module.Morphism.Definitions
  Algebra.Module.Morphism.Structures  
  Algebra.Module.Properties
  ```

* Identity morphisms and composition of morphisms between algebraic structures:
  ```
  Algebra.Morphism.Construct.Composition
  Algebra.Morphism.Construct.Identity
  ```

* Ordered algebraic structures (pomonoids, posemigroups, etc.)
  ```
  Algebra.Ordered
  Algebra.Ordered.Bundles
  Algebra.Ordered.Structures
  ```

* 'Optimised' tail-recursive exponentiation properties:
  ```
  Algebra.Properties.Semiring.Exp.TailRecursiveOptimised
  ```

* A definition of infinite streams using coinductive records:
  ```
  Codata.Guarded.Stream
  Codata.Guarded.Stream.Properties
  Codata.Guarded.Stream.Relation.Binary.Pointwise
  Codata.Guarded.Stream.Relation.Unary.All
  Codata.Guarded.Stream.Relation.Unary.Any
  ```

* A small library for function arguments with default values:
  ```
  Data.Default
  ```

* A small library for a non-empty fresh list:
  ```
  Data.List.Fresh.NonEmpty
  ```

* Combinations and permutations for ℕ.
  ```
  Data.Nat.Combinatorics
  Data.Nat.Combinatorics.Base
  Data.Nat.Combinatorics.Spec
  ```

* Reflection utilities for some specific types:
  ```
  Data.List.Reflection
  Data.Vec.Reflection
  ```

* The `All` predicate over non-empty lists:
  ```
  Data.List.NonEmpty.Relation.Unary.All
  ```

* A small library for heterogenous equational reasoning on vectors:
  ```
  Data.Vec.Properties.Heterogeneous
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

* Algebraic properties of `_∩_` and `_∪_` for predicates
  ```
  Relation.Unary.Algebra
  ```

* Both versions of equality on predications are equivalences
  ```
  Relation.Unary.Relation.Binary.Equality
  ```

* The subset relations on predicates define an order
  ```
  Relation.Unary.Relation.Binary.Subset
  ```

* Polymorphic versions of some unary relations and their properties
  ```
  Relation.Unary.Polymorphic
  Relation.Unary.Polymorphic.Properties
  ```

* Alpha equality over reflected terms
  ```
  Reflection.AST.AlphaEquality
  ```

* `cong!` tactic for deriving arguments to `cong`
  ```
  Tactic.Cong
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
* Added new module `Algebra.Properties.RingWithoutOne`:
  ```
  -‿distribˡ-* : ∀ x y → - (x * y) ≈ - x * y
  -‿distribʳ-* : ∀ x y → - (x * y) ≈ x * - y
  ```
* An implementation of M-types with `--guardedness` flag:
  ```
  Codata.Guarded.M
  ```

* Port of `Linked` to `Vec`:
  ```
  Data.Vec.Relation.Unary.Linked
  Data.Vec.Relation.Unary.Linked.Properties
  ```
* Added Logarithm base 2 on Natural Numbers:
  ```
  Data.Nat.Logarithm.Core
  Data.Nat.Logarithm
  ```

* Proofs of some axioms of linearity:
  ```
  Algebra.Module.Morphism.ModuleHomomorphism
  Algebra.Module.Properties
  ```

* Useful bundles of morphisms between `Module` and friends:
  ```
  Algebra.Module.Morphism.Bundles
  ```

* Support for abstract vector spaces:
  ```
  Algebra.Linear
  Algebra.Linear.Structures
  Algebra.Linear.Bundles
  Algebra.Linear.Properties.VectorSpace
  ```

* Extensional equivalence
  ```
  Function.Relation.Binary.Equality
  ```

Other minor changes
-------------------

* Added new proof to `Data.Maybe.Properties`
```agda
    <∣>-idem : Idempotent _<∣>_
```

* The module `Algebra` now publicly re-exports the contents of
  `Algebra.Structures.Biased`.

* Added new definitions to `Algebra.Bundles`:
  ```agda
  record UnitalMagma c ℓ : Set (suc (c ⊔ ℓ))
  record InvertibleMagma c ℓ : Set (suc (c ⊔ ℓ))
  record InvertibleUnitalMagma c ℓ : Set (suc (c ⊔ ℓ))
  record RawQuasiGroup c ℓ : Set (suc (c ⊔ ℓ))
  record Quasigroup c ℓ : Set (suc (c ⊔ ℓ))
  record RawLoop  c ℓ : Set (suc (c ⊔ ℓ))
  record Loop  c ℓ : Set (suc (c ⊔ ℓ))
  record RingWithoutOne c ℓ : Set (suc (c ⊔ ℓ))
  record KleeneAlgebra c ℓ : Set (suc (c ⊔ ℓ))
  record RawRingWithoutOne c ℓ : Set (suc (c ⊔ ℓ))
  record Quasiring c ℓ : Set (suc (c ⊔ ℓ)) where
  record Nearring c ℓ : Set (suc (c ⊔ ℓ)) where
  record IdempotentMagma c ℓ : Set (suc (c ⊔ ℓ))
  record AlternateMagma c ℓ : Set (suc (c ⊔ ℓ))
  record FlexibleMagma c ℓ : Set (suc (c ⊔ ℓ))
  record MedialMagma c ℓ : Set (suc (c ⊔ ℓ))
  record SemimedialMagma c ℓ : Set (suc (c ⊔ ℓ))
  record LeftBolLoop c ℓ : Set (suc (c ⊔ ℓ))
  record RightBolLoop c ℓ : Set (suc (c ⊔ ℓ))
  record MoufangLoop c ℓ : Set (suc (c ⊔ ℓ))
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
  rawQuasigroup : RawQuasigroup a ℓ₁ → RawQuasigroup b ℓ₂ →
                  RawQuasigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  rawLoop : RawLoop a ℓ₁ → RawLoop b ℓ₂ → RawLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  unitalMagma : UnitalMagma a ℓ₁ → UnitalMagma b ℓ₂ →
                UnitalMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  invertibleMagma : InvertibleMagma a ℓ₁ → InvertibleMagma b ℓ₂ →
                    InvertibleMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  invertibleUnitalMagma : InvertibleUnitalMagma a ℓ₁ → InvertibleUnitalMagma b ℓ₂ →
                          InvertibleUnitalMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  quasigroup : Quasigroup a ℓ₁ → Quasigroup b ℓ₂ → Quasigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  loop : Loop a ℓ₁ → Loop b ℓ₂ → Loop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  kleeneAlgebra : KleeneAlgebra a ℓ₁ → KleeneAlgebra b ℓ₂ →
                  KleeneAlgebra (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
 ```

* Added new definition to `Algebra.Definitions`:
  ```agda
  LeftDividesˡ  : Op₂ A → Op₂ A → Set _
  LeftDividesʳ  : Op₂ A → Op₂ A → Set _
  RightDividesˡ : Op₂ A → Op₂ A → Set _
  RightDividesʳ : Op₂ A → Op₂ A → Set _
  LeftDivides   : Op₂ A → Op₂ A → Set _
  RightDivides  : Op₂ A → Op₂ A → Set _

  LeftInvertible  e _∙_ x = ∃[ x⁻¹ ] (x⁻¹ ∙ x) ≈ e
  RightInvertible e _∙_ x = ∃[ x⁻¹ ] (x ∙ x⁻¹) ≈ e
  Invertible      e _∙_ x = ∃[ x⁻¹ ] ((x⁻¹ ∙ x) ≈ e) × ((x ∙ x⁻¹) ≈ e)
  LeftAlternative _∙_ = ∀ x y  →  ((x ∙ x) ∙ y) ≈ (x ∙ (y ∙ y))
  RightAlternative _∙_ = ∀ x y → (x ∙ (y ∙ y)) ≈ ((x ∙ y) ∙ y)
  Alternative _∙_ = (LeftAlternative _∙_ ) × (RightAlternative _∙_)
  Flexible _∙_ = ∀ x y → ((x ∙ y) ∙ x) ≈ (x ∙ (y ∙ x))
  Medial _∙_ = ∀ x y u z → ((x ∙ y) ∙ (u ∙ z)) ≈ ((x ∙ u) ∙ (y ∙ z))
  LeftSemimedial _∙_ = ∀ x y z → ((x ∙ x) ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ (x ∙ z))
  RightSemimedial _∙_ = ∀ x y z → ((y ∙ z) ∙ (x ∙ x)) ≈ ((y ∙ x) ∙ (z ∙ x))
  Semimedial _∙_ = (LeftSemimedial _∙_) × (RightSemimedial _∙_)
  LeftBol _∙_ = ∀ x y z → (x ∙ (y ∙ (x ∙ z))) ≈ ((x ∙ (y ∙ z)) ∙ z )
  RightBol _∙_ = ∀ x y z → (((z ∙ x) ∙ y) ∙ x) ≈ (z ∙ ((x ∙ y) ∙ x))
  ```

* Added new functions to `Algebra.Definitions.RawSemiring`:
  ```agda
  _^[_]*_ : A → ℕ → A → A
  _^ᵗ_     : A → ℕ → A
  ```

* Added new proofs to `Algebra.Properties.CommutativeSemigroup`:
  ```
  interchange : Interchangable _∙_ _∙_
  xy∙xx≈x∙yxx : ∀ x y → (x ∙ y) ∙ (x ∙ x) ≈ x ∙ (y ∙ (x ∙ x))
  leftSemimedial : LeftSemimedial _∙_
  rightSemimedial : RightSemimedial _∙_
  middleSemimedial : ∀ x y z → (x ∙ y) ∙ (z ∙ x) ≈ (x ∙ z) ∙ (y ∙ x)
  ```
* Added new proofs to `Algebra.Properties.Semigroup`:
  ```
  leftAlternative : LeftAlternative _∙_
  rightAlternative : RightAlternative _∙_
  flexible : Flexible _∙_
  ```

* Added new definitions to `Algebra.Structures`:
  ```agda
  record IsUnitalMagma (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  record IsInvertibleMagma (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  record IsInvertibleUnitalMagma (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  record IsQuasigroup (∙ \\ // : Op₂ A) : Set (a ⊔ ℓ)
  record IsLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  record IsRingWithoutOne (+ * : Op₂ A) (-_ : Op₁ A) (0# : A) : Set (a ⊔ ℓ)
  record IsKleeneAlgebra (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ)
  record IsQuasiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ)
  record IsNearring (+ * : Op₂ A) (0# 1# : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  record IsIdempotentMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  record IsAlternateMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  record IsFlexibleMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  record IsMedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  record IsSemimedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  record IsLeftBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  record IsRightBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) 
  record IsMoufangLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  ```
  and the existing record `IsLattice` now provides
  ```
  ∨-isCommutativeSemigroup : IsCommutativeSemigroup ∨
  ∧-isCommutativeSemigroup : IsCommutativeSemigroup ∧
  ```
  and their corresponding algebraic substructures.

* Added new records to `Algebra.Morphism.Structures`:
  ```agda
  record IsQuasigroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  record IsQuasigroupMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  record IsQuasigroupIsomorphism  (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  record IsLoopHomomorphism       (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  record IsLoopMonomorphism       (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  record IsLoopIsomorphism        (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  record IsRingWithoutOneHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  record IsRingWithoutOneMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  record IsRingWithoutOneIsoMorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  ```

* Added new functions in `Category.Monad.State`:
  ```
  runState  : State s a → s → a × s
  evalState : State s a → s → a
  execState : State s a → s → s
  ```

* Added new proofs in `Data.Bool.Properties`:
  ```agda
  <-wellFounded : WellFounded _<_
  ```

* Added new functions in `Data.Fin.Base`:
  ```
  finToFun  : Fin (m ^ n) → (Fin n → Fin m)
  funToFin  : (Fin m → Fin n) → Fin (n ^ m)
  quotient  : Fin (m * n) → Fin m
  remainder : Fin (m * n) → Fin n
  ```

* Added new proofs in `Data.Fin.Induction`:
  every (strict) partial order is well-founded and Noetherian.

  ```agda
  spo-wellFounded : ∀ {r} {_⊏_ : Rel (Fin n) r} → IsStrictPartialOrder _≈_ _⊏_ → WellFounded _⊏_
  spo-noetherian  : ∀ {r} {_⊏_ : Rel (Fin n) r} → IsStrictPartialOrder _≈_ _⊏_ → WellFounded (flip _⊏_)
  ```

* Added new definitions and proofs in `Data.Fin.Permutation`:
  ```agda
  insert         : Fin (suc m) → Fin (suc n) → Permutation m n → Permutation (suc m) (suc n)
  insert-punchIn : insert i j π ⟨$⟩ʳ punchIn i k ≡ punchIn j (π ⟨$⟩ʳ k)
  insert-remove  : insert i (π ⟨$⟩ʳ i) (remove i π) ≈ π
  remove-insert  : remove i (insert i j π) ≈ π
  ```

* In `Data.Fin.Properties`:
  the proof that an injection from a type `A` into `Fin n` induces a
  decision procedure for `_≡_` on `A` has been generalized to other
  equivalences over `A` (i.e. to arbitrary setoids), and renamed from
  `eq?` to the more descriptive `inj⇒≟` and `inj⇒decSetoid`.

* Added new proofs in `Data.Fin.Properties`:
  ```
  1↔⊤                : Fin 1 ↔ ⊤

  0≢1+n              : zero ≢ suc i

  ↑ˡ-injective       : i ↑ˡ n ≡ j ↑ˡ n → i ≡ j
  ↑ʳ-injective       : n ↑ʳ i ≡ n ↑ʳ j → i ≡ j
  finTofun-funToFin  : funToFin ∘ finToFun ≗ id
  funTofin-funToFun  : finToFun (funToFin f) ≗ f
  ^↔→                : Extensionality _ _ → Fin (m ^ n) ↔ (Fin n → Fin m)

  toℕ-mono-<         : i < j → toℕ i ℕ.< toℕ j
  toℕ-mono-≤         : i ≤ j → toℕ i ℕ.≤ toℕ j
  toℕ-cancel-≤       : toℕ i ℕ.≤ toℕ j → i ≤ j
  toℕ-cancel-<       : toℕ i ℕ.< toℕ j → i < j

  toℕ-combine        : toℕ (combine i j) ≡ k ℕ.* toℕ i ℕ.+ toℕ j
  combine-injectiveˡ : combine i j ≡ combine k l → i ≡ k
  combine-injectiveʳ : combine i j ≡ combine k l → j ≡ l
  combine-injective  : combine i j ≡ combine k l → i ≡ k × j ≡ l
  combine-surjective : ∀ i → ∃₂ λ j k → combine j k ≡ i
  combine-monoˡ-<    : i < j → combine i k < combine j l

  lower₁-injective   : lower₁ i n≢i ≡ lower₁ j n≢j → i ≡ j
  pinch-injective    : suc i ≢ j → suc i ≢ k → pinch i j ≡ pinch i k → j ≡ k

  i<1+i              : i < suc i

  injective⇒≤               : ∀ {f : Fin m → Fin n} → Injective f → m ℕ.≤ n
  <⇒notInjective            : ∀ {f : Fin m → Fin n} → n ℕ.< m → ¬ (Injective f)
  ℕ→Fin-notInjective        : ∀ (f : ℕ → Fin n) → ¬ (Injective f)
  cantor-schröder-bernstein : ∀ {f : Fin m → Fin n} {g : Fin n → Fin m} → Injective f → Injective g → m ≡ n
  ```

* Added new functions in `Data.Integer.Base`:
  ```
  _^_ : ℤ → ℕ → ℤ
  ```

* Added new proofs in `Data.Integer.Properties`:
  ```agda
  sign-cong′ : s₁ ◃ n₁ ≡ s₂ ◃ n₂ → s₁ ≡ s₂ ⊎ (n₁ ≡ 0 × n₂ ≡ 0)
  ≤-⊖        : m ℕ.≤ n → n ⊖ m ≡ + (n ∸ m)
  ∣⊖∣-≤      : m ℕ.≤ n → ∣ m ⊖ n ∣ ≡ n ∸ m
  ∣-∣-≤      : i ≤ j → + ∣ i - j ∣ ≡ j - i

  i^n≡0⇒i≡0      : i ^ n ≡ 0ℤ → i ≡ 0ℤ
  ^-identityʳ    : i ^ 1 ≡ i
  ^-zeroˡ        : 1 ^ n ≡ 1
  ^-*-assoc      : (i ^ m) ^ n ≡ i ^ (m ℕ.* n)
  ^-distribˡ-+-* : i ^ (m ℕ.+ n) ≡ i ^ m * i ^ n

  *-rawMagma    : RawMagma 0ℓ 0ℓ
  *-1-rawMonoid : RawMonoid 0ℓ 0ℓ

  ^-isMagmaHomomorphism  : IsMagmaHomomorphism  ℕ.+-rawMagma    *-rawMagma    (i ^_)
  ^-isMonoidHomomorphism : IsMonoidHomomorphism ℕ.+-0-rawMonoid *-1-rawMonoid (i ^_)
  ```

* Added new functions in `Data.List`:
  ```agda
  takeWhileᵇ   : (A → Bool) → List A → List A
  dropWhileᵇ   : (A → Bool) → List A → List A
  filterᵇ      : (A → Bool) → List A → List A
  partitionᵇ   : (A → Bool) → List A → List A × List A
  spanᵇ        : (A → Bool) → List A → List A × List A
  breakᵇ       : (A → Bool) → List A → List A × List A
  linesByᵇ     : (A → Bool) → List A → List (List A)
  wordsByᵇ     : (A → Bool) → List A → List (List A)
  derunᵇ       : (A → A → Bool) → List A → List A
  deduplicateᵇ : (A → A → Bool) → List A → List A
  ```

* Added new proofs in `Data.List.Relation.Binary.Lex.Strict`:
  ```agda
  xs≮[] : ¬ xs < []
  ```

* Added new proofs to `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  Any-resp-[σ⁻¹∘σ] : (σ : xs ↭ ys) → (ix : Any P xs) → Any-resp-↭ (trans σ (↭-sym σ)) ix ≡ ix
  ∈-resp-[σ⁻¹∘σ]   : (σ : xs ↭ ys) → (ix : x ∈ xs)   → ∈-resp-↭   (trans σ (↭-sym σ)) ix ≡ ix
  ```

* Added new functions in `Data.List.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All P ∪ Any Q ]
  ```

* Added new functions in `Data.List.Fresh.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All {R = R} P ∪ Any Q ]
  ```

* Add new proofs in `Data.List.Properties`:
  ```agda
  ∈⇒∣product : n ∈ ns → n ∣ product ns
  ∷ʳ-++ : xs ∷ʳ a ++ ys ≡ xs ++ a ∷ ys
  ```

* Added new patterns and definitions to `Data.Nat.Base`:
  ```agda
  pattern z<s {n}         = s≤s (z≤n {n})
  pattern s<s {m} {n} m<n = s≤s {m} {n} m<n

  pattern <′-base          = ≤′-refl
  pattern <′-step {n} m<′n = ≤′-step {n} m<′n
  ```


* Added new definitions and proofs to `Data.Nat.Primality`:
  ```agda
  Composite        : ℕ → Set
  composite?       : Decidable composite
  composite⇒¬prime : Composite n → ¬ Prime n
  ¬composite⇒prime : 2 ≤ n → ¬ Composite n → Prime n
  prime⇒¬composite : Prime n → ¬ Composite n
  ¬prime⇒composite : 2 ≤ n → ¬ Prime n → Composite n
  euclidsLemma     : Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  nonZero?  : Decidable NonZero
  n≮0       : n ≮ 0
  n+1+m≢m   : n + suc m ≢ m
  m*n≡0⇒m≡0 : .{{_ : NonZero n}} → m * n ≡ 0 → m ≡ 0
  n>0⇒n≢0   : n > 0 → n ≢ 0
  m^n≢0     : .{{_ : NonZero m}} → NonZero (m ^ n)
  m*n≢0     : .{{_ : NonZero m}} .{{_ : NonZero n}} → NonZero (m * n)
  m≤n⇒n∸m≤n : m ≤ n → n ∸ m ≤ n

  ≤-pred        : suc m ≤ suc n → m ≤ n
  s<s-injective : ∀ {p q : m < n} → s<s p ≡ s<s q → p ≡ q
  <-pred        : suc m < suc n → m < n
  <-step        : m < n → m < 1 + n
  m<1+n⇒m<n∨m≡n : m < suc n → m < n ⊎ m ≡ n

  z<′s : zero <′ suc n
  s<′s : m <′ n → suc m <′ suc n
  <⇒<′ : m < n → m <′ n
  <′⇒< : m <′ n → m < n

  1≤n!    : 1 ≤ n !
  _!≢0    : NonZero (n !)
  _!*_!≢0 : NonZero (m ! * n !)

  anyUpTo? : ∀ (P? : U.Decidable P) (v : ℕ) → Dec (∃ λ n → n < v × P n)
  allUpTo? : ∀ (P? : U.Decidable P) (v : ℕ) → Dec (∀ {n} → n < v → P n)

  n≤1⇒n≡0∨n≡1 : n ≤ 1 → n ≡ 0 ⊎ n ≡ 1

  2^n>0 : 2 ^ n > 0

  n≡⌊n+n/2⌋ : n ≡ ⌊ n + n /2⌋
  n≡⌈n+n/2⌉ : n ≡ ⌈ n + n /2⌉
  ```

* Added new functions in `Data.Nat`:
  ```agda
  _! : ℕ → ℕ
  ```

* Added new proofs in `Data.Nat.DivMod`:
  ```agda
  m%n≤n          : .{{_ : NonZero n}} → m % n ≤ n
  m*n/m!≡n/[m∸1]! : .{{_ : NonZero m}} → m * n / m ! ≡ n / (pred m) !
  ```

* Added new proofs in `Data.Nat.Divisibility`:
  ```agda
  n∣m*n*o       : n ∣ m * n * o
  m*n∣⇒m∣       : m * n ∣ i → m ∣ i
  m*n∣⇒n∣       : m * n ∣ i → n ∣ i
  m≤n⇒m!∣n!     : m ≤ n → m ! ∣ n !
  m/n/o≡m/[n*o] : .{{NonZero n}} .{{NonZero o}} → n * o ∣ m → (m / n) / o ≡ m / (n * o)
  ```

* Added new patterns in `Data.Nat.Reflection`:
  ```agda
  pattern `ℕ     = def (quote ℕ) []
  pattern `zero  = con (quote ℕ.zero) []
  pattern `suc x = con (quote ℕ.suc) (x ⟨∷⟩ [])
  ```

* Added new rounding functions in `Data.Rational.Base`:
  ```agda
  floor ceiling truncate round ⌊_⌋ ⌈_⌉ [_] : ℚ → ℤ
  fracPart : ℚ → ℚ
  ```

* Added new definitions and proofs in `Data.Rational.Properties`:
  ```agda
  ↥ᵘ-toℚᵘ : ↥ᵘ (toℚᵘ p) ≡ ↥ p
  ↧ᵘ-toℚᵘ : ↧ᵘ (toℚᵘ p) ≡ ↧ p

  +-*-rawNearSemiring                 : RawNearSemiring 0ℓ 0ℓ
  +-*-rawSemiring                     : RawSemiring 0ℓ 0ℓ
  toℚᵘ-isNearSemiringHomomorphism-+-* : IsNearSemiringHomomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
  toℚᵘ-isNearSemiringMonomorphism-+-* : IsNearSemiringMonomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
  toℚᵘ-isSemiringHomomorphism-+-*     : IsSemiringHomomorphism     +-*-rawSemiring     ℚᵘ.+-*-rawSemiring     toℚᵘ
  toℚᵘ-isSemiringMonomorphism-+-*     : IsSemiringMonomorphism     +-*-rawSemiring     ℚᵘ.+-*-rawSemiring     toℚᵘ

  pos⇒nonZero       : .{{Positive p}} → NonZero p
  neg⇒nonZero       : .{{Negative p}} → NonZero p
  nonZero⇒1/nonZero : .{{_ : NonZero p}} → NonZero (1/ p)
  ```

* Added new rounding functions in `Data.Rational.Unnormalised.Base`:
  ```agda
  floor ceiling truncate round ⌊_⌋ ⌈_⌉ [_] : ℚᵘ → ℤ
  fracPart : ℚᵘ → ℚᵘ
  ```

* Added new definitions in `Data.Rational.Unnormalised.Properties`:
  ```agda
  +-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
  +-*-rawSemiring     : RawSemiring 0ℓ 0ℓ

  ≰⇒≥ : _≰_ ⇒ _≥_

  *-mono-≤-nonNeg   : .{{_ : NonNegative p}} .{{_ : NonNegative r}} → p ≤ q → r ≤ s → p * r ≤ q * s
  *-mono-<-nonNeg   : .{{_ : NonNegative p}} .{{_ : NonNegative r}} → p < q → r < s → p * r < q * s
  1/-antimono-≤-pos : .{{_ : Positive p}}    .{{_ : Positive q}}    → p ≤ q → 1/ q ≤ 1/ p
  ⊓-mono-<          : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  ⊔-mono-<          : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_

  pos⇒nonZero          : .{{_ : Positive p}} → NonZero p
  neg⇒nonZero          : .{{_ : Negative p}} → NonZero p
  pos+pos⇒pos          : .{{_ : Positive p}}    .{{_ : Positive q}}    → Positive (p + q)
  nonNeg+nonNeg⇒nonNeg : .{{_ : NonNegative p}} .{{_ : NonNegative q}} → NonNegative (p + q)
  pos*pos⇒pos          : .{{_ : Positive p}}    .{{_ : Positive q}}    → Positive (p * q)
  nonNeg*nonNeg⇒nonNeg : .{{_ : NonNegative p}} .{{_ : NonNegative q}} → NonNegative (p * q)
  pos⊓pos⇒pos          : .{{_ : Positive p}}    .{{_ : Positive q}}    → Positive (p ⊓ q)
  pos⊔pos⇒pos          : .{{_ : Positive p}}    .{{_ : Positive q}}    → Positive (p ⊔ q)
  1/nonZero⇒nonZero    : .{{_ : NonZero p}} → NonZero (1/ p)
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

* Added new proofs to `Data.Sign.Properties`:
  ```agda
  *-inverse : Inverse + id _*_
  *-isCommutativeSemigroup : IsCommutativeSemigroup _*_
  *-isCommutativeMonoid : IsCommutativeMonoid _*_ +
  *-isGroup : IsGroup _*_ + id
  *-isAbelianGroup : IsAbelianGroup _*_ + id
  *-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
  *-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
  *-group : Group 0ℓ 0ℓ
  *-abelianGroup : AbelianGroup 0ℓ 0ℓ
  ```

* Added new functions in `Data.String.Base`:
  ```agda
  wordsByᵇ : (Char → Bool) → String → List String
  linesByᵇ : (Char → Bool) → String → List String
  ```

* Added new proofs in `Data.String.Properties`:
  ```
  ≤-isDecTotalOrder-≈ : IsDecTotalOrder _≈_ _≤_
  ≤-decTotalOrder-≈   :  DecTotalOrder _ _ _
  ```
* Added new definitions in `Data.Sum.Properties`:
  ```
  swap-↔ : (A ⊎ B) ↔ (B ⊎ A)
  ```

* Added new proofs in `Data.Sum.Properties`:
  ```
  map-assocˡ : (f : A → C) (g : B → D) (h : C → F) →
    map (map f g) h ∘ assocˡ ≗ assocˡ ∘ map f (map g h)
  map-assocʳ : (f : A → C) (g : B → D) (h : C → F) →
    map f (map g h) ∘ assocʳ ≗ assocʳ ∘ map (map f g) h
  ```

* Made `Map` public in `Data.Tree.AVL.IndexedMap`

* Added new definitions in `Data.Vec.Base`:
  ```agda
  truncate : m ≤ n → Vec A n → Vec A m
  pad      : m ≤ n → A → Vec A m → Vec A n

  FoldrOp A B = ∀ {n} → A → B n → B (suc n)
  FoldlOp A B = ∀ {n} → B n → A → B (suc n)

  foldr′ : (A → B → B) → B → Vec A n → B
  foldl′ : (B → A → B) → B → Vec A n → B
  countᵇ : (A → Bool) → Vec A n → ℕ

  iterate : (A → A) → A → Vec A n

  diagonal           : Vec (Vec A n) n → Vec A n
  DiagonalBind._>>=_ : Vec A n → (A → Vec B n) → Vec B n
  _ʳ++_              : Vec A m → Vec A n → Vec A (m + n)
  ```

* Added new instance in `Data.Vec.Categorical`:
  ```agda
  monad : RawMonad (λ (A : Set a) → Vec A n)
  ```

* Added new proofs in `Data.Vec.Properties`:
  ```agda
  padRight-refl      : padRight ≤-refl a xs ≡ xs
  padRight-replicate : replicate a ≡ padRight le a (replicate a)
  padRight-trans     : padRight (≤-trans m≤n n≤p) a xs ≡ padRight n≤p a (padRight m≤n a xs)

  truncate-refl     : truncate ≤-refl xs ≡ xs
  truncate-trans    : truncate (≤-trans m≤n n≤p) xs ≡ truncate m≤n (truncate n≤p xs)
  truncate-padRight : truncate m≤n (padRight m≤n a xs) ≡ xs

  map-const    : map (const x) xs ≡ replicate x
  map-⊛        : map f xs ⊛ map g xs ≡ map (f ˢ g) xs
  map-++       : map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-is-foldr : map f ≗ foldr (Vec B) (λ x ys → f x ∷ ys) []
  map-∷ʳ       : map f (xs ∷ʳ x) ≡ (map f xs) ∷ʳ (f x)
  map-reverse  : map f (reverse xs) ≡ reverse (map f xs)
  map-ʳ++      : map f (xs ʳ++ ys) ≡ map f xs ʳ++ map f ys

  lookup-concat : lookup (concat xss) (combine i j) ≡ lookup (lookup xss i) j

  ⊛-is->>=    : fs ⊛ xs ≡ fs >>= flip map xs
  lookup-⊛*   : lookup (fs ⊛* xs) (combine i j) ≡ (lookup fs i $ lookup xs j)
  ++-is-foldr : xs ++ ys ≡ foldr ((Vec A) ∘ (_+ n)) _∷_ ys xs
  []≔-++-↑ʳ   : (xs ++ ys) [ m ↑ʳ i ]≔ y ≡ xs ++ (ys [ i ]≔ y)
  unfold-ʳ++  : xs ʳ++ ys ≡ reverse xs ++ ys

  foldl-universal : ∀ (h : ∀ {c} (C : ℕ → Set c) (g : FoldlOp A C) (e : C zero) → ∀ {n} → Vec A n → C n) →
                    (∀ ... → h C g e [] ≡ e) →
                    (∀ ... → h C g e ∘ (x ∷_) ≗ h (C ∘ suc) g (g e x)) →
                    h B f e ≗ foldl B f e
  foldl-fusion  : h d ≡ e → (∀ ... → h (f b x) ≡ g (h b) x) → h ∘ foldl B f d ≗ foldl C g e
  foldl-∷ʳ      : foldl B f e (ys ∷ʳ y) ≡ f (foldl B f e ys) y
  foldl-[]      : foldl B f e [] ≡ e
  foldl-reverse : foldl B {n} f e ∘ reverse ≗ foldr B (flip f) e

  foldr-[]      : foldr B f e [] ≡ e
  foldr-++      : foldr B f e (xs ++ ys) ≡ foldr (B ∘ (_+ n)) f (foldr B f e ys) xs
  foldr-∷ʳ      : foldr B f e (ys ∷ʳ y) ≡ foldr (B ∘ suc) f (f y e) ys
  foldr-ʳ++     : foldr B f e (xs ʳ++ ys) ≡ foldl (B ∘ (_+ n)) (flip f) (foldr B f e ys) xs
  foldr-reverse : foldr B f e ∘ reverse ≗ foldl B (flip f) e

  ∷ʳ-injective  : xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
  ∷ʳ-injectiveˡ : xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
  ∷ʳ-injectiveʳ : xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y

  reverse-∷          : reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
  reverse-involutive : Involutive _≡_ reverse
  reverse-reverse    : reverse xs ≡ ys → reverse ys ≡ xs
  reverse-injective  : reverse xs ≡ reverse ys → xs ≡ ys

  transpose-replicate : transpose (replicate xs) ≡ map replicate xs
  ```

* Added new proofs in `Data.Vec.Relation.Binary.Lex.Strict`:
  ```agda
  xs≮[] : ∀ {n} (xs : Vec A n) → ¬ xs < []
  ```

* Added new functions in `Data.Vec.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All P ∪ Any Q ]
  ```

* Added vector associativity proof to  `Data.Vec.Relation.Binary.Equality.Setoid`:
  ```
  ++-assoc : (xs ++ ys) ++ zs ≋ xs ++ (ys ++ zs)
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

  when   : Bool → IO ⊤ → IO ⊤
  unless : Bool → IO ⊤ → IO ⊤

  whenJust  : Maybe A → (A → IO ⊤) → IO ⊤
  untilJust : IO (Maybe A) → IO A
  ```

* Added new functions in `Reflection.AST.Term`:
  ```
  stripPis     : Term → List (String × Arg Type) × Term
  prependLams  : List (String × Visibility) → Term → Term
  prependHLams : List String → Term → Term
  prependVLams : List String → Term → Term
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

* Added new proofs to `Relation.Binary.Lattice.Properties.{Join,Meet}Semilattice`:
  ```agda
  isPosemigroup : IsPosemigroup _≈_ _≤_ _∨_
  posemigroup : Posemigroup c ℓ₁ ℓ₂
  ≈-dec⇒≤-dec : Decidable _≈_ → Decidable _≤_
  ≈-dec⇒isDecPartialOrder : Decidable _≈_ → IsDecPartialOrder _≈_ _≤_
  ```

* Added new proofs to `Relation.Binary.Lattice.Properties.Bounded{Join,Meet}Semilattice`:
  ```agda
  isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∨_ ⊥
  commutativePomonoid : CommutativePomonoid c ℓ₁ ℓ₂
  ```

* Added new proofs to `Relation.Binary.Properties.Poset`:
  ```agda
  ≤-dec⇒≈-dec : Decidable _≤_ → Decidable _≈_
  ≤-dec⇒isDecPartialOrder : Decidable _≤_ → IsDecPartialOrder _≈_ _≤_
  ```

* Added new proofs in `Relation.Binary.Properties.StrictPartialOrder`:
  ```agda
  >-strictPartialOrder : StrictPartialOrder s₁ s₂ s₃
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

* Added new definitions in `Relation.Unary`:
  ```
  _≐_  : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  _≐′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  _∖_  : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  ```

* Added new proofs in `Relation.Unary.Properties`:
  ```
  ⊆-reflexive : _≐_ ⇒ _⊆_
  ⊆-antisym : Antisymmetric _≐_ _⊆_
  ⊆-min : Min _⊆_ ∅
  ⊆-max : Max _⊆_ U
  ⊂⇒⊆ : _⊂_ ⇒ _⊆_
  ⊂-trans : Trans _⊂_ _⊂_ _⊂_
  ⊂-⊆-trans : Trans _⊂_ _⊆_ _⊂_
  ⊆-⊂-trans : Trans _⊆_ _⊂_ _⊂_
  ⊂-respʳ-≐ : _⊂_ Respectsʳ _≐_
  ⊂-respˡ-≐ : _⊂_ Respectsˡ _≐_
  ⊂-resp-≐ : _⊂_ Respects₂ _≐_
  ⊂-irrefl : Irreflexive _≐_ _⊂_
  ⊂-antisym : Antisymmetric _≐_ _⊂_
  ∅-⊆′ : (P : Pred A ℓ) → ∅ ⊆′ P
  ⊆′-U : (P : Pred A ℓ) → P ⊆′ U
  ⊆′-refl : Reflexive {A = Pred A ℓ} _⊆′_
  ⊆′-reflexive : _≐′_ ⇒ _⊆′_
  ⊆′-trans : Trans _⊆′_ _⊆′_ _⊆′_
  ⊆′-antisym : Antisymmetric _≐′_ _⊆′_
  ⊆′-min : Min _⊆′_ ∅
  ⊆′-max : Max _⊆′_ U
  ⊂′⇒⊆′ : _⊂′_ ⇒ _⊆′_
  ⊂′-trans : Trans _⊂′_ _⊂′_ _⊂′_
  ⊂′-⊆′-trans : Trans _⊂′_ _⊆′_ _⊂′_
  ⊆′-⊂′-trans : Trans _⊆′_ _⊂′_ _⊂′_
  ⊂′-respʳ-≐′ : _⊂′_ Respectsʳ _≐′_
  ⊂′-respˡ-≐′ : _⊂′_ Respectsˡ _≐′_
  ⊂′-resp-≐′ : _⊂′_ Respects₂ _≐′_
  ⊂′-irrefl : Irreflexive _≐′_ _⊂′_
  ⊂′-antisym : Antisymmetric _≐′_ _⊂′_
  ⊆⇒⊆′ : _⊆_ ⇒ _⊆′_
  ⊆′⇒⊆ : _⊆′_ ⇒ _⊆_
  ⊂⇒⊂′ : _⊂_ ⇒ _⊂′_
  ⊂′⇒⊂ : _⊂′_ ⇒ _⊂_
  ≐-refl : Reflexive _≐_
  ≐-sym : Sym _≐_ _≐_
  ≐-trans : Trans _≐_ _≐_ _≐_
  ≐′-refl : Reflexive _≐′_
  ≐′-sym : Sym _≐′_ _≐′_
  ≐′-trans : Trans _≐′_ _≐′_ _≐′_
  ≐⇒≐′ : _≐_ ⇒ _≐′_
  ≐′⇒≐ : _≐′_ ⇒ _≐_

  U-irrelevant : Irrelevant {A = A} U
  ∁-irrelevant : (P : Pred A ℓ) → Irrelevant (∁ P)
  ```

* Generalised proofs in `Relation.Unary.Properties`:
  ```
  ⊆-trans : Trans _⊆_ _⊆_ _⊆_
  ```

* Added new proofs in `Relation.Binary.Properties.Setoid`:
  ```
  ≈-isPreorder     : IsPreorder _≈_ _≈_
  ≈-isPartialOrder : IsPartialOrder _≈_ _≈_

  ≈-preorder : Preorder a ℓ ℓ
  ≈-poset    : Poset a ℓ ℓ
  ```

* Added new definitions in `Relation.Binary.Definitions`:
  ```
  Cotransitive _#_ = ∀ {x y} → x # y → ∀ z → (x # z) ⊎ (z # y)
  Tight    _≈_ _#_ = ∀ x y → (¬ x # y → x ≈ y) × (x ≈ y → ¬ x # y)

  Monotonic₁         _≤_ _⊑_ f     = f Preserves _≤_ ⟶ _⊑_
  Antitonic₁         _≤_ _⊑_ f     = f Preserves (flip _≤_) ⟶ _⊑_
  Monotonic₂         _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ _≤_ ⟶ _⊑_ ⟶ _≼_
  MonotonicAntitonic _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ _≤_ ⟶ (flip _⊑_) ⟶ _≼_
  AntitonicMonotonic _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ (flip _≤_) ⟶ _⊑_ ⟶ _≼_
  Antitonic₂         _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ (flip _≤_) ⟶ (flip _⊑_) ⟶ _≼_
  Adjoint            _≤_ _⊑_ f g   = ∀ {x y} → (f x ⊑ y → x ≤ g y) × (x ≤ g y → f x ⊑ y)
  ```

* Added new definitions in `Relation.Binary.Bundles`:
  ```
  record ApartnessRelation c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  ```

* Added new definitions in `Relation.Binary.Structures`:
  ```
  record IsApartnessRelation (_#_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```
  sym⇒¬-sym       : Symmetric _∼_ → Symmetric _≁_
  cotrans⇒¬-trans : Cotransitive _∼_ → Transitive _≁_
  irrefl⇒¬-refl   : Reflexive _≈_ → Irreflexive _≈_ _∼_ →  Reflexive _≁_
  mono₂⇒cong₂     : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ → ∀ {f} →
                    f Preserves₂ ≤₁ ⟶ ≤₁ ⟶ ≤₂ →
                    f Preserves₂ ≈₁ ⟶ ≈₁ ⟶ ≈₂
  ```

* Added new operations in `Relation.Binary.PropositionalEquality.Properties`:
  ```
  J       : (B : (y : A) → x ≡ y → Set b) (p : x ≡ y) → B x refl → B y p
  dcong   : (p : x ≡ y) → subst B p (f x) ≡ f y
  dcong₂  : (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
  dsubst₂ : (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
  ddcong₂ : (p : x₁ ≡ x₂) (q : subst B p y₁ ≡ y₂) → dsubst₂ C p q (f x₁ y₁) ≡ f x₂ y₂

  isPartialOrder : IsPartialOrder _≡_ _≡_
  poset          : Set a → Poset _ _ _
  ```

* Added new operations in `System.Exit`:
  ```
  isSuccess : ExitCode → Bool
  isFailure : ExitCode → Bool
  ```

* Added new functions in `Codata.Guarded.Stream`:
  ```
  transpose : List (Stream A) → Stream (List A)
  transpose⁺ : List⁺ (Stream A) → Stream (List⁺ A)
  concat : Stream (List⁺ A) → Stream A
  ```

* Added new proofs in `Codata.Guarded.Stream.Properties`:
  ```
  cong-concat : {ass bss : Stream (List⁺.List⁺ A)} → ass ≈ bss → concat ass ≈ concat bss
  map-concat : ∀ (f : A → B) ass → map f (concat ass) ≈ concat (map (List⁺.map f) ass)
  lookup-transpose : ∀ n (ass : List (Stream A)) → lookup n (transpose ass) ≡ List.map (lookup n) ass
  lookup-transpose⁺ : ∀ n (ass : List⁺ (Stream A)) → lookup n (transpose⁺ ass) ≡ List⁺.map (lookup n) ass
  ```

* Added new corollaries in `Data.List.Membership.Setoid.Properties`:
  ```
  ∈-++⁺∘++⁻ : ∀ {v} xs {ys} (p : v ∈ xs ++ ys) → [ ∈-++⁺ˡ , ∈-++⁺ʳ xs ]′ (∈-++⁻ xs p) ≡ p
  ∈-++⁻∘++⁺ : ∀ {v} xs {ys} (p : v ∈ xs ⊎ v ∈ ys) → ∈-++⁻ xs ([ ∈-++⁺ˡ , ∈-++⁺ʳ xs ]′ p) ≡ p
  ∈-++↔ : ∀ {v xs ys} → (v ∈ xs ⊎ v ∈ ys) ↔ v ∈ xs ++ ys
  ∈-++-comm : ∀ {v} xs ys → v ∈ xs ++ ys → v ∈ ys ++ xs
  ∈-++-comm∘++-comm : ∀ {v} xs {ys} (p : v ∈ xs ++ ys) → ∈-++-comm ys xs (∈-++-comm xs ys p) ≡ p
  ∈-++↔++ : ∀ {v} xs ys → v ∈ xs ++ ys ↔ v ∈ ys ++ xs

NonZero/Positive/Negative changes
---------------------------------

This is a full list of proofs that have changed form to use irrelevant instance arguments:

* In `Data.Nat.Base`:
  ```
  ≢-nonZero⁻¹ : ∀ {n} → .(NonZero n) → n ≢ 0
  >-nonZero⁻¹ : ∀ {n} → .(NonZero n) → n > 0
  ```

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
  positive⁻¹        : ∀ {i} → Positive i → i > 0ℤ
  negative⁻¹        : ∀ {i} → Negative i → i < 0ℤ
  nonPositive⁻¹     : ∀ {i} → NonPositive i → i ≤ 0ℤ
  nonNegative⁻¹     : ∀ {i} → NonNegative i → i ≥ 0ℤ
  negative<positive : ∀ {i j} → Negative i → Positive j → i < j

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
  positive⁻¹           : ∀ {q} → .(Positive q) → q > 0ℚᵘ
  nonNegative⁻¹        : ∀ {q} → .(NonNegative q) → q ≥ 0ℚᵘ
  negative⁻¹           : ∀ {q} → .(Negative q) → q < 0ℚᵘ
  nonPositive⁻¹        : ∀ {q} → .(NonPositive q) → q ≤ 0ℚᵘ
  positive⇒nonNegative : ∀ {p} → Positive p → NonNegative p
  negative⇒nonPositive : ∀ {p} → Negative p → NonPositive p
  negative<positive    : ∀ {p q} → .(Negative p) → .(Positive q) → p < q
  nonNeg∧nonPos⇒0      : ∀ {p} → .(NonNegative p) → .(NonPositive p) → p ≃ 0ℚᵘ

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
  positive⁻¹ : Positive p → p > 0ℚ
  nonNegative⁻¹ : NonNegative p → p ≥ 0ℚ
  negative⁻¹ : Negative p → p < 0ℚ
  nonPositive⁻¹ : NonPositive p → p ≤ 0ℚ
  negative<positive : Negative p → Positive q → p < q
  nonNeg≢neg : ∀ p q → NonNegative p → Negative q → p ≢ q
  pos⇒nonNeg : ∀ p → Positive p → NonNegative p
  neg⇒nonPos : ∀ p → Negative p → NonPositive p
  nonNeg∧nonZero⇒pos : ∀ p → NonNegative p → NonZero p → Positive p

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

* In `Data.List.NonEmpty.Base`:
  ```agda
  drop+ : ℕ → List⁺ A → List⁺ A
  ```
  When drop+ping more than the size of the length of the list, the last element remains.

* Added new proofs in `Data.List.NonEmpty.Properties`:
  ```agda
  length-++⁺ : length (xs ++⁺ ys) ≡ length xs + length ys
  length-++⁺-tail : length (xs ++⁺ ys) ≡ suc (length xs + length (tail ys))
  ++-++⁺ : (xs ++ ys) ++⁺ zs ≡ xs ++⁺ ys ++⁺ zs
  ++⁺-cancelˡ′ : xs ++⁺ zs ≡ ys ++⁺ zs′ → List.length xs ≡ List.length ys → zs ≡ zs′
  ++⁺-cancelˡ : xs ++⁺ ys ≡ xs ++⁺ zs → ys ≡ zs
  drop+-++⁺ : drop+ (length xs) (xs ++⁺ ys) ≡ ys
  map-++⁺-commute : map f (xs ++⁺ ys) ≡ map f xs ++⁺ map f ys
  length-map : length (map f xs) ≡ length xs
  map-cong : f ≗ g → map f ≗ map g
  map-compose : map (g ∘ f) ≗ map g ∘ map f
  ```

* Added new functions and proofs in `Data.Nat.GeneralisedArithmetic`:
  ```agda
  iterate : (A → A) → A → ℕ → A
  iterate-is-fold : ∀ (z : A) s m → fold z s m ≡ iterate s z m
  ```

* Added new proofs to `Function.Properties.Inverse`:
  ```agda
  Inverse⇒Injection : Inverse S T → Injection S T
  ↔⇒↣ : A ↔ B → A ↣ B
  ```

* Added a new isomorphism to `Data.Fin.Properties`:
  ```agda
  2↔Bool : Fin 2 ↔ Bool
  ```

* Added new isomorphisms to `Data.Unit.Polymorphic.Properties`:
  ```agda
  ⊤↔⊤* : ⊤ {ℓ} ↔ ⊤*
  ```

* Added new isomorphisms to `Data.Vec.N-ary`:
  ```agda
  Vec↔N-ary : ∀ n → (Vec A n → B) ↔ N-ary n A B
  ```

* Added new isomorphisms to `Data.Vec.Recursive`:
  ```agda
  lift↔ : ∀ n → A ↔ B → A ^ n ↔ B ^ n
  Fin[m^n]↔Fin[m]^n : ∀ m n → Fin (m ^ n) ↔ Fin m Vec.^ n
  ```

* Added new functions to `Function.Properties.Inverse`:
  ```agda
  ↔-refl  : Reflexive _↔_
  ↔-sym   : Symmetric _↔_
  ↔-trans : Transitive _↔_
  ```

* Added new isomorphisms to `Function.Properties.Inverse`:
  ```agda
  ↔-fun : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
  ```
