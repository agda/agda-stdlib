Version 3.0
===========

The library has been tested using Agda 2.8.0.

Highlights
----------

* Modules that previously used `--cubical-compatible` once again use `--without-K`.

* The notation for `Decidable` relations has been (partially) standardised: thus
  - `_≡?_` (at `infix 4`) for `DecidableEquality`
  - `_≈?_` (ditto.) for the general `IsDecEquivalence`

  At present, the old fieldname `_≟_` has been retained, in order to avoid
  a non-backwards compatible/breaking change of fieldname, which will plan
  to do in Version 3.0, with accompanying deprecation of that name, against
  its eventual removal in subsequent versions.

  The change leads to a number of (trivial) renamings/deprecations, others more
  substantive in `Data.{Nat|Fin}.Properties` for the concrete datatypes, which
  are summarised below, but are not each documented for all affected modules.

Bug-fixes
---------

* Fix a bug in `Data.List.Base`'s `linesBy` (the last empty line would be dropped).

Non-backwards compatible changes
--------------------------------

* A major overhaul of the `Function` hierarchy sees the systematic development
  and use of the theory of the left inverse `from` to a given `Surjective` function
  `to`, as a consequence of which we can achieve full symmetry of `Bijection`, in
  `Function.Properties.Bijection`/`Function.Construct.Symmetry`, rather than the
  restricted versions considered to date. NB. this is non-backwards compatible
  because the types of various properties are now sharper, and some previous lemmas
  are no longer present, due to the complexity their deprecation would entail.
  Specifically:
  - `Function.Construct.Symmetry.isBijection` no longer requires the hypothesis `Congruent ≈₂ ≈₁ f⁻¹` for the function `f⁻¹ = B.from`.
  - `Function.Construct.Symmetry.isBijection-≡` is now redundant, as an instance of the above lemma, so has been deleted.
  - Similarly, `Function.Construct.Symmetry.bijection` no longer requires a `Congruent` hypothesis, and `Function.Construct.Symmetry.bijection-≡` is now redundant/deleted.
  - `Function.Properties.Bijection.sym-≡` is now redundant as an instance of a fully general symmetry property `Function.Properties.Bijection.sym`, hence also deleted.

* [issue #2547](https://github.com/agda/agda-stdlib/issues/2547)
  The names of the *implicit* binders in the following definitions have been
  rectified to be consistent with the rest of `Relation.Binary.Definitions`:
  `Transitive`, `Antisym`, and `Antisymmetric`.

* [Issue #2548](https://github.com/agda/agda-stdlib/issues/2458)
  Consistent with other names (such as `∙-cong`, `ε-homo` etc.) in
  `Algebra.*`, the field name of the basic homomorphism property `homo` in
  `Algebra.Morphism.Structures.IsMagmaHomomorphism` has been renamed to `∙-homo`.

Minor improvements
------------------

* The definitions in `Function.Consequences.Propositional` of the form `strictlyX⇒X` have been streamlined via pattern-matching on `refl`, rather than defined by delegation to `Function.Consequences.Setoid` and the use of `cong`.

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Morphism.Structures`:
  ```agda
  homo  ↦  ∙-homo
  ```

* In `Data.Fin.Properties`:
  ```agda
  _≟_      ↦  _≡?_
  inj⇒≟    ↦  inj⇒≡?
  ≟-≡      ↦  ≡?-≡
  ≟-≡-refl ↦  ≡?-≡-refl
  ≟-≢     ↦  ≡?-≢
  ```

* In `Data.Integer.GCD`:
  ```agda
  gcd[0,0]≡0 ↦ gcd[i,i]≡∣i∣
  ```

* In `Data.Nat.GCD`:
  ```agda
  gcd[0,0]≡0 ↦ gcd[n,n]≡n
  ```

* In `Data.Nat.Properties`:
  ```agda
  _≟_       ↦   _≡?_
  ≟-diag    ↦   ≡?-≡
  ≟-≡       ↦   ≡?-≢
  ≟?-≡-refl ↦ ≡?-≡-refl
  ```

* In `Effect.Monad.Partiality`:
  ```agda
  _≟-Kind_     ↦   _≡?-Kind_
  ```

* In `Reflection.AST.AlphaEquality`:
  ```agda
  ≟⇒α     ↦   ≡?⇒α
  ```

* In `Relation.Binary.PropositionalEquality`:
  ```agda
  ≡-≟-identity     ↦   ≡-≡?-identity
  ≢-≟-identity     ↦   ≢-≡?-identity
  ```

* In `Relation.Nary`:
  ```agda
  ≟-mapₙ     ↦   ≡?-mapₙ
  ```

* In `Function.Bundles.IsSurjection`:
  ```agda
  to⁻      ↦  Function.Structures.IsSurjection.from
  to∘to⁻   ↦  Function.Structures.IsSurjection.strictlyInverseˡ
  ```

* In `Function.Properties.Surjection`:
  ```agda
  injective⇒to⁻-cong   ↦  Function.Bundles.Bijection.from-cong
  ```

New modules
-----------

* `Codata.Guarded.Stream.Relation.Unary.Linked` for a proof that each pair
  of consecutive elements of a stream are related.

* `Data.Bool.ListAction.Properties` for properties of conjunction and
  disjunction of lists.

* A new type of lists that grow on the right.
  This is typically useful to model contexts of typing rules
  or type accumulators that need to be reversed in the base case.
  ```
  Data.SnocList.Base
  ```

Additions to existing modules
-----------------------------

* In `Data.Integer.GCD`:
  ```agda
  gcd[i,i]≡∣i∣ : ∀ i → gcd i i ≡ + ∣i∣
  ```

* In `Data.Nat.GCD`:
  ```agda
  gcd[n,n]≡n : ∀ n → gcd n n ≡ n
  ```

* In `Data.Rational.Properties`:
  ```agda
  ↥[i/1]≡i  : (i : ℤ) → ↥ (i / 1) ≡ i
  ↧ₙ[i/1]≡1 : (i : ℤ) → ↧ₙ (i / 1) ≡ 1
  n/n≡1 : ∀ (n : ℕ) .{{_ : ℕ.NonZero n}} → + n / n ≡ 1ℚ
  -i/n≡-[i/n] : ∀ (i : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n}} →
                ℤ.- i / n ≡ - (i / n)
  *-cancelˡ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (p ℕ.* r)}} →
                (+ p ℤ.* q) / (p ℕ.* r) ≡ q / r
  *-cancelʳ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (r ℕ.* p)}} →
                (q ℤ.* + p) / (r ℕ.* p) ≡ q / r
  i/n+j/n≡[i+j]/n : ∀ (i j : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n }} →
                    i / n + j / n ≡ (i ℤ.+ j) / n
  ```

* In `Function.Bundles.Bijection`:
  ```agda
  from             : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ to from
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
  inverseʳ         : Inverseʳ _≈₁_ _≈₂_ to from
  strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from
  ```

* In `Function.Bundles.LeftInverse`:
  ```agda
  surjective       : Surjective _≈₁_ _≈₂_ to
  surjection       : Surjection From To
  ```

* In `Function.Bundles.RightInverse`:
  ```agda
  isInjection      : IsInjection to
  injective        : Injective _≈₁_ _≈₂_ to
  injection        : Injection From To
  ```

* In `Function.Bundles.Surjection`:
  ```agda
  from             : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ to from
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
  ```

* In `Function.Construct.Symmetry`:
  ```agda
  isBijection : IsBijection ≈₁ ≈₂ to → IsBijection ≈₂ ≈₁ from
  bijection   : Bijection R S → Bijection S R
  ```

* In `Function.Properties.Bijection`:
  ```agda
  sym : Bijection S T → Bijection T S
  ```

* In `Function.Structures.IsBijection`:
  ```agda
  from             : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ to from
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
  inverseʳ         : Inverseʳ _≈₁_ _≈₂_ to from
  strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from
  from-cong        : Congruent _≈₂_ _≈₁_ from
  from-injective   : Injective _≈₂_ _≈₁_ from
  from-surjective  : Surjective _≈₂_ _≈₁_ from
  from-bijective   : Bijective _≈₂_ _≈₁_ from
  ```

* In `Function.Structures.IsLeftInverse`:
  ```agda
  surjective : Surjective _≈₁_ _≈₂_ to
  ```

* In `Function.Structures.IsRightInverse`:
  ```agda
  injective   : Injective _≈₁_ _≈₂_ to
  isInjection : IsInjection to
  ```

* In `Function.Structures.IsSurjection`:
  ```agda
  from             : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ to from
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
  from-injective   : Injective _≈₂_ _≈₁_ from
