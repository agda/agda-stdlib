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

* The notation for `Decidable` relations has been (partially) standardised: thus
  - `_≡?_` (at `infix 4`) for `DecidableEquality`
  - `_≈?_` (ditto.) for the fieldname of the general `IsDecEquivalence`

  Despite being non-backwards compatible, because a fieldname has changed, the
  old notation `_≟_` (which was used for both of the above) has been retained,
  but deprecated. This leads to a large amount of (trivial) deprecations, in
  addition to the substantive one under `Relation.Binary.Structures`, and in
  `Data.{Nat|Fin}.Properties` for the concrete datatypes. These deprecations
  are summarised below, but are not each documented for each affected module.

* [issue #2541](https://github.com/agda/agda-stdlib/issues/2541)
  The definition of `Adjoint` in `Relation.Binary.Definitions` has been altered
  to be the conjunction of two universally quantified `Half*Adjoint` properties,
  rather than to be a universally quantified conjunction, for better compatibility
  with `Function.Definitions`.

* [issue #2547](https://github.com/agda/agda-stdlib/issues/2547)
  The names of the *implicit* binders in the following definitions have been
  rectified to be consistent with the rest of `Relation.Binary.Definitions`:
  `Transitive`, `Antisym`, and `Antisymmetric`.

* [Issue #2548](https://github.com/agda/agda-stdlib/issues/2458)
  Consistent with other names (such as `∙-cong`, `ε-homo` etc.) in
  `Algebra.*`, the field name of the basic homomorphism property `homo` in
  `Algebra.Morphism.Structures.IsMagmaHomomorphism` has been renamed to `∙-homo`.


* [Issue #3022](https://github.com/agda/agda-stdlib/issues/3022)
  The previous development of rose trees has been refactored to make
  the definitions `safe` wrt termination checking etc. by avoiding
  the use of `sized-types`, at the cost of a little extra plumbing.
  ```
  Data.Tree.Rose
  Data.Tree.Rose.Properties
  Data.Tree.Rose.Show
  ```

Minor improvements
------------------

* [Issue #2502](https://github.com/agda/agda-stdlib/issues/2502) The module
  `Algebra.Consequences.Base` now takes the underlying equality relation as
  an additional top-level parameter, with slightly improved ergonomics wrt
  subsequent imports by clients, as well as streamlined internals. Moreover,
  it now has the implicit parameters of its internal modules lifted out as
  global `variable`s.

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
  ≟-≢      ↦  ≡?-≢
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

* A namespace for the (unsafe) use of `sized-types` to define rose trees
  and their associated operations, previously defined under `Data.Tree`,
  with the intention of migrating all such uses of sized datatypes here.
  ```
  Data.Sized
  Data.Sized.Tree
  ```
  Correspondingly, the previous development of rose trees has been refactored
  to make the definitions `safe` wrt termination checking etc.
  ```
  Data.Tree.Rose
  Data.Tree.Rose.Properties
  Data.Tree.Rose.Show
  ```

Additions to existing modules
-----------------------------

* In `Data.Bool.Properties`:
  ```agda
  ∨-monoid : Monoid 0ℓ 0ℓ
  ∧-monoid : Monoid 0ℓ 0ℓ
  ```

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

* In `Data.Vec.Properties`:
  ```agda
  lookup-head : (xs : Vec A (suc n)) → lookup xs zero ≡ head xs
  lookup-tail : (xs : Vec A (suc n)) → lookup xs (suc i) ≡ lookup (tail xs) i
  ```

* In `Function.Consequences`:
  ```agda
  inverseˡ⇒halfLeftAdjoint  : Inverseˡ ≈₁ ≈₂ f f⁻¹ → HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹
  halfLeftAdjoint⇒inverseˡ  : HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₁ ≈₂ f f⁻¹
  inverseˡ⇒halfRightAdjoint : Symmetric ≈₁ → Symmetric ≈₂ →
                              Inverseʳ ≈₁ ≈₂ f f⁻¹ → HalfRightAdjoint ≈₁ ≈₂ f f⁻¹
  halfRightAdjoint⇒inverseˡ : Symmetric ≈₁ → Symmetric ≈₂ →
                              HalfRightAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₁ ≈₂ f f⁻¹
  inverseᵇ⇒adjoint          : Symmetric ≈₁ → Symmetric ≈₂ →
                              Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Adjoint ≈₁ ≈₂ f f⁻¹
  adjoint⇒inverseᵇ          : Symmetric ≈₁ → Symmetric ≈₂ →
                              Adjoint ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₁ ≈₂ f f⁻¹
  ```

* In `Function.Consequences.Setoid`:
  ```agda
  inverseˡ⇒halfLeftAdjoint  : Inverseˡ ≈₁ ≈₂ f f⁻¹ → HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹
  halfLeftAdjoint⇒inverseˡ  : HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₁ ≈₂ f f⁻¹
  inverseʳ⇒halfRightAdjoint : Inverseʳ ≈₁ ≈₂ f f⁻¹ → HalfRightAdjoint ≈₁ ≈₂ f f⁻¹
  halfRightAdjoint⇒inverseʳ : HalfRightAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₁ ≈₂ f f⁻¹
  inverseᵇ⇒adjoint          : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Adjoint ≈₁ ≈₂ f f⁻¹
  adjoint⇒inverseᵇ          : Adjoint ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₁ ≈₂ f f⁻¹
  ```

* In `Relation.Binary.Definitions`:
  ```agda
  HalfLeftAdjoint : Rel A ℓ₁ → Rel B ℓ₂ → (A → B) → (B → A) → Set _
  HalfLeftAdjoint _≤_ _⊑_ f g = ∀ {x y} → (x ≤ g y → f x ⊑ y)

  HalfRightAdjoint : Rel A ℓ₁ → Rel B ℓ₂ → (A → B) → (B → A) → Set _
  HalfRightAdjoint _≤_ _⊑_ f g = ∀ {x y} → (f x ⊑ y → x ≤ g y)
  ```
