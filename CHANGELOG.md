Version 3.0
===========

The library has been tested using Agda 2.8.0.

Highlights
----------

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

Non-backwards compatible changes
--------------------------------

* The definition of `Adjoint` in `Relation.Binary.Definitions` has been altered
  to be the conjunction of two universally quantified `Half*Adjoint` properties,
  rather than to be a universally quantified conjunction, for better compatibility
  with `Function.Definitions`.

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Data.Fin.Properties`:
  ```agda
  _≟_      ↦  _≡?_
  inj⇒≟    ↦  inj⇒≡?
  ≟-≡      ↦  ≡?-≡
  ≟-≡-refl ↦  ≡?-≡-refl
  ≟-≢     ↦  ≡?-≢
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

New modules
-----------

Additions to existing modules
-----------------------------

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

