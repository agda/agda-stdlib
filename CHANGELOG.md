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

* In `Algebra.Apartness.Structures`, renamed `sym` from `IsApartnessRelation`
  to `#-sym` in order to avoid overloaded projection. The field names
  `irrefl` and `cotrans` are similarly renamed for the sake of consistency.

Non-backwards compatible changes
--------------------------------

* The definitions of `Algebra.Structures.IsHeyting*` and
  `Algebra.Bundles.Heyting*` have been refactored, together
  with that of `Relation.Binary.Definitions.Tight` on which they depend.
  Specifically:
  - `Tight _≈_ _#_` has been redefined as `∀ x y → ¬ x # y → x ≈ y`,
    dropping the redundant second conjunct, because it is equivalent to
    `Irreflexive _≈_ _#_`.
  - new definitions: `(Is)TightApartnessRelation` structure/bundle, exploiting
    the above redefinition.
  - the definition of `HeytingCommutativeRing` now drops the properties of
    invertibility, in favour of moving them to `HeytingField`.
  - both `Heyting*` algebraic structure/bundles have been redefined to base
    off an underlying `TightApartnessRelation`.

* [issue #2547](https://github.com/agda/agda-stdlib/issues/2547) The names of the *implicit* binders in the following definitions have been rectified to be consistent with those in the rest of `Relation.Binary.Definitions`: `Transitive`, `Antisym`, and `Antisymmetric`.

* [Issue #2548](https://github.com/agda/agda-stdlib/issues/2458) Consistent with other names (such as `∙-cong`, `ε-homo` etc.) in `Algebra.*`, the field name of the basic homomorphism property in `Algebra.Morphism.Structures.IsMagmaHomomorphism` has been renamed from `homo` to `∙-homo`.

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Apartness.Properties.HeytingCommutativeRing`:
  ```agda
  x-0≈x  ↦   Algebra.Properties.Ring.x-0#≈x
  #-sym  ↦   Algebra.Apartness.Structures.IsHeytingCommutativeRing.#-sym
  ```

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

* `Algebra.Apartness.Properties.HeytingField`, refactoring the existing
  `Algebra.Apartness.Properties.HeytingCommutativeRing`.

* `Codata.Guarded.Stream.Relation.Unary.Linked` for a proof that each pair
  of consecutive elements of a stream are related.

Additions to existing modules
-----------------------------

* In `Algebra.Apartness.Bundles.HeytingCommutativeRing`:
  ```agda
  TightApartnessRelation c ℓ₁ ℓ₂ : Set _
  ```

* In `Algebra.Apartness.Structures.IsHeytingCommutativeRing`:
  ```agda
  IsTightApartnessRelation _≈_ _#_ : Set _
  ```

* In `Algebra.Properties.AbelianGroup`:
  ```agda
  x-ε≈x : RightIdentity ε _-_
  ```

* In `Algebra.Properties.RingWithoutOne`:
  ```agda
  x-0#≈x : RightIdentity 0# _-_
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```agda
  ≄-apartnessRelation        : ApartnessRelation _ _ _
  ≄-isTightApartnessRelation : IsTightApartnessRelation _≃_ _≄_
  ≄-tightApartnessRelation   : TightApartnessRelation _ _ _
  ```

* In `Relation.Binary.Properties.DecSetoid`:
  ```agda
  ≉-isTightApartnessRelation : IsTightApartnessRelation _≈_ _#_
  ≉-tightApartnessRelation   : TightApartnessRelation _ _ _
  ```
  Additionally,
  ```agda
  ≉-tight : Tight _≈_ _≉_
  ```
  has been redefined to reflect the change in the definition of `Tight`.
