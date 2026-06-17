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

* Fix a bug in `Data.List.Base`'s `linesBy` (the last empty line would be dropped).

Non-backwards compatible changes
--------------------------------

* [issue #2547](https://github.com/agda/agda-stdlib/issues/2547) The names of the *implicit* binders in the following definitions have been rectified to be consistent with those in the rest of `Relation.Binary.Definitions`: `Transitive`, `Antisym`, and `Antisymmetric`.

* [Issue #2548](https://github.com/agda/agda-stdlib/issues/2458) Consistent with other names (such as `∙-cong`, `ε-homo` etc.) in `Algebra.*`, the field name of the basic homomorphism property in `Algebra.Morphism.Structures.IsMagmaHomomorphism` has been renamed from `homo` to `∙-homo`.

Minor improvements
------------------

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

* `Codata.Guarded.Stream.Relation.Unary.Linked` for a proof that each pair
  of consecutive elements of a stream are related.

* `Data.Bool.ListAction.Properties` for properties of conjunction and
  disjuntion of lists.

* A new type of lists that grow on the right.
  This is typically useful to model contexts of typing rules
  or type accumulators that need to be reversed in the base case.
  ```
  Data.SnocList.Base
  ```

Additions to existing modules
-----------------------------

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
