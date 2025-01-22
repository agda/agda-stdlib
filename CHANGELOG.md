Version 2.3-dev
===============

The library has been tested using Agda 2.7.0 and 2.7.0.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Data.List.Base`:
  ```agda
  and       ↦  Data.Bool.ListAction.and
  or        ↦  Data.Bool.ListAction.or
  any       ↦  Data.Bool.ListAction.any
  all       ↦  Data.Bool.ListAction.all
  ```

New modules
-----------

* `Data.List.Base.{and|or|any|all}` and their properties have been lifted out into `Data.Bool.ListAction`.

Additions to existing modules
-----------------------------

* In `Algebra.Construct.Pointwise`:
  ```agda
  isNearSemiring                  : IsNearSemiring _≈_ _+_ _*_ 0# →
                                    IsNearSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#)
  isSemiringWithoutOne            : IsSemiringWithoutOne _≈_ _+_ _*_ 0# →
                                    IsSemiringWithoutOne (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#)
  isCommutativeSemiringWithoutOne : IsCommutativeSemiringWithoutOne _≈_ _+_ _*_ 0# →
                                    IsCommutativeSemiringWithoutOne (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#)
  isCommutativeSemiring           : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1# →
                                    IsCommutativeSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isIdempotentSemiring            : IsIdempotentSemiring _≈_ _+_ _*_ 0# 1# →
                                    IsIdempotentSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isKleeneAlgebra                 : IsKleeneAlgebra _≈_ _+_ _*_ _⋆ 0# 1# →
                                    IsKleeneAlgebra (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₁ _⋆) (lift₀ 0#) (lift₀ 1#)
  isQuasiring                     : IsQuasiring _≈_ _+_ _*_ 0# 1# →
                                    IsQuasiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isCommutativeRing               : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1# →
                                    IsCommutativeRing (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₁ -_) (lift₀ 0#) (lift₀ 1#)
  commutativeMonoid               : CommutativeMonoid c ℓ → CommutativeMonoid (a ⊔ c) (a ⊔ ℓ)
  nearSemiring                    : NearSemiring c ℓ → NearSemiring (a ⊔ c) (a ⊔ ℓ)
  semiringWithoutOne              : SemiringWithoutOne c ℓ → SemiringWithoutOne (a ⊔ c) (a ⊔ ℓ)
  commutativeSemiringWithoutOne   : CommutativeSemiringWithoutOne c ℓ → CommutativeSemiringWithoutOne (a ⊔ c) (a ⊔ ℓ)
  commutativeSemiring             : CommutativeSemiring c ℓ → CommutativeSemiring (a ⊔ c) (a ⊔ ℓ)
  idempotentSemiring              : IdempotentSemiring c ℓ → IdempotentSemiring (a ⊔ c) (a ⊔ ℓ)
  kleeneAlgebra                   : KleeneAlgebra c ℓ → KleeneAlgebra (a ⊔ c) (a ⊔ ℓ)
  quasiring                       : Quasiring c ℓ → Quasiring (a ⊔ c) (a ⊔ ℓ)
  commutativeRing                 : CommutativeRing c ℓ → CommutativeRing (a ⊔ c) (a ⊔ ℓ)
  ```
