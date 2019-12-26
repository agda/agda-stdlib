------------------------------------------------------------------------
-- The Agda standard library
--
-- Commutative semirings with some additional structure ("almost"
-- commutative rings), used by the ring solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Solver.Ring.AlmostCommutativeRing where

open import Relation.Binary
open import Algebra
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Function
open import Level

open import Algebra.Structures public using (IsAlmostCommutativeRing)
open import Algebra.Bundles public using (AlmostCommutativeRing)
open import Algebra.Morphism public
  using (_-Raw-AlmostCommutative⟶_; -raw-almostCommutative⟶)

Induced-equivalence : ∀ {c₁ c₂ ℓ₁ ℓ₂} {Coeff : RawRing c₁ ℓ₁}
                      {R : AlmostCommutativeRing c₂ ℓ₂} →
                      Coeff -Raw-AlmostCommutative⟶ R →
                      Rel (RawRing.Carrier Coeff) ℓ₂
Induced-equivalence {R = R} morphism a b = ⟦ a ⟧ ≈ ⟦ b ⟧
  where
  open AlmostCommutativeRing R
  open _-Raw-AlmostCommutative⟶_ morphism

------------------------------------------------------------------------
-- Conversions

-- Commutative rings are almost commutative rings.

fromCommutativeRing : ∀ {r₁ r₂} → CommutativeRing r₁ r₂ → AlmostCommutativeRing r₁ r₂
fromCommutativeRing CR = record
  { isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿cong                = -‿cong
      ; -‿*-distribˡ          = -‿*-distribˡ
      ; -‿+-comm              = ⁻¹-∙-comm
      }
  }
  where
  open CommutativeRing CR
  import Algebra.Properties.Ring as R; open R ring
  import Algebra.Properties.AbelianGroup as AG; open AG +-abelianGroup

-- Commutative semirings can be viewed as almost commutative rings by
-- using identity as the "almost negation".

fromCommutativeSemiring : ∀ {r₁ r₂} → CommutativeSemiring r₁ r₂ → AlmostCommutativeRing _ _
fromCommutativeSemiring CS = record
  { -_                      = id
  ; isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿cong                = id
      ; -‿*-distribˡ          = λ _ _ → refl
      ; -‿+-comm              = λ _ _ → refl
      }
  }
  where open CommutativeSemiring CS
