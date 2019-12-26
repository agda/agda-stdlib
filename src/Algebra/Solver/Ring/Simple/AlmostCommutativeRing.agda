{-# OPTIONS --without-K --safe #-}

module Algebra.Solver.Ring.Simple.AlmostCommutativeRing where

open import Algebra
open import Algebra.Morphism
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Level
open import Function
open import Relation.Binary
import Algebra.Operations.Ring  as Exp
{-
record AlmostCommutativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  infixr 8 _^_
  field
    Carrier                 : Set c
    _≈_                     : Rel Carrier ℓ
    _+_                     : Op₂ Carrier
    _*_                     : Op₂ Carrier
    -_                      : Op₁ Carrier
    0#                      : Carrier
    0≟_                     : (x : Carrier) → Maybe (0# ≈ x)
    1#                      : Carrier
    isAlmostCommutativeRing : IsAlmostCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsAlmostCommutativeRing isAlmostCommutativeRing hiding (refl) public

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring = record
    { isCommutativeSemiring = isCommutativeSemiring
    }

  open CommutativeSemiring commutativeSemiring public
    using
    ( +-semigroup; +-monoid; +-commutativeMonoid
    ; *-semigroup; *-monoid; *-commutativeMonoid
    ; semiring
    )

  rawRing : RawRing c ℓ
  rawRing = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }

  _^_ : Carrier → ℕ → Carrier
  _^_ = Exp._^_ rawRing
  {-# NOINLINE _^_ #-}

  refl : ∀ {x} → x ≈ x
  refl = IsAlmostCommutativeRing.refl isAlmostCommutativeRing

flipped : ∀ {c ℓ} → AlmostCommutativeRing c ℓ → AlmostCommutativeRing c ℓ
flipped rng = record
  { Carrier = Carrier
  ; _≈_ = _≈_
  ; _+_ = flip _+_
  ; _*_ = flip _*_
  ; -_  = -_
  ; 0#  = 0#
  ; 0≟_ = 0≟_
  ; 1#  = 1#
  ; isAlmostCommutativeRing = record
    { -‿cong       = -‿cong
    ; -‿*-distribˡ = λ x y → *-comm y (- x) ⟨ trans ⟩ (-‿*-distribˡ x y ⟨ trans ⟩ -‿cong (*-comm x y))
    ; -‿+-comm     = flip -‿+-comm
    ; isCommutativeSemiring = record
      { +-isCommutativeMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong        = flip +-cong
            }
          ; assoc = λ x y z → sym (+-assoc z y x)
          }
        ; identityˡ = +-identityʳ
        ; comm = flip +-comm
        }
      ; *-isCommutativeMonoid = record 
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong        = flip *-cong
            }
          ; assoc = λ x y z → sym (*-assoc z y x)
          }
          ; identityˡ = *-identityʳ
          ; comm      = flip *-comm
        }
      ; distribʳ = λ x y z → distribˡ _ _ _
      ; zeroˡ = zeroʳ
      }
    }
  } where open AlmostCommutativeRing rng



-- A homomorphism induces a notion of equivalence on the raw ring.

Induced-equivalence :
  ∀ {c₁ c₂ c₃ ℓ} {Coeff : RawRing c₁ c₂} {R : AlmostCommutativeRing c₃ ℓ} →
  Coeff -Raw-AlmostCommutative⟶ R → Rel (RawRing.Carrier Coeff) ℓ
Induced-equivalence {R = R} morphism a b = ⟦ a ⟧ ≈ ⟦ b ⟧
  where
  open AlmostCommutativeRing R
  open _-Raw-AlmostCommutative⟶_ morphism

------------------------------------------------------------------------
-- Conversions

-- Commutative rings are almost commutative rings.

fromCommutativeRing : ∀ {r₁ r₂} → (CR : CommutativeRing r₁ r₂) →
                      (∀ x → Maybe ((CommutativeRing._≈_ CR) (CommutativeRing.0# CR) x)) →
                      AlmostCommutativeRing _ _
fromCommutativeRing CR 0≟_ = record
  { isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿cong                = -‿cong
      ; -‿*-distribˡ          = -‿*-distribˡ
      ; -‿+-comm              = ⁻¹-∙-comm
      }
  ; 0≟_ = 0≟_
  }
  where
  open CommutativeRing CR
  import Algebra.Properties.Ring as R; open R ring
  import Algebra.Properties.AbelianGroup as AG; open AG +-abelianGroup

fromCommutativeSemiring : ∀ {r₁ r₂} → (CS : CommutativeSemiring r₁ r₂) →
                          (∀ x → Maybe ((CommutativeSemiring._≈_ CS) (CommutativeSemiring.0# CS) x)) →
                          AlmostCommutativeRing _ _
fromCommutativeSemiring CS 0≟_ = record
  { -_                      = id
  ; isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿cong                = id
      ; -‿*-distribˡ          = λ _ _ → refl
      ; -‿+-comm              = λ _ _ → refl
      }
  ; 0≟_ = 0≟_
  }
  where open CommutativeSemiring CS
-}
