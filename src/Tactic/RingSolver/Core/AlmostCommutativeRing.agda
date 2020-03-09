------------------------------------------------------------------------
-- The Agda standard library
--
-- Almost commutative rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver.Core.AlmostCommutativeRing where

open import Level
open import Relation.Binary
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Structures using (IsCommutativeSemiring)
open import Algebra.Definitions
open import Algebra.Bundles using (RawRing; CommutativeRing; CommutativeSemiring)
import Algebra.Morphism as Morphism
open import Function
open import Level
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)

record IsAlmostCommutativeRing
         {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
         (_+_ _*_ : A → A → A) (-_ : A → A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#
    -‿cong                : -_ Preserves _≈_ ⟶ _≈_
    -‿*-distribˡ          : ∀ x y → ((- x) * y)     ≈ (- (x * y))
    -‿+-comm              : ∀ x y → ((- x) + (- y)) ≈ (- (x + y))

  open IsCommutativeSemiring isCommutativeSemiring public

import Algebra.Operations.Ring as Exp

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
    isAlmostCommutativeRing :
      IsAlmostCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsAlmostCommutativeRing isAlmostCommutativeRing hiding (refl) public
  open import Data.Nat.Base as ℕ using (ℕ)

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring = record
    { isCommutativeSemiring = isCommutativeSemiring
    }

  open CommutativeSemiring commutativeSemiring public
    using ( +-semigroup; +-monoid; +-commutativeMonoid
          ; *-semigroup; *-monoid; *-commutativeMonoid
          ; semiring
          )

  rawRing : RawRing _ _
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

record _-Raw-AlmostCommutative⟶_
         {r₁ r₂ r₃ r₄}
         (From : RawRing r₁ r₂)
         (To : AlmostCommutativeRing r₃ r₄) : Set (r₁ ⊔ r₂ ⊔ r₃ ⊔ r₄) where
  private
    module F = RawRing From
    module T = AlmostCommutativeRing To
  open Morphism.Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦_⟧    : Morphism
    +-homo : Homomorphic₂ ⟦_⟧ F._+_ T._+_
    *-homo : Homomorphic₂ ⟦_⟧ F._*_ T._*_
    -‿homo : Homomorphic₁ ⟦_⟧ F.-_  T.-_
    0-homo : Homomorphic₀ ⟦_⟧ F.0#  T.0#
    1-homo : Homomorphic₀ ⟦_⟧ F.1#  T.1#

-raw-almostCommutative⟶
  : ∀ {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂) →
    AlmostCommutativeRing.rawRing R -Raw-AlmostCommutative⟶ R
-raw-almostCommutative⟶ R = record
  { ⟦_⟧    = id
  ; +-homo = λ _ _ → refl
  ; *-homo = λ _ _ → refl
  ; -‿homo = λ _ → refl
  ; 0-homo = refl
  ; 1-homo = refl
  }
  where open AlmostCommutativeRing R

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

fromCommutativeRing : ∀ {r₁ r₂} (CR : CommutativeRing r₁ r₂) →
                      (open CommutativeRing CR) →
                      (∀ x → Maybe (0# ≈ x)) →
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
  open import Algebra.Properties.Ring ring
  open import Algebra.Properties.AbelianGroup +-abelianGroup

fromCommutativeSemiring : ∀ {r₁ r₂} (CS : CommutativeSemiring r₁ r₂)
                          (open CommutativeSemiring CS) →
                          (∀ x → Maybe (0# ≈ x)) →
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
