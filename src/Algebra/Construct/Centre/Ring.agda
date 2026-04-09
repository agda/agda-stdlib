------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Ring
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
  using (Ring; CommutativeRing; Monoid; RawRing; RawMonoid)

module Algebra.Construct.Centre.Ring {c ℓ} (ring : Ring c ℓ) where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Consequences.Setoid using (zero⇒central)
open import Algebra.Morphism.Structures using (IsRingMonomorphism)
open import Algebra.Morphism.RingMonomorphism using (isRing)
open import Function.Base using (id)


private
  module X = Ring ring

open import Algebra.Properties.Ring ring using (-‿distribˡ-*; -‿distribʳ-*)
open import Relation.Binary.Reasoning.Setoid X.setoid as ≈-Reasoning


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Monoid

open import Algebra.Construct.Centre.Monoid X.*-monoid as Z public
  using (Centre; ι; ∙-comm)

-- Now, can define a commutative sub-Ring

domain : RawRing _ _
domain = record
  { _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0#
  ; 1# = 1#
  }
  where
  open RawMonoid Z.domain renaming (ε to 1#; _∙_ to _*_)
  _+_ : Op₂ Centre
  g + h = record
    { ι       = ι g X.+ ι h
    ; central = λ r → begin
      (ι g X.+ ι h) X.* r      ≈⟨ X.distribʳ _ _ _ ⟩
      ι g X.* r X.+ ι h X.* r  ≈⟨ X.+-cong (Centre.central g r) (Centre.central h r) ⟩
      r X.* ι g  X.+ r X.* ι h ≈⟨ X.distribˡ _ _ _ ⟨
      r X.* (ι g X.+ ι h)      ∎
    }
  -_ : Op₁ Centre
  - g = record
    { ι       = X.- ι g
    ; central = λ r → begin
      X.- ι g X.* r   ≈⟨ -‿distribˡ-* (ι g) r ⟨
      X.- (ι g X.* r) ≈⟨ X.-‿cong (Centre.central g r) ⟩
      X.- (r X.* ι g) ≈⟨ -‿distribʳ-* r (ι g) ⟩
      r  X.* X.- ι g  ∎
    }
  0# : Centre
  0# = record
    { ι = X.0#
    ; central = zero⇒central X.setoid {_∙_ = X._*_} X.zero
    }

isRingMonomorphism : IsRingMonomorphism domain X.rawRing ι
isRingMonomorphism = record
  { isRingHomomorphism = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = id }
            ; homo = λ _ _ → X.refl
            }
          ; ε-homo = X.refl
          }
        ; *-homo = λ _ _ → X.refl
        }
      ; 1#-homo = X.refl
      }
    ; -‿homo = λ _ → X.refl
    }
    ; injective = id
  }

-- Public export of the sub-X-homomorphisms

open IsRingMonomorphism isRingMonomorphism public
  using (isRingHomomorphism
        ; isSemiringHomomorphism
        ; isNearSemiringHomomorphism
        ; +-isMonoidHomomorphism
        ; +-isMagmaHomomorphism
        ; *-isMonoidHomomorphism
        ; *-isMagmaHomomorphism
        )

-- And hence a CommutativeRing

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { isCommutativeRing = record
    { isRing = isRing isRingMonomorphism X.isRing
    ; *-comm = ∙-comm
    }
  }

-- Public export of the sub-X-structures/bundles

open CommutativeRing commutativeRing public
  using (isCommutativeRing; isRing
        ; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
        ; +-invertibleMagma; +-invertibleUnitalMagma
        ; +-rawMonoid; +-monoid; +-commutativeMonoid
        ; +-group; +-abelianGroup
        ; +-semigroup; +-commutativeSemigroup
        ; *-rawMagma; *-magma; *-commutativeMagma
        ; *-semigroup; *-commutativeSemigroup
        ; *-rawMonoid; *-monoid; *-commutativeMonoid
        ; nearSemiring
        ; semiringWithoutOne; commutativeSemiringWithoutOne
        ; semiringWithoutAnnihilatingZero; semiring
        )

-- Public export of the bundle

Z[_] = commutativeRing
