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
open import Algebra.Morphism.Structures
open import Algebra.Morphism.RingMonomorphism using (isRing)
open import Function.Base using (id; const; _$_)


private
  module R = Ring ring
  module R* = Monoid R.*-monoid

open import Relation.Binary.Reasoning.Setoid R.setoid as ≈-Reasoning
open import Algebra.Properties.Ring ring using (-‿distribˡ-*; -‿distribʳ-*)


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Monoid

open import Algebra.Construct.Centre.Monoid R.*-monoid as Z public
  using (Center; ι; ∙-comm)

-- Now, can define a commutative sub-Ring

_+_ : Op₂ Center
g + h = record
  { ι       = ι g R.+ ι h
  ; central = λ r → begin
    (ι g R.+ ι h) R.* r      ≈⟨ R.distribʳ _ _ _ ⟩
    ι g R.* r R.+ ι h R.* r  ≈⟨ R.+-cong (Center.central g r) (Center.central h r) ⟩
    r R.* ι g  R.+ r R.* ι h ≈⟨ R.distribˡ _ _ _ ⟨
    r R.* (ι g R.+ ι h)      ∎
  }

-_ : Op₁ Center
- g = record
  { ι       = R.- ι g
  ; central = λ r → begin R.- ι g R.* r ≈⟨ -‿distribˡ-* (ι g) r ⟨
  R.- (ι g R.* r) ≈⟨ R.-‿cong (Center.central g r) ⟩
  R.- (r R.* ι g) ≈⟨ -‿distribʳ-* r (ι g) ⟩
  r  R.* R.- ι g ∎
  }

0# : Center
0# = record
  { ι = R.0#
  ; central = zero⇒central R.setoid {_∙_ = R._*_} R.zero
  }

domain : RawRing _ _
domain = record
  { _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0#
  ; 1# = 1#
  } where open RawMonoid Z.domain renaming (ε to 1#; _∙_ to _*_)

isRingHomomorphism : IsRingHomomorphism domain R.rawRing ι
isRingHomomorphism = record
  { isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = id }
          ; homo = λ _ _ → R.refl
          }
        ; ε-homo = R.refl
        }
      ; *-homo = λ _ _ → R.refl
      }
    ; 1#-homo = R.refl
    }
  ; -‿homo = λ _ → R.refl
  }

isRingMonomorphism : IsRingMonomorphism domain R.rawRing ι
isRingMonomorphism = record
  { isRingHomomorphism = isRingHomomorphism
  ; injective = id
  }

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { isCommutativeRing = record
    { isRing = isRing isRingMonomorphism R.isRing
    ; *-comm = ∙-comm
    }
  }

Z[_] = commutativeRing
