------------------------------------------------------------------------
-- The Agda standard library
--
-- Function Equality setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

module Function.Relation.Binary.Setoid.Equality {a₁ a₂ b₁ b₂ : Level}
  (From : Setoid a₁ a₂) (To : Setoid b₁ b₂) where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)

private
  module To = Setoid To
  module From = Setoid From

infix 4 _≈_
_≈_ : (f g : Func From To) → Set (a₁ ⊔ b₂)
f ≈ g = {x : From.Carrier} → f ⟨$⟩ x To.≈ g ⟨$⟩ x

refl : Reflexive _≈_
refl = To.refl

sym : Symmetric _≈_
sym = λ f≈g → To.sym f≈g

trans : Transitive _≈_
trans = λ f≈g g≈h → To.trans f≈g g≈h

setoid : Setoid _ _
setoid = record
  { Carrier = Func From To
  ; _≈_ = _≈_
  ; isEquivalence = record  -- need to η-expand else Agda gets confused
    { refl = λ {f} → refl {f}
    ; sym = λ {f} {g} → sym {f} {g}
    ; trans = λ {f} {g} {h} → trans {f} {g} {h}
    }
  }

-- most of the time, this infix version is nicer to use
infixr 9 _⇨_
_⇨_ : Setoid _ _
_⇨_ = setoid
