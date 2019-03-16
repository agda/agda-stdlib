------------------------------------------------------------------------
-- The Agda standard library
--
-- W-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.W where

open import Level
open import Function
open import Data.Product hiding (map)
open import Data.Container.Core hiding (map)
open import Data.Container.Relation.Unary.All using (□; all)
open import Relation.Nullary
open import Agda.Builtin.Equality

-- The family of W-types.

data W {s p} (C : Container s p) : Set (s ⊔ p) where
  sup : ⟦ C ⟧ (W C) → W C

module _ {s p} {C : Container s p} {s : Shape C} {f : Position C s → W C} where

 sup-injective₁ : ∀ {t g} → sup (s , f) ≡ sup (t , g) → s ≡ t
 sup-injective₁ refl = refl

 -- See also Data.W.WithK.sup-injective₂.

-- Projections.

module _ {s p} {C : Container s p} where

  head : W C → Shape C
  head (sup (x , f)) = x

  tail : (x : W C) → Position C (head x) → W C
  tail (sup (x , f)) = f

-- map

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         (m : C₁ ⇒ C₂) where

  map : W C₁ → W C₂
  map (sup (x , f)) = sup (⟪ m ⟫ (x , λ p → map (f p)))

-- induction

module _ {s p ℓ} {C : Container s p} (P : W C → Set ℓ)
         (alg : ∀ {t} → □ C P t → P (sup t)) where

 induction : (w : W C) → P w
 induction (sup (s , f)) = alg $ all (induction ∘ f)

module _ {s p ℓ} {C : Container s p} (open Container C)
         {P : Set ℓ} (alg : ⟦ C ⟧ P → P) where

 foldr : W C → P
 foldr = induction (const P) (alg ∘ -,_ ∘ □.proof)

-- If Position is always inhabited, then W_C is empty.

module _ {s p} {C : Container s p} where

  inhabited⇒empty : (∀ s → Position C s) → ¬ W C
  inhabited⇒empty b = foldr ((_$ b _) ∘ proj₂)
