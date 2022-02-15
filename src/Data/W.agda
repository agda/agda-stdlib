------------------------------------------------------------------------
-- The Agda standard library
--
-- W-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.W where

open import Level
open import Function.Base using (_$_; _∘_; const)
open import Data.Product using (_,_; -,_; proj₂)
open import Data.Container.Core using (Container; ⟦_⟧; Shape; Position; _⇒_; ⟪_⟫)
open import Data.Container.Relation.Unary.All using (□; all)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    s p s₁ s₂ p₁ p₂ ℓ : Level
    C : Container s p
    C₁ : Container s₁ p₁
    C₂ : Container s₂ p₂

-- The family of W-types.

data W (C : Container s p) : Set (s ⊔ p) where
  sup : ⟦ C ⟧ (W C) → W C

sup-injective₁ : ∀ {s t : Shape C} {f : Position C s → W C} {g} →
                 sup (s , f) ≡ sup (t , g) → s ≡ t
sup-injective₁ refl = refl

-- See also Data.W.WithK.sup-injective₂.

-- Projections.

head : W C → Shape C
head (sup (x , f)) = x

tail : (x : W C) → Position C (head x) → W C
tail (sup (x , f)) = f

-- map

map : (m : C₁ ⇒ C₂) → W C₁ → W C₂
map m (sup (x , f)) = sup (⟪ m ⟫ (x , λ p → map m (f p)))

-- induction

module _ (P : W C → Set ℓ)
         (alg : ∀ {t} → □ C P t → P (sup t)) where

 induction : (w : W C) → P w
 induction (sup (s , f)) = alg $ all (induction ∘ f)

module _ {P : Set ℓ} (alg : ⟦ C ⟧ P → P) where

 foldr : W C → P
 foldr = induction (const P) (alg ∘ -,_ ∘ □.proof)

-- If Position is always inhabited, then W_C is empty.

inhabited⇒empty : (∀ s → Position C s) → ¬ W C
inhabited⇒empty b = foldr ((_$ b _) ∘ proj₂)
