------------------------------------------------------------------------
-- The Agda standard library
--
-- Sized W-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Data.W.Sized where

open import Level
open import Size
open import Function.Base using (_$_; _∘_; const)
open import Data.Product using (_,_; -,_; proj₂)
open import Data.Container.Core as Container using (Container; ⟦_⟧; Shape; Position; _⇒_; ⟪_⟫)
open import Data.Container.Relation.Unary.All using (□; all)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    i : Size
    s p s₁ s₂ p₁ p₂ ℓ : Level
    C : Container s p
    C₁ : Container s₁ p₁
    C₂ : Container s₂ p₂

-- The family of W-types.

data W (C : Container s p) : Size → Set (s ⊔ p) where
  sup : ⟦ C ⟧ (W C i) → W C (↑ i)

sup-injective₁ : ∀ {s t : Shape C} {f : Position C s → W C i} {g} →
                 sup (s , f) ≡ sup (t , g) → s ≡ t
sup-injective₁ refl = refl

-- See also Data.W.WithK.sup-injective₂.

-- Projections.

head : W C i → Shape C
head (sup (x , f)) = x

tail : (x : W C i) → Position C (head x) → W C i
tail (sup (x , f)) = f

-- map

map : (m : C₁ ⇒ C₂) → W C₁ i → W C₂ i
map m (sup c) = sup (⟪ m ⟫ (Container.map (map m) c))

-- induction

module _ (P : W C ∞ → Set ℓ)
         (alg : ∀ {t} → □ C P t → P (sup t)) where

 induction : (w : W C _) → P w
 induction (sup (s , f)) = alg $ all (induction ∘ f)

module _ {P : Set ℓ} (alg : ⟦ C ⟧ P → P) where

 foldr : W C _ → P
 foldr = induction (const P) (alg ∘ -,_ ∘ □.proof)

-- If Position is always inhabited, then W_C is empty.

inhabited⇒empty : (∀ s → Position C s) → ¬ W C i
inhabited⇒empty b = foldr ((_$ b _) ∘ proj₂)
