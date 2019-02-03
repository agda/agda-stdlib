------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on M-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.M.Properties where

open import Level
open import Size
open import Codata.Thunk using (Thunk; force)
open import Codata.M
open import Codata.M.Bisimilarity
open import Data.Container as C hiding (map) renaming (module Morphism to Mp)
open import Data.Product as Prod using (_,_)
open import Data.Product.Properties
open import Function
import Relation.Binary.PropositionalEquality as P

module _ {s p} {C : Container s p} where

  map-id : ∀ {i} c → Bisim C i (map (Mp.id C) c) c
  map-id (inf (s , f)) = inf (P.refl , λ where p .force → map-id (f p .force))

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} where

  map-cong : ∀ {i} {f g : C₁ ⇒ C₂} →
             (∀ {X : Set (s₁ ⊔ p₁)} t → Eq C₂ {X = X} P._≡_ (⟪ f ⟫ t) (⟪ g ⟫ t)) →
             ∀ c₁ → Bisim C₂ i (map f c₁) (map g c₁)
  map-cong {f = f} {g} f≗g (inf t@(s , n)) with f≗g t
  ... | eqs , eqf = inf (eqs , λ where
     p .force {j} → P.subst (λ t → Bisim C₂ j (map f (n (position f p) .force))
                                              (map g (t .force)))
                    (eqf p)
                    (map-cong f≗g (n (position f p) .force)))

module _ {s₁ s₂ s₃ p₁ p₂ p₃} {C₁ : Container s₁ p₁}
         {C₂ : Container s₂ p₂} {C₃ : Container s₃ p₃} where

  map-compose : ∀ {i} {g : C₂ ⇒ C₃} {f : C₁ ⇒ C₂} c₁ →
                Bisim C₃ i (map (g Mp.∘ f) c₁) (map g $′ map f c₁)
  map-compose (inf (s , f)) = inf (P.refl , λ where p .force → map-compose (f _ .force))


module _ {s₁ s₂ p₁ p₂ s} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {S : Set s} {alg : S → ⟦ C₁ ⟧ S} {f : C₁ ⇒ C₂} where

  map-unfold : ∀ {i} s → Bisim C₂ i (map f (unfold alg s))
                                    (unfold (⟪ f ⟫ ∘′ alg) s)
  map-unfold s = inf (P.refl , λ where p .force → map-unfold _)
