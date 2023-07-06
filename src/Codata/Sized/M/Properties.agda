------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on M-types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.M.Properties where

open import Level
open import Size
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.M
open import Codata.Sized.M.Bisimilarity
open import Data.Container.Core as C hiding (map)
import Data.Container.Morphism as Mp
open import Data.Product as Prod using (_,_)
open import Data.Product.Properties hiding (map-cong)
open import Function.Base using (_$′_; _∘′_)
import Relation.Binary.PropositionalEquality.Core as P
import Relation.Binary.PropositionalEquality.Properties as P

open import Data.Container.Relation.Binary.Pointwise using (_,_)
import Data.Container.Relation.Binary.Equality.Setoid as EqSetoid

private module Eq {a} (A : Set a) = EqSetoid (P.setoid A)
open Eq using (Eq)

module _ {s p} {C : Container s p} where

  map-id : ∀ {i} c → Bisim C i (map (Mp.id C) c) c
  map-id (inf (s , f)) = inf (P.refl , λ where p .force → map-id (f p .force))

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} where

  map-cong : ∀ {i} {f g : C₁ ⇒ C₂} →
             (∀ {X} t → Eq X C₂ (⟪ f ⟫ t) (⟪ g ⟫ t)) →
             ∀ c₁ → Bisim C₂ i (map f c₁) (map g c₁)
  map-cong {f = f} {g} f≗g (inf t@(s , n)) with f≗g t
  ... | eqs , eqf = inf (eqs , λ where
     p .force {j} → P.subst (λ t → Bisim C₂ j (map f (n (position f p) .force))
                                              (map g (t .force)))
                    (eqf p)
                    (map-cong f≗g (n (position f p) .force)))

module _ {s₁ s₂ s₃ p₁ p₂ p₃} {C₁ : Container s₁ p₁}
         {C₂ : Container s₂ p₂} {C₃ : Container s₃ p₃} where

  map-∘ : ∀ {i} {g : C₂ ⇒ C₃} {f : C₁ ⇒ C₂} c₁ →
                Bisim C₃ i (map (g Mp.∘ f) c₁) (map g $′ map f c₁)
  map-∘ (inf (s , f)) = inf (P.refl , λ where p .force → map-∘ (f _ .force))


module _ {s₁ s₂ p₁ p₂ s} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {S : Set s} {alg : S → ⟦ C₁ ⟧ S} {f : C₁ ⇒ C₂} where

  map-unfold : ∀ {i} s → Bisim C₂ i (map f (unfold alg s))
                                    (unfold (⟪ f ⟫ ∘′ alg) s)
  map-unfold s = inf (P.refl , λ where p .force → map-unfold _)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-compose = map-∘
{-# WARNING_ON_USAGE map-compose
"Warning: map-compose was deprecated in v2.0.
Please use map-∘ instead."
#-}
