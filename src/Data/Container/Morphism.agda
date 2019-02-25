------------------------------------------------------------------------
-- The Agda standard library
--
-- Container Morphisms
------------------------------------------------------------------------

module Data.Container.Morphism where

open import Data.Container.Core
import Function as F

module _ {s p} (C : Container s p) where

  id : C ⇒ C
  id .shape    = F.id
  id .position = F.id

module _ {s₁ s₂ s₃ p₁ p₂ p₃}
         {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} {C₃ : Container s₃ p₃}
         where

  infixr 9 _∘_
  _∘_ : C₂ ⇒ C₃ → C₁ ⇒ C₂ → C₁ ⇒ C₃
  (f ∘ g) .shape    = shape    f F.∘′ shape    g
  (f ∘ g) .position = position g F.∘′ position f
