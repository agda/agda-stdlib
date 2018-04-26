------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of _⊆_ and _⊆′_
------------------------------------------------------------------------

module Data.List.Sets.Setoid.Properties where

open import Relation.Binary
open import Data.List.Any using (Any; here; there)
open import Data.List.All
open import Data.List.Base using (List ; [] ; _∷_)

open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

open import Function using (_∘_ ; _$_)

import Data.List.Sets.Setoid as Sets

module _ {c ℓ} (S : Setoid c ℓ) where
  open Sets S
  open Setoid S renaming (Carrier to A)

  ∈-resp-⊆ : ∀ {x} → (x ∈_) Respects _⊆_
  ∈-resp-⊆ xs⊆ys = xs⊆ys $_

  ∈-resp-⊆′ : ∀ {x} → (x ∈_) Respects _⊆′_
  ∈-resp-⊆′ [] ()
  ∈-resp-⊆′ (h∈l₁ ∷ l₁⊆l₂) (here x≈h)   = ∈-resp-≈ S (sym x≈h) h∈l₁
  ∈-resp-⊆′ (h∈l₁ ∷ l₁⊆l₂) (there x∈l₁) = ∈-resp-⊆′ l₁⊆l₂ x∈l₁

  ⊆′⇒⊆ : ∀ {l₁ l₂} → l₁ ⊆′ l₂ → l₁ ⊆ l₂
  ⊆′⇒⊆ l₁⊆′l₂ = ∈-resp-⊆′ l₁⊆′l₂

  ⊆⇒⊆′ : ∀ {l₁ l₂} → l₁ ⊆ l₂ → l₁ ⊆′ l₂
  ⊆⇒⊆′ {[]}     l₁⊆l₂ = []
  ⊆⇒⊆′ {x ∷ l₁} l₁⊆l₂ = l₁⊆l₂ (here refl) ∷ ⊆⇒⊆′ (l₁⊆l₂ ∘ there)

  -- some basic properties of these two kinds of ⊆ relations

  ⊆-refl : Reflexive _⊆_
  ⊆-refl x∈xs = x∈xs

  ⊆-trans : Transitive _⊆_
  ⊆-trans xs⊆ys ys⊆zs x∈xs = ys⊆zs (xs⊆ys x∈xs)


  ⊆′-growʳ : ∀ {x : A} {l l′} → l ⊆′ l′ → l ⊆′ x ∷ l′
  ⊆′-growʳ {x} {.[]}   []            = []
  ⊆′-growʳ {x} {_ ∷ _} (h∈l ∷ l⊆′l′) = there h∈l ∷ ⊆′-growʳ l⊆′l′

  l⊆′x∷l : ∀ {x l} → l ⊆′ x ∷ l
  l⊆′x∷l {x} {l = []} = []
  l⊆′x∷l {x} {y ∷ l}  = there (here refl) ∷ ⊆′-growʳ l⊆′x∷l

  ⊆′-refl : Reflexive _⊆′_
  ⊆′-refl {[]}     = []
  ⊆′-refl {x ∷ x₁} = here refl ∷ l⊆′x∷l

  ⊆′-trans : Transitive _⊆′_
  ⊆′-trans []          y⊆z = []
  ⊆′-trans (h∈y ∷ x⊆y) y⊆z = ∈-resp-⊆′ y⊆z h∈y ∷ ⊆′-trans x⊆y y⊆z
