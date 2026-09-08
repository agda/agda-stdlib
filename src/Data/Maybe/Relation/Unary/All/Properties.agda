------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Relation.Unary.All.Properties where

open import Data.Maybe.Base using (Maybe; just; nothing; map; _<∣>_)
open import Data.Maybe.Relation.Unary.All as All
  using (All; nothing; just)
open import Data.Maybe.Relation.Binary.Connected
  using (Connected; just-nothing; nothing-just; nothing; just)
open import Data.Product.Base using (_×_; _,_)
open import Function.Base using (_∘_)
open import Level using (Level)
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary.Core using (Rel)

private
  variable
    a b p q ℓ : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred B q

------------------------------------------------------------------------
-- Relationship with other combinators
------------------------------------------------------------------------

All⇒Connectedˡ : ∀ {R : Rel A ℓ} {x y} →
                 All (R x) y → Connected R (just x) y
All⇒Connectedˡ (just x) = just x
All⇒Connectedˡ nothing  = just-nothing

All⇒Connectedʳ : ∀ {R : Rel A ℓ} {x y} →
                 All (λ v → R v y) x → Connected R x (just y)
All⇒Connectedʳ (just x) = just x
All⇒Connectedʳ nothing  = nothing-just

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for maybe operations
------------------------------------------------------------------------
-- map

map⁺ : ∀ {f : A → B} {mx} → All (P ∘ f) mx → All P (map f mx)
map⁺ (just p) = just p
map⁺ nothing  = nothing

map⁻ : ∀ {f : A → B} {mx} → All P (map f mx) → All (P ∘ f) mx
map⁻ {mx = just x}  (just px) = just px
map⁻ {mx = nothing} nothing   = nothing

-- A variant of All.map.

gmap : ∀ {f : A → B} → P ⊆ Q ∘ f → All P ⊆ All Q ∘ map f
gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- _<∣>_

<∣>⁺ : ∀ {mx my} → All P mx → All P my → All P (mx <∣> my)
<∣>⁺ (just px) pmy = just px
<∣>⁺ nothing   pmy = pmy

<∣>⁻ : ∀ mx {my} → All P (mx <∣> my) → All P mx
<∣>⁻ (just x) pmxy = pmxy
<∣>⁻ nothing  pmxy = nothing
