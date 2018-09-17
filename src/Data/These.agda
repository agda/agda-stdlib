------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type
------------------------------------------------------------------------

module Data.These where

open import Level
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Function

data These {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  this  : A     → These A B
  that  :     B → These A B
  these : A → B → These A B

-- map

map : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂}
      (f : A₁ → A₂) (g : B₁ → B₂) → These A₁ B₁ → These A₂ B₂
map f g (this a)    = this (f a)
map f g (that b)    = that (g b)
map f g (these a b) = these (f a) (g b)

map₁ : ∀ {a₁ a₂ b} {A₁ : Set a₁} {A₂ : Set a₂} {B : Set b}
       (f : A₁ → A₂) → These A₁ B → These A₂ B
map₁ f = map f id

map₂ : ∀ {a b₁ b₂} {A : Set a} {B₁ : Set b₁} {B₂ : Set b₂}
       (g : B₁ → B₂) → These A B₁ → These A B₂
map₂ = map id

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

-- fold

  fold : (A → C) → (B → C) → (A → B → C) → These A B → C
  fold l r lr (this a)    = l a
  fold l r lr (that b)    = r b
  fold l r lr (these a b) = lr a b

  foldWithDefaults : A → B → (A → B → C) → These A B → C
  foldWithDefaults a b lr = fold (flip lr b) (lr a) lr

module _ {a b} {A : Set a} {B : Set b} where

-- swap

  swap : These A B → These B A
  swap = fold that this (flip these)

-- Component extraction via Maybe

  fromThis : These A B → Maybe A
  fromThis = fold just (const nothing) (const ∘′ just)

  fromThat : These A B → Maybe B
  fromThat = fold (const nothing) just (const just)

-- align

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  alignWith : ∀ {e f} {E : Set e} {F : Set f} →
    (These A C → E) → (These B D → F) → These A B → These C D → These E F
  alignWith f g (this a)    (this c)    = this (f (these a c))
  alignWith f g (this a)    (that d)    = these (f (this a)) (g (that d))
  alignWith f g (this a)    (these c d) = these (f (these a c)) (g (that d))
  alignWith f g (that b)    (this c)    = these (f (that c)) (g (this b))
  alignWith f g (that b)    (that d)    = that (g (these b d))
  alignWith f g (that b)    (these c d) = these (f (that c)) (g (these b d))
  alignWith f g (these a b) (this c)    = these (f (these a c)) (g (this b))
  alignWith f g (these a b) (that d)    = these (f (this a)) (g (these b d))
  alignWith f g (these a b) (these c d) = these (f (these a c)) (g (these b d))

  align : These A B → These C D → These (These A C) (These B D)
  align = alignWith id id

-- projections

module _ {a} {A : Set a} where

  leftMost : These A A → A
  leftMost = fold id id const

  rightMost : These A A → A
  rightMost = fold id id (flip const)

  mergeThese : (A → A → A) → These A A → A
  mergeThese = fold id id
