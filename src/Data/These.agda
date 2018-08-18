------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type
------------------------------------------------------------------------

module Data.These where

open import Level
open import Algebra using (Semigroup)
open import Function

data These {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  this  : A → These A B
  that  : B → These A B
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

-- swap

swap : ∀ {a b} {A : Set a} {B : Set b} → These A B → These B A
swap (this a)    = that a
swap (that b)    = this b
swap (these a b) = these b a

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
  leftMost (this a)    = a
  leftMost (that a)    = a
  leftMost (these a _) = a

  rightMost : These A A → A
  rightMost (this a)    = a
  rightMost (that a)    = a
  rightMost (these _ a) = a

module _ {c ℓ} (S : Semigroup c ℓ) where

  open Semigroup S renaming (Carrier to A)

  toSemigroup : These A A → A
  toSemigroup (this a₁)     = a₁
  toSemigroup (that a₂)     = a₂
  toSemigroup (these a₁ a₂) = a₁ ∙ a₂
