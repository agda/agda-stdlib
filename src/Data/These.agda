------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type
------------------------------------------------------------------------

module Data.These where

open import Level

data These {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  this  : A → These A B
  that  : B → These A B
  these : A → B → These A B

map : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂}
      (f : A₁ → A₂) (g : B₁ → B₂) → These A₁ B₁ → These A₂ B₂
map f g (this a)    = this (f a)
map f g (that b)    = that (g b)
map f g (these a b) = these (f a) (g b)

leftMost : ∀ {a} {A : Set a} → These A A → A
leftMost (this a)    = a
leftMost (that a)    = a
leftMost (these a _) = a

rightMost : ∀ {a} {A : Set a} → These A A → A
rightMost (this a)    = a
rightMost (that a)    = a
rightMost (these _ a) = a
