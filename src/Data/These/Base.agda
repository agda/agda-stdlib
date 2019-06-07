------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type, basic type and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.These.Base where

open import Level
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Function

private
  variable
    a b c d e f : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    F : Set f

data These {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  this  : A     → These A B
  that  :     B → These A B
  these : A → B → These A B

------------------------------------------------------------------------
-- Operations

-- injection

fromSum : A ⊎ B → These A B
fromSum = [ this , that ]′

-- map

map : (f : A → B) (g : C → D) → These A C → These B D
map f g (this a)    = this (f a)
map f g (that b)    = that (g b)
map f g (these a b) = these (f a) (g b)

map₁ : (f : A → B) → These A C → These B C
map₁ f = map f id

map₂ : (g : B → C) → These A B → These A C
map₂ = map id

-- fold

fold : (A → C) → (B → C) → (A → B → C) → These A B → C
fold l r lr (this a)    = l a
fold l r lr (that b)    = r b
fold l r lr (these a b) = lr a b

foldWithDefaults : A → B → (A → B → C) → These A B → C
foldWithDefaults a b lr = fold (flip lr b) (lr a) lr

-- swap

swap : These A B → These B A
swap = fold that this (flip these)

-- align

alignWith : (These A C → E) → (These B D → F) → These A B → These C D → These E F
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
