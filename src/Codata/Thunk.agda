------------------------------------------------------------------------
-- The Agda standard library
--
-- The Thunk wrappers for sized codata, copredicates and corelations
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Codata.Thunk where

open import Size
open import Relation.Unary.Sized

------------------------------------------------------------------------
-- Basic types.

record Thunk {ℓ} (F : SizedSet ℓ) (i : Size) : Set ℓ where
  coinductive
  field force : {j : Size< i} → F j
open Thunk public

Thunk^P : ∀ {f p} {F : SizedSet f} (P : Size → F ∞ → Set p)
          (i : Size) (tf : Thunk F ∞) → Set p
Thunk^P P i tf = Thunk (λ i → P i (tf .force)) i

Thunk^R : ∀ {f g r} {F : SizedSet f} {G : SizedSet g}
          (R : Size → F ∞ → G ∞ → Set r)
          (i : Size) (tf : Thunk F ∞) (tg : Thunk G ∞) → Set r
Thunk^R R i tf tg = Thunk (λ i → R i (tf .force) (tg .force)) i

------------------------------------------------------------------------
-- Syntax

Thunk-syntax : ∀ {ℓ} → SizedSet ℓ → Size → Set ℓ
Thunk-syntax = Thunk

syntax Thunk-syntax (λ j → e) i = Thunk[ j < i ] e

------------------------------------------------------------------------
-- Basic functions.

-- Thunk is a functor
module _ {p q} {P : SizedSet p} {Q : SizedSet q} where

  map : ∀[ P ⇒ Q ] → ∀[ Thunk P ⇒ Thunk Q ]
  map f p .force = f (p .force)

-- Thunk is a comonad
module _ {p} {P : SizedSet p} where

  extract : ∀[ Thunk P ] → P ∞
  extract p = p .force

  duplicate : ∀[ Thunk P ⇒ Thunk (Thunk P) ]
  duplicate p .force .force = p .force

module _ {p q} {P : SizedSet p} {Q : SizedSet q} where

  infixl 1 _<*>_
  _<*>_ : ∀[ Thunk (P ⇒ Q) ⇒ Thunk P ⇒ Thunk Q ]
  (f <*> p) .force = f .force (p .force)

-- We can take cofixpoints of functions only making Thunk'd recursive calls
module _ {p} (P : SizedSet p) where

  cofix : ∀[ Thunk P ⇒ P ] → ∀[ P ]
  cofix f = f λ where .force → cofix f
