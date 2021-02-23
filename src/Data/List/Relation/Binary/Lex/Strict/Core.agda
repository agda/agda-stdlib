------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definitions of lexicographic ordering used here are suitable if
-- the argument order is a strict partial order.

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Lex.Strict.Core where

open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import Data.Unit.Base using (⊤)
open import Level
open import Relation.Binary.Core using (Rel)

open import Data.List.Relation.Binary.Lex.Core as Core public
  using (base; halt; this; next; ¬≤-this; ¬≤-next)

private
  variable
    a ℓ₁ ℓ₂ : Level

----------------------------------------------------------------------
-- Strict lexicographic ordering.

Lex-< : {A : Set a} (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) →
        Rel (List A) (a ⊔ ℓ₁ ⊔ ℓ₂)
Lex-< = Core.Lex ⊥

Lex-≤ : {A : Set a} (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) →
        Rel (List A) (a ⊔ ℓ₁ ⊔ ℓ₂)
Lex-≤ = Core.Lex ⊤
