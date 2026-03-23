------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of castʳ related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Cast
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

castʳ⁺ : ∀ {l m u h} {lm : Tree V l m h} {m<u : m <⁺ u} →
         Any P lm → Any P (castʳ lm m<u)
castʳ⁺ (here p) = here p
castʳ⁺ (left p) = left p
castʳ⁺ (right p) = right (castʳ⁺ p)

castʳ⁻ : ∀ {l m u h} {lm : Tree V l m h} {m<u : m <⁺ u} →
         Any P (castʳ lm m<u) → Any P lm
castʳ⁻ {lm = node _ _ _ _} (here p) = here p
castʳ⁻ {lm = node _ _ _ _} (left p) = left p
castʳ⁻ {lm = node _ _ _ _} (right p) = right (castʳ⁻ p)
