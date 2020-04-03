------------------------------------------------------------------------
-- The Agda standard library
--
-- Syntax for magma reasoning
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles

module Algebra.Reasoning.Magma.Expr {c ℓ} (M : Magma c ℓ) where

open Magma M

open import Level
open import Data.Tree.Binary.Indexed
open import Data.Product
open import Data.Unit
open import Function.Base

private
  variable
    s : 𝕋

MTree : 𝕋 → Set c
MTree s = ITree ⊤ Carrier s

Expr : 𝕋 → Set c
Expr s = MTree s × IndexLeaf s

infixl 4 _◂_
infixr 4 _▸_

_◂_ : Carrier → Expr s → Expr (ns ls s)
c ◂ (t , foc) = node (leaf c) tt t , il-r foc

_▸_ : Expr s → Carrier → Expr (ns s ls)
(t , foc) ▸ c = node t tt (leaf c) , il-l foc

⌊_⌋ : Carrier → Expr ls
⌊ x ⌋ = leaf x , here-l

eval : Expr s → Carrier
eval (t , _) = foldr (λ l _ r → l ∙ r) id t

focus : (e : Expr s) → Carrier
focus (t , i) = retrieve-leaf t i

replace-at-focus : Expr s → Carrier → Expr s
replace-at-focus (t , foc) g = (update-index (λ _ → g) t foc) , foc

cong-expr : ∀ {s} →
            (e : Expr s) →
            {h : Carrier} →
            focus e ≈ h →
            eval e ≈ eval (replace-at-focus e h)
cong-expr (leaf x , here-l) eq = eq
cong-expr (node l m r , il-l i) eq = ∙-congʳ (cong-expr (l , i) eq)
cong-expr (node l m r , il-r i) eq = ∙-congˡ (cong-expr (r , i) eq)
