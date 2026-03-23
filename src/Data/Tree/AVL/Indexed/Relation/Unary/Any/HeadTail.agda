------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of headTail related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.HeadTail
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (suc; _+_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function using (id)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core renaming (refl to ≡-refl)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.JoinConstFuns sto
  using (joinˡ⁻-here⁺; joinˡ⁻-left⁺; joinˡ⁻-right⁺; joinˡ⁻⁻)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

headTail⁺ : ∀ {l u h} (t : Tree V l u (1 + h)) →
            let _ , _ , _ , t⁻ = headTail t in
            Any P t → P (proj₁ (headTail t)) ⊎ Any P t⁻
headTail⁺ (node _ (leaf _) _ ∼+) (here p) = inj₁ p
headTail⁺ (node _ (leaf _) _ ∼+) (right p) = inj₂ p
headTail⁺ (node _ (leaf _) _ ∼0) (here p) = inj₁ p
headTail⁺ (node k₃ t₁₂@(node _ _ _ _) t₄ bal) (here p)
  = let _ , _ , t₂ = headTail t₁₂
    in inj₂ (joinˡ⁻-here⁺ k₃ t₂ t₄ bal p)
headTail⁺ (node k₃ t₁₂@(node _ _ _ _) t₄ bal) (left p)
  = let _ , _ , t₂ = headTail t₁₂
    in Sum.map id (joinˡ⁻-left⁺ k₃ t₂ t₄ bal) (headTail⁺ t₁₂ p)
headTail⁺ (node k₃ t₁₂@(node _ _ _ _) t₄ bal) (right p)
  = let _ , _ , t₂ = headTail t₁₂
    in inj₂ (joinˡ⁻-right⁺ k₃ t₂ t₄ bal p)

headTail-head⁻ : ∀ {l u h} → (t : Tree V l u (suc h)) →
                 P (proj₁ (headTail t)) → Any P t
headTail-head⁻ (node _ (leaf _) _ ∼+) p = here p
headTail-head⁻ (node _ (leaf _) _ ∼0) p = here p
headTail-head⁻ (node _ t₁₂@(node _ _ _ _) _ _) p =
  left (headTail-head⁻ t₁₂ p)

headTail-tail⁻ : ∀ {l u h} (t : Tree V l u (1 + h)) →
                 let _ , _ , _ , t⁻ = headTail t in
                 Any P t⁻ → Any P t
headTail-tail⁻ (node _ (leaf _) _ ∼+) p = right p
headTail-tail⁻ (node _ (leaf _) _ ∼0) p = right p
headTail-tail⁻ (node k₃ t₁₂@(node _ _ _ _) t₄ bal) p
  using _ , _ , t₂ ← headTail t₁₂
  with joinˡ⁻⁻ k₃ t₂ t₄ bal p
... | inj₁ pk = here pk
... | inj₂ (inj₂ pr) = right pr
... | inj₂ (inj₁ pl) using p⁻ ← headTail-tail⁻ t₁₂ pl with bal
-- This match on `bal` shows the termination checker that `h` decreases.
...   | ∼+ = left p⁻
...   | ∼0 = left p⁻
...   | ∼- = left p⁻
