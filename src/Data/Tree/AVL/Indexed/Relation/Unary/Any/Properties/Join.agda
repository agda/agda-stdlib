------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of join related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Join
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Cast sto
  using (castʳ⁺; castʳ⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.HeadTail sto
  using (headTail⁺; headTail-head⁻; headTail-tail⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.JoinLemmas sto
  using (joinʳ⁻-left⁺; joinʳ⁻-here⁺; joinʳ⁻-right⁺; joinʳ⁻⁻)


private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p
    l m u : Key⁺
    hˡ hʳ h : ℕ


----------------------------------------------------------------------
-- join

join-left⁺ : (t₁ : Tree V l m hˡ) (t₂ : Tree V m u hʳ) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             Any {V = V} P t₁ → Any P (proj₂ (join t₁ t₂ bal))
join-left⁺ _ (leaf _)            ∼-  p = castʳ⁺ p
join-left⁺ t₁ t₂₃@(node _ _ _ _) bal p using k₂ , m<k₂ , t₃ ← headTail t₂₃
  = joinʳ⁻-left⁺ k₂ (castʳ t₁ m<k₂) t₃ bal (castʳ⁺ p)

join-right⁺ : (t₁ : Tree V l m hˡ) (t₂ : Tree V m u hʳ) →
              (bal : hˡ ∼ hʳ ⊔ h) →
              Any {V = V} P t₂ → Any P (proj₂ (join t₁ t₂ bal))
join-right⁺ t₁ t₂₃@(node _ _ _ _) bal p using k₂ , m<k₂ , t₃ ← headTail t₂₃
  = Sum.[ joinʳ⁻-here⁺ k₂ (castʳ t₁ m<k₂) t₃ bal
        , joinʳ⁻-right⁺ k₂ (castʳ t₁ m<k₂) t₃ bal ]′
        (headTail⁺ t₂₃ p)

join⁻ : (t₁ : Tree V l m hˡ) (t₂ : Tree V m u hʳ) →
        (bal : hˡ ∼ hʳ ⊔ h) →
        Any {V = V} P (proj₂ (join t₁ t₂ bal)) →
        Any P t₁ ⊎ Any P t₂
join⁻ _ (leaf _) ∼- p = inj₁ (castʳ⁻ p)
join⁻ t₁ t₂₃@(node _ _ _ _) bal p using k₂ , m<k₂ , t₃ ← headTail t₂₃
  with joinʳ⁻⁻ k₂ (castʳ t₁ m<k₂) t₃ bal p
... | inj₁ pk        = inj₂ (headTail-head⁻ t₂₃ pk)
... | inj₂ (inj₁ pl) = inj₁ (castʳ⁻ pl)
... | inj₂ (inj₂ pr) = inj₂ (headTail-tail⁻ t₂₃ pr)
