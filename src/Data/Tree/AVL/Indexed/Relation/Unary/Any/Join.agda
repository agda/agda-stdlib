------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of join related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Join
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core renaming (refl to ≡-refl)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open StrictTotalOrder sto renaming (Carrier to Key)

open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Cast sto
  using (castʳ⁺; castʳ⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.JoinConstFuns sto
  using (joinʳ⁻-left⁺; joinʳ⁻-here⁺; joinʳ⁻-right⁺; joinʳ⁻⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.HeadTail sto
  using (headTail⁺; headTail-head⁻; headTail-tail⁻)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

module _ {V : Value v} where

  private
    Val = Value.family V

  join-left⁺ : ∀ {l m u hˡ hʳ h} →
               (t₁ : Tree V l m hˡ) (t₂ : Tree V m u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P t₁ → Any P (proj₂ (join t₁ t₂ bal))
  join-left⁺ _ (leaf _) ∼- p = castʳ⁺ p
  join-left⁺ {hʳ = suc _} t₁ t₂₃@(node _ _ _ _) bal p
    with headTail t₂₃
  ... | (k₂ , m<k₂ , t₃) =
    joinʳ⁻-left⁺ k₂ (castʳ t₁ m<k₂) t₃ bal (castʳ⁺ p)

  join-right⁺ : ∀ {l m u hˡ hʳ h} →
                (t₁ : Tree V l m hˡ) (t₂ : Tree V m u hʳ) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P t₂ → Any P (proj₂ (join t₁ t₂ bal))
  join-right⁺ _ (leaf _) ∼- ()
  join-right⁺ {hʳ = suc _} t₁ t₂₃@(node _ _ _ _) bal p
    with headTail t₂₃ | headTail⁺ t₂₃ p
  ... | k₂ , m<k₂ , t₃ | inj₁ ph =
    joinʳ⁻-here⁺ k₂ (castʳ t₁ m<k₂) t₃ bal ph
  ... | k₂ , m<k₂ , t₃ | inj₂ pt =
    joinʳ⁻-right⁺ k₂ (castʳ t₁ m<k₂) t₃ bal pt

  join⁻ : ∀ {l m u hˡ hʳ h} →
          (t₁ : Tree V l m hˡ) (t₂ : Tree V m u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (join t₁ t₂ bal)) →
          Any P t₁ ⊎ Any P t₂
  join⁻ _ (leaf _) ∼- p = inj₁ (castʳ⁻ p)
  join⁻ {hʳ = suc _} t₁ t₂₃@(node _ _ _ _) bal p
    with (k₂ , m<k₂ , t₃) ← headTail t₂₃ in eq
       | joinʳ⁻⁻ k₂ (castʳ t₁ m<k₂) t₃ bal p | eq
  ... | inj₁ pk | ≡-refl = inj₂ (headTail-head⁻ t₂₃ pk)
  ... | inj₂ (inj₁ pl) | ≡-refl = inj₁ (castʳ⁻ pl)
  ... | inj₂ (inj₂ pr) | ≡-refl = inj₂ (headTail-tail⁻ t₂₃ pr)

  join-node⁻ : ∀ {l u hˡ hʳ h} {k′ : Key} (v : Val k′) →
               (lk′ : Tree V l [ k′ ] hˡ) (k′u : Tree V [ k′ ] u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P (proj₂ (join lk′ k′u bal)) →
               Any P (node (k′ , v) lk′ k′u bal)
  join-node⁻ _ lk′ k′u bal p with join⁻ lk′ k′u bal p
  ... | inj₁ p₁ = left p₁
  ... | inj₂ p₂ = right p₂
