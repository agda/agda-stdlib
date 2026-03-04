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
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
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
            Any P t →
            P (proj₁ (headTail t))
            ⊎ Any P (proj₂ (proj₂ (proj₂ (headTail t))))
headTail⁺ (node _ (leaf _) _ ∼+) (here p) = inj₁ p
headTail⁺ (node _ (leaf _) _ ∼+) (right p) = inj₂ p
headTail⁺ (node _ (leaf _) _ ∼0) (here p) = inj₁ p
headTail⁺ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) (here p)
  with headTail t₁₂
... | k₁ , l<k₁ , t₂ = inj₂ (joinˡ⁻-here⁺ k₃ t₂ t₄ bal p)
headTail⁺ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) (left p)
  with headTail t₁₂ | headTail⁺ t₁₂ p
... | k₁ , l<k₁ , t₂ | inj₁ ph = inj₁ ph
... | k₁ , l<k₁ , t₂ | inj₂ pt = inj₂ (joinˡ⁻-left⁺ k₃ t₂ t₄ bal pt)
headTail⁺ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) (right p)
  with headTail t₁₂
... | k₁ , l<k₁ , t₂ = inj₂ (joinˡ⁻-right⁺ k₃ t₂ t₄ bal p)

headTail-head⁻ : ∀ {l u h} → (t : Tree V l u (suc h)) →
                 P (proj₁ (headTail t)) → Any P t
headTail-head⁻ (node _ (leaf _) _ ∼+) p = here p
headTail-head⁻ (node _ (leaf _) _ ∼0) p = here p
headTail-head⁻ (node {hˡ = suc _} _ t₁₂ _ _) p
  with headTail t₁₂
headTail-head⁻ (node {hˡ = suc _} _ t₁₂@(node _ _ _ _) _ _) p
  | k₁ , l<k₁ , t₂ = left (headTail-head⁻ t₁₂ p)

headTail-tail⁻ : ∀ {l u h} (t : Tree V l u (1 + h)) →
                 Any P (proj₂ (proj₂ (proj₂ (headTail t)))) →
                 Any P t
headTail-tail⁻ (node _ (leaf _) _ ∼+) p = right p
headTail-tail⁻ (node _ (leaf _) _ ∼0) p = right p
headTail-tail⁻ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) p
  with k₁ , l<k₁ , t₂ ← headTail t₁₂ in eq
     -- This match on `bal` is so the termination checker sees `h`
     -- decrease.
     | joinˡ⁻⁻ k₃ t₂ t₄ bal p | bal | eq
... | inj₁ pk | _ | ≡-refl = here pk
... | inj₂ (inj₁ pl) | ∼+ | ≡-refl = left (headTail-tail⁻ t₁₂ pl)
... | inj₂ (inj₁ pl) | ∼0 | ≡-refl = left (headTail-tail⁻ t₁₂ pl)
... | inj₂ (inj₁ pl) | ∼- | ≡-refl = left (headTail-tail⁻ t₁₂ pl)
... | inj₂ (inj₂ pr) | _ | ≡-refl = right pr
