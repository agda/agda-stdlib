------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of toList related to Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.ToList
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.DifferenceList.Base using (_∷_)
open import Data.DifferenceList.Properties
  using (ListLike; []⁺; ∷⁺; ++⁺; toList-++-homo)
import Data.List.Base as List
import Data.List.Relation.Unary.Any as List
import Data.List.Relation.Unary.Any.Properties as List
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; subst; sym)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto
  using (Any; here; left; right)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p
    l u : Key⁺
    hˡ hʳ h : ℕ
    t : Tree V l u h


listLike : (t : Tree V l u h) → ListLike (toDiffList t)
listLike (leaf l<u) = List.[] , []⁺
listLike (node k l r bal) =
  let (ls , ls∼dls) = listLike l
      (rs , rs∼drs) = listLike r
  in ls List.++ k List.∷ rs ,
     (++⁺ ls∼dls (∷⁺ k rs∼drs))

++≡node : (kv : K& V) →
          (lk : Tree V l [ kv .key ] hˡ) →
          (ku : Tree V [ kv .key ] u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          toList lk List.++ kv List.∷ toList ku ≡
            toList (node kv lk ku bal)
++≡node kv lk ku _ =
  toList-++-homo (listLike lk) (kv ∷ toDiffList ku)

toList⁺ : Any P t → List.Any P (toList t)
toList⁺-node : {kv : K& V} →
               {lk : Tree V l [ kv .key ] hˡ} →
               {ku : Tree V [ kv .key ] u hʳ} →
               {bal : hˡ ∼ hʳ ⊔ h} →
               Any P (node kv lk ku bal) →
               List.Any P (toList lk List.++ kv List.∷ toList ku)
toList⁺ {P = P} {t = node kv lk ku bal} p =
  subst (List.Any P) (++≡node kv lk ku bal) (toList⁺-node p)
toList⁺-node {lk = lk} (here p) =
  List.++⁺ʳ (toList lk) (List.here p)
toList⁺-node (left p) =
  List.++⁺ˡ (toList⁺ p)
toList⁺-node {lk = lk} (right p) =
  List.++⁺ʳ (toList lk) (List.there (toList⁺ p))

toList⁻ : List.Any P (toList t) → Any P t
toList⁻-node : {kv : K& V} →
               {lk : Tree V l [ kv .key ] hˡ} →
               {ku : Tree V [ kv .key ] u hʳ} →
               {bal : hˡ ∼ hʳ ⊔ h} →
               List.Any P (toList lk) ⊎ List.Any P (kv List.∷ toList ku) →
               Any P (node kv lk ku bal)
toList⁻ {P = P} {t = node kv lk ku bal} p =
  toList⁻-node
    (List.++⁻ (toList lk)
      (subst (List.Any P) (sym (++≡node kv lk ku bal)) p))
toList⁻-node (inj₁ p) = left (toList⁻ p)
toList⁻-node (inj₂ (List.here p)) = here p
toList⁻-node (inj₂ (List.there p)) = right (toList⁻ p)
