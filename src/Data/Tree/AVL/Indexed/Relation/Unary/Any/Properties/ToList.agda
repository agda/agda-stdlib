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
  using (_∼_; []⁺; ++-∷⁺; toList-refl; toList-++)
import Data.List.Base as List
import Data.List.Relation.Unary.Any as List
import Data.List.Relation.Unary.Any.Properties as List
open import Data.Nat.Base using (ℕ)
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
    v : Level
    V : Value v
    p : Level
    P : Pred (K& V) p
    l u : Key⁺
    h : ℕ
    t : Tree V l u h


toList∼toDiffList : (t : Tree V l u h) →
                    toList t ∼ toDiffList t
toList∼toDiffList (leaf l<u) = []⁺
toList∼toDiffList (node k l r bal) =
  toList-refl (++-∷⁺ k (toList∼toDiffList l) (toList∼toDiffList r))

toList⁺ : Any P t → List.Any P (toList t)
toList⁺ {P = P} {t = node k l r bal} p =
  subst (List.Any P) toList-node (path-++-∷ p)
  where
  path-++-∷ : Any P (node k l r bal) →
              List.Any P (toList l List.++ k List.∷ toList r)
  path-++-∷ (here p) = List.++⁺ʳ (toList l) (List.here p)
  path-++-∷ (left p) = List.++⁺ˡ (toList⁺ p)
  path-++-∷ (right p) = List.++⁺ʳ (toList l) (List.there (toList⁺ p))
  toList-node : toList l List.++ k List.∷ toList r ≡
                toList (node k l r bal)
  toList-node = toList-++ (toList∼toDiffList l) (k ∷ toDiffList r)

toList⁻ : List.Any P (toList t) → Any P t
toList⁻ {P = P} {t = node k l r bal} p =
  path-++-∷ (List.++⁻ (toList l)
                      (subst (List.Any P) (sym toList-node) p))
  where
  path-++-∷ : List.Any P (toList l) ⊎ List.Any P (k List.∷ toList r) →
              Any P (node k l r bal)
  path-++-∷ (inj₁ p) = left (toList⁻ p)
  path-++-∷ (inj₂ (List.here p)) = here p
  path-++-∷ (inj₂ (List.there p)) = right (toList⁻ p)
  toList-node : toList l List.++ k List.∷ toList r ≡
                toList (node k l r bal)
  toList-node = toList-++ (toList∼toDiffList l) (k ∷ toDiffList r)
