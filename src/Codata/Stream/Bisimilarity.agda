------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for Streams
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Stream.Bisimilarity where

open import Size
open import Codata.Thunk
open import Codata.Stream
open import Level
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

data Bisim {a b r} {A : Set a} {B : Set b} (R : REL A B r) i :
           REL (Stream A ∞) (Stream B ∞) (a ⊔ b ⊔ r) where
  _∷_ : ∀ {x y xs ys} → R x y → Thunk^R (Bisim R) i xs ys →
        Bisim R i (x ∷ xs) (y ∷ ys)

module _ {a r} {A : Set a} {R : Rel A r} where

 reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
 reflexive refl^R {i} {r ∷ rs} = refl^R ∷ λ where .force → reflexive refl^R

module _ {a b} {A : Set a} {B : Set b}
         {r} {P : A → B → Set r} {Q : B → A → Set r} where

 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ (p ∷ ps) = sym^PQ p ∷ λ where .force → symmetric sym^PQ (ps .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

 transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
 transitive trans^PQR (p ∷ ps) (q ∷ qs) =
   trans^PQR p q ∷ λ where .force → transitive trans^PQR (ps .force) (qs .force)

module _ {a r} {A : Set a} {R : Rel A r} where

  isPartialEquivalence : ∀ {i} → IsPartialEquivalence R → IsPartialEquivalence (Bisim R i)
  isPartialEquivalence pequiv^R = record
    { sym   = symmetric pequiv^R.sym
    ; trans = transitive pequiv^R.trans
    } where module pequiv^R = IsPartialEquivalence pequiv^R

  isEquivalence : ∀ {i} → IsEquivalence R → IsEquivalence (Bisim R i)
  isEquivalence equiv^R = record
    { refl  = reflexive equiv^R.refl
    ; isPartialEquivalence = isPartialEquivalence equiv^R.isPartialEquivalence
    } where module equiv^R = IsEquivalence equiv^R

module _ {a r} (S : Setoid a r) where

  setoid : ∀ i → Setoid a (a ⊔ r)
  setoid i = record { isEquivalence = isEquivalence {i = i} (Setoid.isEquivalence S) }

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs xs ys i} → Pointwise R as bs →
        Bisim R i xs ys → Bisim R i (as ++ xs) (bs ++ ys)
  ++⁺ []       rs = rs
  ++⁺ (r ∷ pw) rs = r ∷ λ where .force → ++⁺ pw rs

  ⁺++⁺ : ∀ {as bs xs ys i} → Pointwise R (List⁺.toList as) (List⁺.toList bs) →
         Thunk^R (Bisim R) i xs ys → Bisim R i (as ⁺++ xs) (bs ⁺++ ys)
  ⁺++⁺ (r ∷ pw) rs = r ∷ λ where .force → ++⁺ pw (rs .force)

-- Pointwise Equality as a Bisimilarity
------------------------------------------------------------------------

module _ {ℓ} {A : Set ℓ} where

 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Stream A ∞ → Stream A ∞ → Set ℓ
 _⊢_≈_ = Bisim _≡_

 refl : ∀ {i} → Reflexive (i ⊢_≈_)
 refl = reflexive Eq.refl

 sym : ∀ {i} → Symmetric (i ⊢_≈_)
 sym = symmetric Eq.sym

 trans : ∀ {i} → Transitive (i ⊢_≈_)
 trans = transitive Eq.trans

module ≈-Reasoning {a} {A : Set a} {i} where

  open import Relation.Binary.Reasoning.Setoid (setoid (Eq.setoid A) i) public
