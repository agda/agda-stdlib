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

private
  variable
    a b c p q r : Level
    A : Set a
    B : Set b
    C : Set c
    i : Size

data Bisim {A : Set a} {B : Set b} (R : REL A B r) i :
           REL (Stream A ∞) (Stream B ∞) (a ⊔ b ⊔ r) where
  _∷_ : ∀ {x y xs ys} → R x y → Thunk^R (Bisim R) i xs ys →
        Bisim R i (x ∷ xs) (y ∷ ys)

module _ {R : Rel A r} where

 reflexive : Reflexive R → Reflexive (Bisim R i)
 reflexive refl^R {r ∷ rs} = refl^R ∷ λ where .force → reflexive refl^R

module _ {P : REL A B p} {Q : REL B A q} where

 symmetric : Sym P Q → Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ (p ∷ ps) = sym^PQ p ∷ λ where .force → symmetric sym^PQ (ps .force)

module _ {P : REL A B p} {Q : REL B C q} {R : REL A C r} where

 transitive : Trans P Q R → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
 transitive trans^PQR (p ∷ ps) (q ∷ qs) =
   trans^PQR p q ∷ λ where .force → transitive trans^PQR (ps .force) (qs .force)


isEquivalence : {R : Rel A r} → IsEquivalence R → IsEquivalence (Bisim R i)
isEquivalence equiv^R = record
  { refl  = reflexive equiv^R.refl
  ; sym   = symmetric equiv^R.sym
  ; trans = transitive equiv^R.trans
  } where module equiv^R = IsEquivalence equiv^R

setoid : Setoid a r → Size → Setoid a (a ⊔ r)
setoid S i = record
  { isEquivalence = isEquivalence {i = i} (Setoid.isEquivalence S)
  }

module _ {R : REL A B r} where

  ++⁺ : ∀ {as bs xs ys} → Pointwise R as bs →
        Bisim R i xs ys → Bisim R i (as ++ xs) (bs ++ ys)
  ++⁺ []       rs = rs
  ++⁺ (r ∷ pw) rs = r ∷ λ where .force → ++⁺ pw rs

  ⁺++⁺ : ∀ {as bs xs ys} → Pointwise R (List⁺.toList as) (List⁺.toList bs) →
         Thunk^R (Bisim R) i xs ys → Bisim R i (as ⁺++ xs) (bs ⁺++ ys)
  ⁺++⁺ (r ∷ pw) rs = r ∷ λ where .force → ++⁺ pw (rs .force)

------------------------------------------------------------------------
-- Pointwise Equality as a Bisimilarity

module _ {A : Set a} where

 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Stream A ∞ → Stream A ∞ → Set a
 _⊢_≈_ = Bisim _≡_

 refl : ∀ {i} → Reflexive (i ⊢_≈_)
 refl = reflexive Eq.refl

 sym : ∀ {i} → Symmetric (i ⊢_≈_)
 sym = symmetric Eq.sym

 trans : ∀ {i} → Transitive (i ⊢_≈_)
 trans = transitive Eq.trans

module ≈-Reasoning {a} {A : Set a} {i} where

  open import Relation.Binary.Reasoning.Setoid (setoid (Eq.setoid A) i) public
