------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for the Delay type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Codata.Delay.Bisimilarity where

open import Size
open import Codata.Thunk
open import Codata.Delay
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

data Bisim {a b r} {A : Set a} {B : Set b} (R : A → B → Set r) i :
           (xs : Delay A ∞) (ys : Delay B ∞) → Set (a ⊔ b ⊔ r) where
  now   : ∀ {x y} → R x y → Bisim R i (now x) (now y)
  later : ∀ {xs ys} → Thunk^R (Bisim R) i xs ys → Bisim R i (later xs) (later ys)

module _ {a r} {A : Set a} {R : A → A → Set r} where

 reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
 reflexive refl^R {i} {now r}    = now refl^R
 reflexive refl^R {i} {later rs} = later λ where .force → reflexive refl^R

module _ {a b} {A : Set a} {B : Set b}
         {r} {P : A → B → Set r} {Q : B → A → Set r} where

 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ (now p)    = now (sym^PQ p)
 symmetric sym^PQ (later ps) = later λ where .force → symmetric sym^PQ (ps .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

 transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
 transitive trans^PQR (now p)    (now q)    = now (trans^PQR p q)
 transitive trans^PQR (later ps) (later qs) =
   later λ where .force → transitive trans^PQR (ps .force) (qs .force)


-- Pointwise Equality as a Bisimilarity
------------------------------------------------------------------------

module _ {ℓ} {A : Set ℓ} where

 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Delay A ∞ → Delay A ∞ → Set ℓ
 _⊢_≈_ = Bisim _≡_

 refl : ∀ {i} → Reflexive (i ⊢_≈_)
 refl = reflexive Eq.refl

 sym : ∀ {i} → Symmetric (i ⊢_≈_)
 sym = symmetric Eq.sym

 trans : ∀ {i} → Transitive (i ⊢_≈_)
 trans = transitive Eq.trans
