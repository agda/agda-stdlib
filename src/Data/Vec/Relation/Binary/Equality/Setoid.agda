------------------------------------------------------------------------
-- The Agda standard library
--
-- Semi-heterogeneous vector equality over setoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary

module Data.Vec.Relation.Binary.Equality.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin using (zero; suc)
open import Data.Vec.Base
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise)
open import Function.Base
open import Level using (_⊔_)
open import Relation.Binary

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition of equality

infix 4 _≋_

_≋_ : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ)
_≋_ = Pointwise _≈_

open Pointwise public using ([]; _∷_)
open PW public using (length-equal)

------------------------------------------------------------------------
-- Relational properties

≋-refl : ∀ {n} → Reflexive (_≋_ {n})
≋-refl = PW.refl refl

≋-sym : ∀ {n m} → Sym _≋_ (_≋_ {m} {n})
≋-sym = PW.sym sym

≋-trans : ∀ {n m o} → Trans (_≋_ {m}) (_≋_ {n} {o}) (_≋_)
≋-trans = PW.trans trans

≋-isEquivalence : ∀ n → IsEquivalence (_≋_ {n})
≋-isEquivalence = PW.isEquivalence isEquivalence

≋-setoid : ℕ → Setoid a (a ⊔ ℓ)
≋-setoid = PW.setoid S

------------------------------------------------------------------------
-- map

open PW public using ( map⁺)

------------------------------------------------------------------------
-- ++

open PW public using (++⁺ ; ++⁻ ; ++ˡ⁻; ++ʳ⁻)

++-identityˡ : ∀ {n} (xs : Vec A n) → [] ++ xs ≋ xs
++-identityˡ _ = ≋-refl

++-identityʳ : ∀ {n} (xs : Vec A n) → xs ++ [] ≋ xs
++-identityʳ []       = []
++-identityʳ (x ∷ xs) = refl ∷ ++-identityʳ xs

++-assoc : ∀ {n m k} (xs : Vec A n) (ys : Vec A m) (zs : Vec A k) →
             (xs ++ ys) ++ zs ≋ xs ++ (ys ++ zs)
++-assoc [] ys zs = ≋-refl
++-assoc (x ∷ xs) ys zs = refl ∷ ++-assoc xs ys zs

map-++ : ∀ {b m n} {B : Set b}
                   (f : B → A) (xs : Vec B m) {ys : Vec B n} →
                   map f (xs ++ ys) ≋ map f xs ++ map f ys
map-++ f []       = ≋-refl
map-++ f (x ∷ xs) = refl ∷ map-++ f xs

map-[]≔ : ∀ {b n} {B : Set b}
          (f : B → A) (xs : Vec B n) i p →
          map f (xs [ i ]≔ p) ≋ map f xs [ i ]≔ f p
map-[]≔ f (x ∷ xs) zero    p = refl ∷ ≋-refl
map-[]≔ f (x ∷ xs) (suc i) p = refl ∷ map-[]≔ f xs i p

------------------------------------------------------------------------
-- concat

open PW public using (concat⁺; concat⁻)

------------------------------------------------------------------------
-- replicate

replicate-shiftʳ : ∀ {m} n x (xs : Vec A m) →
                  replicate {n = n}     x ++ (x ∷ xs) ≋
                  replicate {n = 1 + n} x ++      xs
replicate-shiftʳ zero    x xs = ≋-refl
replicate-shiftʳ (suc n) x xs = refl ∷ (replicate-shiftʳ n x xs)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-++-commute = map-++
{-# WARNING_ON_USAGE map-++-commute
"Warning: map-++-commute was deprecated in v2.0.
Please use map-++ instead."
#-}
