------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation in the Propositional case
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional.Properties {a} {A : Set a} where

open import Algebra.Bundles
open import Algebra.Definitions
open import Algebra.Structures
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat using (suc)
open import Data.Product.Base using (-,_; proj₂)
open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
import Data.List.Properties as List
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂)
open import Function.Base using (_∘_; _⟨_⟩_)
open import Level using (Level)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (_Respects_; Decidable)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; cong; cong₂; _≢_; setoid)
open import Relation.Nullary

import Data.List.Relation.Binary.Permutation.Propositional as Propositional
import Data.List.Relation.Binary.Permutation.Setoid.Properties as Permutation
import Data.List.Relation.Binary.Permutation.Homogeneous as Properties

private
  variable
    b p : Level
    B : Set b
    x y z : A
    ws xs ys zs : List A
    vs : List B

  module ↭ = Permutation (setoid A)


open Propositional {A = A} public
open ↭ public
-- legacy variations in naming
  renaming (dropMiddleElement-≋ to drop-mid-≡; dropMiddleElement to drop-mid)
-- legacy variation in implicit/explicit parametrisation
  hiding (shift; map⁺)

------------------------------------------------------------------------
-- Some useful lemmas

shift : ∀ v (xs ys : List A) → xs ++ [ v ] ++ ys ↭ v ∷ xs ++ ys
shift v = ↭-shift {v = v}

{- not sure we need either of these for their proofs?
------------------------------------------------------------------------
-- Some other useful lemmas, optimised for the Propositional case

drop-mid-≡ : ∀ {x : A} ws xs {ys} {zs} →
             ws ++ [ x ] ++ ys ≡ xs ++ [ x ] ++ zs →
             ws ++ ys ↭ xs ++ zs
drop-mid-≡ []       []       eq   with cong List.tail eq
drop-mid-≡ []       []       eq   | refl = refl
drop-mid-≡ []       (x ∷ xs) refl = shift _ xs _
drop-mid-≡ (w ∷ ws) []       refl = ↭-sym (shift _ ws _)
drop-mid-≡ (w ∷ ws) (x ∷ xs) eq with List.∷-injective eq
... | refl , eq′ = prep w (drop-mid-≡ ws xs eq′)

drop-mid : ∀ {x : A} ws xs {ys zs} →
           ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
drop-mid {A = A} {x} ws xs p = drop-mid′ p ws xs refl refl
  where
  drop-mid′ : ∀ {l′ l″ : List A} → l′ ↭ l″ →
              ∀ ws xs {ys zs} →
              ws ++ [ x ] ++ ys ≡ l′ →
              xs ++ [ x ] ++ zs ≡ l″ →
              ws ++ ys ↭ xs ++ zs
  drop-mid′ refl         ws           xs           refl eq   = drop-mid-≡ ws xs (≡.sym eq)
  drop-mid′ (prep x p)   []           []           refl eq   with cong tail eq
  drop-mid′ (prep x p)   []           []           refl eq   | refl = p
  drop-mid′ (prep x p)   []           (x ∷ xs)     refl refl = trans p (shift _ _ _)
  drop-mid′ (prep x p)   (w ∷ ws)     []           refl refl = trans (↭-sym (shift _ _ _)) p
  drop-mid′ (prep x p)   (w ∷ ws)     (x ∷ xs)     refl refl = prep _ (drop-mid′ p ws xs refl refl)
  drop-mid′ (swap y z p) []           []           refl refl = prep _ p
  drop-mid′ (swap y z p) []           (x ∷ [])     refl eq   with cong {B = List _}
                                                                       (λ { (x ∷ _ ∷ xs) → x ∷ xs
                                                                          ; _            → []
                                                                          })
                                                                       eq
  drop-mid′ (swap y z p) []           (x ∷ [])     refl eq   | refl = prep _ p
  drop-mid′ (swap y z p) []           (x ∷ _ ∷ xs) refl refl = prep _ (trans p (shift _ _ _))
  drop-mid′ (swap y z p) (w ∷ [])     []           refl eq   with cong tail eq
  drop-mid′ (swap y z p) (w ∷ [])     []           refl eq   | refl = prep _ p
  drop-mid′ (swap y z p) (w ∷ x ∷ ws) []           refl refl = prep _ (trans (↭-sym (shift _ _ _)) p)
  drop-mid′ (swap y y p) (y ∷ [])     (y ∷ [])     refl refl = prep _ p
  drop-mid′ (swap y z p) (y ∷ [])     (z ∷ y ∷ xs) refl refl = begin
      _ ∷ _             <⟨ p ⟩
      _ ∷ (xs ++ _ ∷ _) <⟨ shift _ _ _ ⟩
      _ ∷ _ ∷ xs ++ _   <<⟨ refl ⟩
      _ ∷ _ ∷ xs ++ _   ∎
  drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ [])     refl refl = begin
      _ ∷ _ ∷ ws ++ _   <<⟨ refl ⟩
      _ ∷ (_ ∷ ws ++ _) <⟨ ↭-sym (shift _ _ _) ⟩
      _ ∷ (ws ++ _ ∷ _) <⟨ p ⟩
      _ ∷ _             ∎
  drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ y ∷ xs) refl refl = swap y z (drop-mid′ p _ _ refl refl)
  drop-mid′ (trans p₁ p₂) ws  xs refl refl with ∈-∃++ (∈-resp-↭ p₁ (∈-insert ws))
  ... | (h , t , refl) = trans (drop-mid′ p₁ ws h refl refl) (drop-mid′ p₂ h xs refl refl)
-}

------------------------------------------------------------------------
-- Additional/specialised properties which hold in the case _≈_ = _≡_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Permutations of singleton lists

↭-singleton-inv : xs ↭ [ x ] → xs ≡ [ x ]
↭-singleton-inv ρ with _ , refl , refl ← ↭-singleton⁻¹ ρ = refl

------------------------------------------------------------------------
-- sym
{-
↭-sym-involutive : ∀ {xs ys : List A} (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
↭-sym-involutive refl          = refl
↭-sym-involutive (prep x ↭)    = cong (prep x) (↭-sym-involutive ↭)
↭-sym-involutive (swap x y ↭)  = cong (swap x y) (↭-sym-involutive ↭)
↭-sym-involutive (trans ↭₁ ↭₂) =
  cong₂ trans (↭-sym-involutive ↭₁) (↭-sym-involutive ↭₂)
-}
------------------------------------------------------------------------
-- Relationships to other predicates
{-
Any-resp-[σ⁻¹∘σ] : {xs ys : List A} {P : Pred A p} →
                   (σ : xs ↭ ys) →
                   (ix : Any P xs) →
                   Any-resp-↭ (trans σ (↭-sym σ)) ix ≡ ix
Any-resp-[σ⁻¹∘σ] refl          ix               = refl
Any-resp-[σ⁻¹∘σ] (prep _ _)    (here _)         = refl
Any-resp-[σ⁻¹∘σ] (swap _ _ _)  (here _)         = refl
Any-resp-[σ⁻¹∘σ] (swap _ _ _)  (there (here _)) = refl
Any-resp-[σ⁻¹∘σ] (trans σ₁ σ₂) ix
  rewrite Any-resp-[σ⁻¹∘σ] σ₂ (Any-resp-↭ σ₁ ix)
  rewrite Any-resp-[σ⁻¹∘σ] σ₁ ix
  = refl
Any-resp-[σ⁻¹∘σ] (prep _ σ)    (there ix)
  rewrite Any-resp-[σ⁻¹∘σ] σ ix
  = refl
Any-resp-[σ⁻¹∘σ] (swap _ _ σ)  (there (there ix))
  rewrite Any-resp-[σ⁻¹∘σ] σ ix
  = refl

∈-resp-[σ⁻¹∘σ] : {xs ys : List A} {x : A} →
                 (σ : xs ↭ ys) →
                 (ix : x ∈ xs) →
                 ∈-resp-↭ (trans σ (↭-sym σ)) ix ≡ ix
∈-resp-[σ⁻¹∘σ] = Any-resp-[σ⁻¹∘σ]
-}
------------------------------------------------------------------------
-- map

module _  {B : Set b} (f : A → B) where

  open Propositional {A = B} using () renaming (_↭_ to _↭′_)

  map⁺ : xs ↭ ys → List.map f xs ↭′ List.map f ys
  map⁺ = ↭.map⁺ (setoid B) {!≡.cong f!}
{-
  -- permutations preserve 'being a mapped list'
  ↭-map-inv : List.map f xs ↭′ vs → ∃ λ ys → vs ≡ List.map f ys × xs ↭ ys
  ↭-map-inv {xs = []} f*xs↭vs
    with ≡.refl ← ↭′.↭-[]-invˡ f*xs↭vs  = [] , ≡.refl , ↭-refl
  ↭-map-inv {xs = x ∷ []} (Properties.refl f*xs≋vs) = {!f*xs≋vs!}
  ↭-map-inv {xs = x ∷ []} (Properties.prep eq p) = {!!}
  ↭-map-inv {xs = x ∷ []} (Properties.trans p p₁) = {!!}
  ↭-map-inv {xs = x ∷ y ∷ xs} (Properties.refl x₁) = {!!}
  ↭-map-inv {xs = x ∷ y ∷ xs} (Properties.prep eq p) = {!!}
  ↭-map-inv {xs = x ∷ y ∷ xs} (Properties.swap eq₁ eq₂ p) = {!!}
  ↭-map-inv {xs = x ∷ y ∷ xs} (Properties.trans p p₁) = {!!}
-}

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

↭-empty-inv = ↭-[]-invʳ
{-# WARNING_ON_USAGE ↭-empty-inv
"Warning: ↭-empty-inv was deprecated in v2.1.
Please use ↭-[]-invʳ instead."
#-}


