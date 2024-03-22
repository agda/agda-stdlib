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
open import Data.Product.Base using (-,_; proj₂)
open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂)
open import Function.Base using (_∘_; _⟨_⟩_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (_Respects_; Decidable)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; cong; setoid)
open import Relation.Nullary
open import Relation.Unary using (Pred)

import Data.List.Relation.Binary.Permutation.Propositional as Propositional
import Data.List.Relation.Binary.Permutation.Setoid.Properties as Permutation

private
  variable
    b p r : Level
    B : Set b
    v x y z : A
    ws xs ys zs : List A
    vs : List B
    P : Pred A p
    R : Rel A r

  module ↭ = Permutation (setoid A)


------------------------------------------------------------------------
-- Export all Setoid lemmas which hold unchanged in the case _≈_ = _≡_
------------------------------------------------------------------------

open Propositional {A = A} public
open ↭ public
-- POSSIBLE DEPRECATION: legacy variations in naming
  renaming (dropMiddleElement-≋ to drop-mid-≡; dropMiddleElement to drop-mid)
-- DEPRECATION: legacy variation in implicit/explicit parametrisation
  hiding (shift)
-- more efficient versions defined in `Propositional`
  hiding (↭-transˡ-≋; ↭-transʳ-≋)
-- needing to specialise to ≡, where `Respects` and `Preserves` etc. are trivial
  hiding ( map⁺; All-resp-↭; Any-resp-↭; ∈-resp-↭; ↭-sym-involutive
         ; ∈-resp-↭-sym⁻¹; ∈-resp-↭-sym)

------------------------------------------------------------------------
-- Additional/specialised properties which hold in the case _≈_ = _≡_
------------------------------------------------------------------------

sym-involutive : (p : x ≡ y) → ≡.sym (≡.sym p) ≡ p
sym-involutive refl = refl

trans-trans-sym : (p : x ≡ y) (q : y ≡ z) → ≡.trans (≡.trans p q) (≡.sym q) ≡ p
trans-trans-sym refl refl = refl

------------------------------------------------------------------------
-- Permutations of singleton lists

↭-singleton-inv : xs ↭ [ x ] → xs ≡ [ x ]
↭-singleton-inv ρ with _ , refl , refl ← ↭-singleton⁻¹ ρ = refl

------------------------------------------------------------------------
-- sym

↭-sym-involutive : (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
↭-sym-involutive = ↭.↭-sym-involutive sym-involutive

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

All-resp-↭ : (All P) Respects _↭_
All-resp-↭ = ↭.All-resp-↭ (≡.resp _)

Any-resp-↭ : (Any P) Respects _↭_
Any-resp-↭ = ↭.Any-resp-↭ (≡.resp _)

∈-resp-↭ : (x ∈_) Respects _↭_
∈-resp-↭ = ↭.∈-resp-↭

∈-resp-↭-sym⁻¹ : (p : xs ↭ ys) {iy : v ∈ ys} →
                 ∈-resp-↭ p (∈-resp-↭ (↭-sym p) iy) ≡ iy
∈-resp-↭-sym⁻¹ = ↭.∈-resp-↭-sym⁻¹ sym-involutive trans-trans-sym

∈-resp-↭-sym : (p : xs ↭ ys) {ix : v ∈ xs} →
               ∈-resp-↭ (↭-sym p) (∈-resp-↭ p ix) ≡ ix
∈-resp-↭-sym = ↭.∈-resp-↭-sym sym-involutive trans-trans-sym

------------------------------------------------------------------------
-- map

module _  {B : Set b} (f : A → B) where

  open Propositional {A = B} using () renaming (_↭_ to _↭′_)

  map⁺ : xs ↭ ys → List.map f xs ↭′ List.map f ys
  map⁺ = ↭.map⁺ (setoid B) (cong f)
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
-- Some other useful lemmas, optimised for the Propositional case
{- not sure we need these for their proofs? so renamed on import above

drop-mid-≡ : ∀ {v : A} ws xs {ys} {zs} →
             ws ++ [ x ] ++ ys ≡ xs ++ [ v ] ++ zs →
             ws ++ ys ↭ xs ++ zs
drop-mid-≡ []       []       ys≡zs
  with refl ← cong List.tail ys≡zs = refl
drop-mid-≡ []       (x ∷ xs) refl  = ↭-shift xs
drop-mid-≡ (w ∷ ws) []       refl  = ↭-sym (↭-shift ws)
drop-mid-≡ (w ∷ ws) (x ∷ xs) w∷ws[v]ys≡x∷xs[v]zs
  with refl , ws[v]ys≡xs[v]zs ← List.∷-injective eq
  = prep w (drop-mid-≡ ws xs ws[v]ys≡xs[v]zs)

drop-mid : ∀ {v : A} ws xs {ys zs} →
           ws ++ [ v ] ++ ys ↭ xs ++ [ v ] ++ zs →
           ws ++ ys ↭ xs ++ zs
drop-mid {A = A} {x} ws xs p = drop-mid′ p ws xs refl refl
  where
  drop-mid′ : ∀ {l′ l″ : List A} → l′ ↭ l″ →
              ∀ ws xs {ys zs} →
              ws ++ [ x ] ++ ys ≡ l′ →
              xs ++ [ x ] ++ zs ≡ l″ →
              ws ++ ys ↭ xs ++ zs
  drop-mid′ refl         ws           xs           refl eq   = drop-mid-≡ ws xs (≡.sym eq)
  drop-mid′ (prep x p)   []           []           refl eq   with refl ← cong tail eq = p
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
-- *** NB the next step can't be replaced with <⟨ shift _ _ _ ⟨ for some reason? ***
      _ ∷ (_ ∷ ws ++ _) <⟨ ↭-sym (shift _ _ _) ⟩
-- *** because of parsing problems for that use of the `Reasoning` combinators!? ***
      _ ∷ (ws ++ _ ∷ _) <⟨ p ⟩
      _ ∷ _             ∎
  drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ y ∷ xs) refl refl = swap y z (drop-mid′ p _ _ refl refl)
  drop-mid′ (trans p₁ p₂) ws  xs refl refl with ∈-∃++ (∈-resp-↭ p₁ (∈-insert ws))
  ... | (h , t , refl) = trans (drop-mid′ p₁ ws h refl refl) (drop-mid′ p₂ h xs refl refl)
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

shift : ∀ v xs ys → xs ++ [ v ] ++ ys ↭ v ∷ xs ++ ys
shift v xs ys = ↭-shift {v = v} xs {ys}
{-# WARNING_ON_USAGE shift
"Warning: shift was deprecated in v2.1.
Please use ↭-shift instead. \\
NB. Parametrisation has changed to make v and ys implicit."
#-}
