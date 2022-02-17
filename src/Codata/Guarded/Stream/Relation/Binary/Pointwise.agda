------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive pointwise lifting of relations to streams
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream.Relation.Binary.Pointwise where

open import Codata.Guarded.Stream as Stream using (Stream; head; tail)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∘_; _on_)
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
  variable
    a ℓ : Level
    A B C D : Set a
    R S T : REL A B ℓ
    xs ys : Stream A

------------------------------------------------------------------------
-- Bisimilarity

record Pointwise (_∼_ : REL A B ℓ) (as : Stream A) (bs : Stream B) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : head as ∼ head bs
    tail : Pointwise _∼_ (tail as) (tail bs)

open Pointwise public

lookup : ∀ n → Pointwise R ⇒ (R on (Stream.lookup n))
lookup zero    rs = rs .head
lookup (suc n) rs = lookup n (rs .tail)

map : R ⇒ S → Pointwise R ⇒ Pointwise S
head (map R⇒S xs) = R⇒S (head xs)
tail (map R⇒S xs) = map R⇒S (tail xs)

reflexive : Reflexive R → Reflexive (Pointwise R)
head (reflexive R-refl) = R-refl
tail (reflexive R-refl) = reflexive R-refl

symmetric : Sym R S → Sym (Pointwise R) (Pointwise S)
head (symmetric R-sym-S xsRys) = R-sym-S (head xsRys)
tail (symmetric R-sym-S xsRys) = symmetric R-sym-S (tail xsRys)

transitive : Trans R S T → Trans (Pointwise R) (Pointwise S) (Pointwise T)
head (transitive RST-trans xsRys ysSzs) = RST-trans (head xsRys) (head ysSzs)
tail (transitive RST-trans xsRys ysSzs) = transitive RST-trans (tail xsRys) (tail ysSzs)

isEquivalence : IsEquivalence R → IsEquivalence (Pointwise R)
isEquivalence equiv^R = record
  { refl  = reflexive equiv^R.refl
  ; sym   = symmetric equiv^R.sym
  ; trans = transitive equiv^R.trans
  } where module equiv^R = IsEquivalence equiv^R

setoid : Setoid a ℓ → Setoid a ℓ
setoid S = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence S)
  }

antisymmetric : Antisym R S T → Antisym (Pointwise R) (Pointwise S) (Pointwise T)
head (antisymmetric RST-antisym xsRys ysSxs) = RST-antisym (head xsRys) (head ysSxs)
tail (antisymmetric RST-antisym xsRys ysSxs) = antisymmetric RST-antisym (tail xsRys) (tail ysSxs)

tabulate⁺ : ∀ {f : ℕ → A} {g : ℕ → B} →
            (∀ i → R (f i) (g i)) → Pointwise R (Stream.tabulate f) (Stream.tabulate g)
head (tabulate⁺ f∼g) = f∼g 0
tail (tabulate⁺ f∼g) = tabulate⁺ (f∼g ∘ suc)

tabulate⁻ : ∀ {f : ℕ → A} {g : ℕ → B} →
            Pointwise R (Stream.tabulate f) (Stream.tabulate g) → (∀ i → R (f i) (g i))
tabulate⁻ xsRys zero    = head xsRys
tabulate⁻ xsRys (suc i) = tabulate⁻ (tail xsRys) i

map⁺ : ∀ (f : A → C) (g : B → D) →
       Pointwise (λ a b → R (f a) (g b)) xs ys →
       Pointwise R (Stream.map f xs) (Stream.map g ys)
head (map⁺ f g faRgb) = head faRgb
tail (map⁺ f g faRgb) = map⁺ f g (tail faRgb)

map⁻ : ∀ (f : A → C) (g : B → D) →
       Pointwise R (Stream.map f xs) (Stream.map g ys) →
       Pointwise (λ a b → R (f a) (g b)) xs ys
head (map⁻ f g faRgb) = head faRgb
tail (map⁻ f g faRgb) = map⁻ f g (tail faRgb)

drop⁺ : ∀ n → Pointwise R ⇒ (Pointwise R on Stream.drop n)
drop⁺ zero    as≈bs = as≈bs
drop⁺ (suc n) as≈bs = drop⁺ n (as≈bs .tail)

------------------------------------------------------------------------
-- Pointwise Equality as a Bisimilarity

module _ {A : Set a} where

 infix 1 _≈_
 _≈_ : Stream A → Stream A → Set a
 _≈_ = Pointwise _≡_

 refl : Reflexive _≈_
 refl = reflexive Eq.refl

 sym : Symmetric _≈_
 sym = symmetric Eq.sym

 trans : Transitive _≈_
 trans = transitive Eq.trans

module ≈-Reasoning {a} {A : Set a} where

  open import Relation.Binary.Reasoning.Setoid (setoid (Eq.setoid A)) public
