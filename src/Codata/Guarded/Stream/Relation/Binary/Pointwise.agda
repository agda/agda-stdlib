------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive pointwise lifting of relations to streams
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream.Relation.Binary.Pointwise where

open import Codata.Guarded.Stream as Stream using (Stream; head; tail)
open import Data.Nat.Base using (ℕ)
open import Function.Base using (_∘_)
open import Level
open import Relation.Binary

private
  variable
    a ℓ : Level
    A B C D : Set a
    R S T : REL A B ℓ
    xs ys : Stream A

record Pointwise (_∼_ : REL A B ℓ) (as : Stream A) (bs : Stream B) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : head as ∼ head bs
    tail : Pointwise _∼_ (tail as) (tail bs)

open Pointwise public

map : R ⇒ S → Pointwise R ⇒ Pointwise S
head (map R⇒S xs) = R⇒S (head xs)
tail (map R⇒S xs) = map R⇒S (tail xs)

refl : Reflexive R → Reflexive (Pointwise R)
head (refl R-refl) = R-refl
tail (refl R-refl) = refl R-refl

sym : Sym R S → Sym (Pointwise R) (Pointwise S)
head (sym R-sym-S xsRys) = R-sym-S (head xsRys)
tail (sym R-sym-S xsRys) = sym R-sym-S (tail xsRys)

trans : Trans R S T → Trans (Pointwise R) (Pointwise S) (Pointwise T)
head (trans RST-trans xsRys ysSzs) = RST-trans (head xsRys) (head ysSzs)
tail (trans RST-trans xsRys ysSzs) = trans RST-trans (tail xsRys) (tail ysSzs)

antisym : Antisym R S T → Antisym (Pointwise R) (Pointwise S) (Pointwise T)
head (antisym RST-antisym xsRys ysSxs) = RST-antisym (head xsRys) (head ysSxs)
tail (antisym RST-antisym xsRys ysSxs) = antisym RST-antisym (tail xsRys) (tail ysSxs)

tabulate⁺ : ∀ {f : ℕ → A} {g : ℕ → B} →
            (∀ i → R (f i) (g i)) → Pointwise R (Stream.tabulate f) (Stream.tabulate g)
head (tabulate⁺ f∼g) = f∼g 0
tail (tabulate⁺ f∼g) = tabulate⁺ (f∼g ∘ ℕ.suc)

tabulate⁻ : ∀ {f : ℕ → A} {g : ℕ → B} →
            Pointwise R (Stream.tabulate f) (Stream.tabulate g) → (∀ i → R (f i) (g i))
tabulate⁻ xsRys ℕ.zero = head xsRys
tabulate⁻ xsRys (ℕ.suc i) = tabulate⁻ (tail xsRys) i

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
