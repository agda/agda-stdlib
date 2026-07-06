------------------------------------------------------------------------
-- The Agda standard library
--
-- Finding the maximum/minimum values in a list, specialised for Nat
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This specialised module is needed as `m < n` for Nat is not
-- implemented as `m ≤ n × m ≢ n`.

module Data.List.Extrema.Nat where

open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties as ℕ using (≤∧≢⇒<; <⇒≤; <⇒≢)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.List.Base using (List)
import Data.List.Extrema
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Product.Base using (_×_; _,_; uncurry′)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)

private
  variable
    a : Level
    A : Set a

  <⇒<× : ∀ {x y} → x < y → x ≤ y × x ≢ y
  <⇒<× x<y = <⇒≤ x<y , <⇒≢ x<y

  <×⇒< : ∀ {x y} → x ≤ y × x ≢ y → x < y
  <×⇒< (x≤y , x≢y) = ≤∧≢⇒< x≤y x≢y

  module Extrema = Data.List.Extrema ℕ.≤-totalOrder

------------------------------------------------------------------------
-- Re-export the contents of Extrema

open Extrema public
  hiding
  ( f[argmin]<v⁺; v<f[argmin]⁺; argmin[xs]<argmin[ys]⁺
  ; f[argmax]<v⁺; v<f[argmax]⁺; argmax[xs]<argmax[ys]⁺
  ; min<v⁺; v<min⁺; min[xs]<min[ys]⁺
  ; max<v⁺; v<max⁺; max[xs]<max[ys]⁺
  )

------------------------------------------------------------------------
-- New versions of the proofs involving _<_

-- Argmin

f[argmin]<v⁺ : ∀ {f : A → ℕ} {v} ⊤ xs →
              (f ⊤ < v) ⊎ (Any (λ x → f x < v) xs) →
              f (argmin f ⊤ xs) < v
f[argmin]<v⁺ ⊤ xs arg =
  <×⇒< (Extrema.f[argmin]<v⁺ ⊤ xs (Sum.map <⇒<× (Any.map <⇒<×) arg))

v<f[argmin]⁺ : ∀ {f : A → ℕ} {v ⊤ xs} →
              v < f ⊤ → All (λ x → v < f x) xs →
              v < f (argmin f ⊤ xs)
v<f[argmin]⁺ {v} v<f⊤ v<fxs =
  <×⇒< (Extrema.v<f[argmin]⁺ (<⇒<× v<f⊤) (All.map <⇒<× v<fxs))

argmin[xs]<argmin[ys]⁺ : ∀ {f g : A → ℕ} ⊤₁ {⊤₂} xs {ys} →
                        (f ⊤₁ < g ⊤₂) ⊎ Any (λ x → f x < g ⊤₂) xs →
                        All (λ y → (f ⊤₁ < g y) ⊎ Any (λ x → f x < g y) xs) ys →
                        f (argmin f ⊤₁ xs) < g (argmin g ⊤₂ ys)
argmin[xs]<argmin[ys]⁺ ⊤₁ xs xs<⊤₂ xs<ys =
  v<f[argmin]⁺ (f[argmin]<v⁺ ⊤₁ _ xs<⊤₂) (All.map (f[argmin]<v⁺ ⊤₁ xs) xs<ys)

-- Argmax

v<f[argmax]⁺ : ∀ {f : A → ℕ} {v} ⊥ xs → (v < f ⊥) ⊎ (Any (λ x → v < f x) xs) →
              v < f (argmax f ⊥ xs)
v<f[argmax]⁺ ⊥ xs leq = <×⇒< (Extrema.v<f[argmax]⁺ ⊥ xs (Sum.map <⇒<× (Any.map <⇒<×) leq))

f[argmax]<v⁺ : ∀ {f : A → ℕ} {v ⊥ xs} → f ⊥ < v → All (λ x → f x < v) xs →
              f (argmax f ⊥ xs) < v
f[argmax]<v⁺ ⊥<v xs<v = <×⇒< (Extrema.f[argmax]<v⁺ (<⇒<× ⊥<v) (All.map <⇒<× xs<v))

argmax[xs]<argmax[ys]⁺ : ∀ {f g : A → ℕ} {⊥₁} ⊥₂ {xs} ys →
                         (f ⊥₁ < g ⊥₂) ⊎ Any (λ y → f ⊥₁ < g y) ys →
                         All (λ x → (f x < g ⊥₂) ⊎ Any (λ y → f x < g y) ys) xs →
                         f (argmax f ⊥₁ xs) < g (argmax g ⊥₂ ys)
argmax[xs]<argmax[ys]⁺ ⊥₂ ys ⊥₁<ys xs<ys =
  f[argmax]<v⁺ (v<f[argmax]⁺ ⊥₂ _ ⊥₁<ys) (All.map (v<f[argmax]⁺ ⊥₂ ys) xs<ys)

-- Min

min<v⁺ : ∀ {v} ⊤ xs → ⊤ < v ⊎ Any (_< v) xs → min ⊤ xs < v
min<v⁺ = f[argmin]<v⁺

v<min⁺ : ∀ {v ⊤ xs} → v < ⊤ → All (v <_) xs → v < min ⊤ xs
v<min⁺ = v<f[argmin]⁺

min[xs]<min[ys]⁺ : ∀ ⊤₁ {⊤₂} xs {ys} → (⊤₁ < ⊤₂) ⊎ Any (_< ⊤₂) xs →
                   All (λ y → (⊤₁ < y) ⊎ Any (λ x → x < y) xs) ys →
                   min ⊤₁ xs < min ⊤₂ ys
min[xs]<min[ys]⁺ = argmin[xs]<argmin[ys]⁺

-- Max

max<v⁺ : ∀ {v ⊥ xs} → ⊥ < v → All (_< v) xs → max ⊥ xs < v
max<v⁺ = f[argmax]<v⁺

v<max⁺ : ∀ {v} ⊥ xs → v < ⊥ ⊎ Any (v <_) xs → v < max ⊥ xs
v<max⁺ = v<f[argmax]⁺

max[xs]<max[ys]⁺ : ∀ {⊥₁} ⊥₂ {xs} ys → ⊥₁ < ⊥₂ ⊎ Any (⊥₁ <_) ys →
                   All (λ x → x < ⊥₂ ⊎ Any (x <_) ys) xs →
                   max ⊥₁ xs < max ⊥₂ ys
max[xs]<max[ys]⁺ = argmax[xs]<argmax[ys]⁺
