------------------------------------------------------------------------
-- The Agda standard library
--
-- An apartness relation for ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Apartness where

open import Relation.Binary.Definitions using (Irreflexive; Symmetric)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Data.Sum using (inj₁; inj₂; map)
open import Data.Product using (_,_)
open import Function using (_∘_)

import Relation.Binary.Apartness as A
open A.Structures


data _#_ : ℕ → ℕ → Set where
  z#s : ∀ {m : ℕ} → zero # suc m
  s#z : ∀ {m : ℕ} → suc m # zero
  s#s : ∀ {m n : ℕ} → m # n → suc m # suc n

open A.Properties _#_

#-reduce : ∀ {m n : ℕ} → suc m # suc n → m # n
#-reduce (s#s x) = x

#-irrefl : Irreflexive _≡_ _#_
#-irrefl {zero} {zero} refl ()
#-irrefl refl (s#s x) = #-irrefl refl x

#-sym : Symmetric _#_
#-sym z#s = s#z
#-sym s#z = z#s
#-sym (s#s x) = s#s (#-sym x)

#-comp : Comparison
#-comp {y = zero} z#s = inj₂ z#s
#-comp {y = suc _} z#s = inj₁ z#s
#-comp {y = zero} s#z = inj₁ s#z
#-comp {y = suc _} s#z = inj₂ s#z
#-comp {y = zero} (s#s x#z) = inj₁ s#z
#-comp {y = suc _} (s#s x#z) = map s#s s#s (#-comp x#z)

#-apart : IsApartness _≡_ _#_
#-apart = record { irrefl = #-irrefl ; sym = #-sym ; comp = #-comp }

#-tight : Tight _≡_ _#_
#-tight {zero} {zero} _ = refl
#-tight {suc x} {zero} (¬x#y , _) with ¬x#y s#z
... | ()
#-tight {zero} {suc y} (_ , ¬y#x) with ¬y#x s#z
... | ()
#-tight {suc x} {suc y} (¬sx#sy , ¬sy#sx) =
  cong suc (#-tight (¬sx#sy ∘ s#s , ¬sy#sx ∘ s#s))




module Test where
  open import Relation.Nullary using (¬_)
  open import Data.Product using (_×_)

  sm≢sn→m≢n : ∀ {m n} → ¬ suc m ≡ suc n → ¬ m ≡ n
  sm≢sn→m≢n sm≢sn m≡n = sm≢sn (cong suc m≡n)

  ≢→# : ∀ {x y} → ¬ (x ≡ y) → x # y
  ≢→# {zero} {zero} z≢z with z≢z refl
  ... | ()
  ≢→# {zero} {suc y} _ = z#s
  ≢→# {suc x} {zero} _ = s#z
  ≢→# {suc x} {suc y} sx≢sy = s#s (≢→# (sm≢sn→m≢n sx≢sy))
