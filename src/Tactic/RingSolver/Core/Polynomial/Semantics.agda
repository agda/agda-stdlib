------------------------------------------------------------------------
-- The Agda standard library
--
-- "Evaluating" a polynomial, using Horner's method.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Semantics
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat     using (ℕ; suc; zero; _≤′_; ≤′-step; ≤′-refl)
open import Data.Vec     using (Vec; []; _∷_; uncons)
open import Data.List    using ([]; _∷_)
open import Data.Product using (_,_; _×_)
open import Data.List.Kleene using (_+; _*; ∹_; _&_; [])

open Homomorphism homo
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Algebra.Operations.Ring rawRing

drop : ∀ {i n} → i ≤′ n → Vec Carrier n → Vec Carrier i
drop ≤′-refl         xs       = xs
drop (≤′-step i+1≤n) (_ ∷ xs) = drop i+1≤n xs

drop-1 : ∀ {i n} → suc i ≤′ n → Vec Carrier n → Carrier × Vec Carrier i
drop-1 si≤n xs = uncons (drop si≤n xs)
{-# INLINE drop-1 #-}

_*⟨_⟩^_ : Carrier → Carrier → ℕ → Carrier
x *⟨ ρ ⟩^ zero = x
x *⟨ ρ ⟩^ suc i = ρ ^ i +1 * x
{-# INLINE _*⟨_⟩^_ #-}

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------
-- Why do we have three functions here? Why are they so weird looking?
--
-- These three functions are the main bottleneck for all of the proofs: as such,
-- slight changes can dramatically affect the length of proof code.

mutual

  _⟦∷⟧_ : ∀ {n} → Poly n × Coeff n * → Carrier × Vec Carrier n → Carrier
  (x , [])     ⟦∷⟧ (ρ , ρs) = ⟦ x ⟧ ρs
  (x , (∹ xs)) ⟦∷⟧ (ρ , ρs) = ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs

  ⅀⟦_⟧ : ∀ {n} → Coeff n + → (Carrier × Vec Carrier n) → Carrier
  ⅀⟦ x ≠0 Δ i & xs ⟧ (ρ , ρs) = ((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ i
  {-# INLINE ⅀⟦_⟧ #-}

  ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
  ⟦ Κ x  ⊐ i≤n ⟧ _ = ⟦ x ⟧ᵣ
  ⟦ ⅀ xs ⊐ i≤n ⟧ Ρ = ⅀⟦ xs ⟧ (drop-1 i≤n Ρ)
  {-# INLINE ⟦_⟧ #-}

--------------------------------------------------------------------------------
-- Performance
--------------------------------------------------------------------------------
-- As you might imagine, the implementation of the functions above seriously
-- affect performance. What you might not realise, though, is that the most
-- important component is the *order of the arguments*. For instance, if
-- we change:
--
--   (x , xs) ⟦∷⟧ (ρ , ρs) = ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs
--
-- To:
--
--   (x , xs) ⟦∷⟧ (ρ , ρs) = ⟦ x ⟧ ρs +  ⅀⟦ xs ⟧ (ρ , ρs) * ρ
--
-- We get a function that's several orders of magnitude slower!
