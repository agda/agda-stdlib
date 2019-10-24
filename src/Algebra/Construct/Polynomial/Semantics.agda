{-# OPTIONS --without-K --safe #-}

-- "Evaluating" a polynomial, using Horner's method.
open import Algebra.Construct.Polynomial.Parameters

module Algebra.Construct.Polynomial.Semantics
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
  where

open import Data.Nat     using (ℕ; suc; zero; _≤′_; ≤′-step; ≤′-refl)
open import Data.Vec     using (Vec; []; _∷_; uncons)
open import Data.List    using ([]; _∷_)
open import Data.Product using (_,_; _×_)
open import Data.List.Kleene using (_+; _*; ∹_; _&_; [])

open Homomorphism homo
open import Algebra.Construct.Polynomial.Base from

open import Algebra.Operations.Ring.Compact rawRing

drop : ∀ {i n} → i ≤′ n → Vec Carrier n → Vec Carrier i
drop ≤′-refl Ρ = Ρ
drop (≤′-step si≤n) (_ ∷ Ρ) = drop si≤n Ρ

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
  (x , []) ⟦∷⟧ (ρ , ρs) = ⟦ x ⟧ ρs
  (x , (∹ xs )) ⟦∷⟧ (ρ , ρs) = ρ * Σ⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs

  Σ⟦_⟧ : ∀ {n} → Coeff n + → (Carrier × Vec Carrier n) → Carrier
  Σ⟦ x ≠0 Δ i & xs ⟧ (ρ , ρs) = ((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ i

  ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
  ⟦ Κ x  ⊐ i≤n ⟧ _ = ⟦ x ⟧ᵣ
  ⟦ Σ xs ⊐ i≤n ⟧ Ρ = Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
{-# INLINE ⟦_⟧ #-}
{-# INLINE Σ⟦_⟧ #-}
--------------------------------------------------------------------------------
-- Performance
--------------------------------------------------------------------------------
-- As you might imagine, the implementation of the functions above seriously
-- affect performance. What you might not realise, though, is that the most
-- important component is the *order of the arguments*. For instance, if
-- we change:
--
--   (x , xs) ⟦∷⟧ (ρ , ρs) = ρ * Σ⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs
--
-- To:
--
--   (x , xs) ⟦∷⟧ (ρ , ρs) = ⟦ x ⟧ ρs +  Σ⟦ xs ⟧ (ρ , ρs) * ρ
--
-- We get a function that's several orders of magnitude slower!
