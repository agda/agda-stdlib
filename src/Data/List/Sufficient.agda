------------------------------------------------------------------------
-- The Agda standard library
--
-- 'Sufficient' lists: a structurally inductive view of lists xs
-- as given by xs ≡ non-empty prefix + sufficient suffix
--
-- Useful for termination arguments for function definitions
-- which provably consume a non-empty (but otherwise arbitrary) prefix
-- e.g. lexers, parsers etc.
--
-- Credited by Conor McBride as originally due to James McKinna
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Sufficient {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    x : A
    xs : List A


------------------------------------------------------------------------
-- Sufficient view

data Sufficient : (xs : List A) → Set a where

  suff-acc : ∀ {xs} →
             (suff_ih : ∀ {a} {pre suff} → xs ≡ a ∷ (pre ++ suff) →
                        Sufficient suff) →
             Sufficient xs


------------------------------------------------------------------------
-- Sufficient properties: constructors

[]⁺ : Sufficient []
[]⁺ = suff-acc λ ()

∷⁺ : Sufficient xs → Sufficient (x ∷ xs)
∷⁺ {xs = xs} suff-xs@(suff-acc acc) = suff-acc λ { refl → suf _ refl }
  where
    suf : ∀ pre {suff} → xs ≡ pre ++ suff → Sufficient suff
    suf []        refl = suff-xs
    suf (a ∷ pre) eq   = acc eq

------------------------------------------------------------------------
-- Sufficient view covering property

sufficient : (xs : List A) → Sufficient xs
sufficient []       = []⁺
sufficient (x ∷ xs) = ∷⁺ (sufficient xs)
