------------------------------------------------------------------------
-- The Agda standard library
--
-- 'Sufficient' lists: a structurally inductive view of lists xs
-- as given by xs ≡ non-empty prefix + sufficient suffix
--
-- Useful for termination arguments for function definitions
-- which provably consume a non-empty (but otherwise arbitrary) prefix
-- *without* having to resort to ancillary WF inductions on length etc.
-- e.g. lexers, parsers etc.
--
-- Credited by Conor McBride as originally due to James McKinna
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Sufficient {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


------------------------------------------------------------------------
-- Sufficient view

data Sufficient : (xs : List A) → Set a where

  suff-acc : ∀ {xs} →
             (suff_ih : ∀ {a} {prefix suffix} → xs ≡ a ∷ (prefix ++ suffix) →
                        Sufficient suffix) →
             Sufficient xs


------------------------------------------------------------------------
-- Sufficient properties: constructors (typically not for export)

module Constructors where

  []⁺ : Sufficient []
  []⁺ = suff-acc λ ()

  ∷⁺ : ∀ {x} {xs} → Sufficient xs → Sufficient (x ∷ xs)
  ∷⁺ {xs = xs} suff-xs@(suff-acc acc) = suff-acc λ { refl → suf _ refl }
    where suf : ∀ prefix {suffix} → xs ≡ prefix ++ suffix → Sufficient suffix
          suf []           refl = suff-xs
          suf (a ∷ prefix) eq   = acc eq

------------------------------------------------------------------------
-- Sufficient view covering property

module _ where

  open Constructors

  sufficient : (xs : List A) → Sufficient xs
  sufficient []       = []⁺
  sufficient (x ∷ xs) = ∷⁺ (sufficient xs)
