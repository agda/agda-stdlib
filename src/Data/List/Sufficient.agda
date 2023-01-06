------------------------------------------------------------------------
-- The Agda standard library
--
-- 'Sufficient' lists: a structurally inductive view of lists xs
-- as given by xs ≡ non-empty prefix + sufficient suffix
--
-- Useful for termination arguments for function definitions
-- which provably consume a non-empty (but otherwise arbitrary) prefix
-- *without* having to resort to ancillary WF induction on length etc.
-- e.g. lexers, parsers etc.
--
-- Credited by Conor McBride as originally due to James McKinna
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Sufficient {a} {A : Set a} where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Sufficient builder

suffAcc : ∀ {b} (B :  List A → Set b) (xs : List A) → Set (a ⊔ b)
suffAcc B xs = ∀ {a} {prefix} suffix → xs ≡ a ∷ prefix ++ suffix → B suffix

------------------------------------------------------------------------
-- Sufficient view

data Sufficient : (xs : List A) → Set a where

  acc : ∀ {xs} (ih : suffAcc Sufficient xs) → Sufficient xs


------------------------------------------------------------------------
-- Sufficient properties

-- constructors (typically not for export)

module Constructors where

  []⁺ : Sufficient []
  []⁺ = acc λ _ ()

  ∷⁺ : ∀ {x} {xs} → Sufficient xs → Sufficient (x ∷ xs)
  ∷⁺ {xs = xs} suff-xs@(acc hyp) = acc λ { _ refl → suf _ refl }
    where suf : ∀ prefix {suffix} → xs ≡ prefix ++ suffix → Sufficient suffix
          suf []               refl = suff-xs
          suf (_ ∷ _) {suffix} eq   = hyp suffix eq

-- destructors

module Destructors where

  ++⁻ : ∀ xs {ys} → Sufficient (xs ++ ys) → Sufficient ys
  ++⁻ []            suff-ys   = suff-ys
  ++⁻ (x ∷ xs) {ys} (acc hyp) = hyp ys refl

  ∷⁻ : ∀ {x} {xs} → Sufficient (x ∷ xs) → Sufficient xs
  ∷⁻ {x} = ++⁻ [ x ]


------------------------------------------------------------------------
-- Sufficient view covering property

module _ where

  open Constructors

  sufficient : (xs : List A) → Sufficient xs
  sufficient []       = []⁺
  sufficient (x ∷ xs) = ∷⁺ (sufficient xs)

------------------------------------------------------------------------
-- Recursion on the sufficient view

module _ {b} (B : List A → Set b) where

  suffRec : ∀ {zs} (rec : ∀ {ys} (ih : suffAcc B ys) → B ys) → B zs
  suffRec  {zs} = suffRec′ (sufficient zs)
    where
      suffRec′ : ∀ {zs} → Sufficient zs →
                 (rec : ∀ {ys} (ih : suffAcc B ys) → B ys) →
                 B zs
      suffRec′ (acc hyp) rec = rec (λ xs eq → suffRec′ (hyp xs eq) rec)

