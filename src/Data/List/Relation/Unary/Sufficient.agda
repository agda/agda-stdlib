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

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Sufficient where

open import Level using (Level; _⊔_)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

private
  variable

    a b : Level
    A : Set a
    x : A
    xs : List A

------------------------------------------------------------------------
-- Sufficient builder

suffAcc : {A : Set a} (B :  List A → Set b) (xs : List A) → Set (a ⊔ b)
suffAcc B xs = ∀ {x} {prefix} suffix → xs ≡ x ∷ prefix ++ suffix → B suffix

------------------------------------------------------------------------
-- Sufficient view

data Sufficient {A : Set a} : (xs : List A) → Set a where

  acc : ∀ {xs} (ih : suffAcc Sufficient xs) → Sufficient xs


------------------------------------------------------------------------
-- Sufficient properties

-- constructors

module Constructors where

  []⁺ : Sufficient {A = A} []
  []⁺ = acc λ _ ()

  ∷⁺ : Sufficient xs → Sufficient (x ∷ xs)
  ∷⁺ {xs = xs} suffices@(acc hyp) = acc λ { _ refl → suf _ refl }
    where
      suf : ∀ prefix {suffix} → xs ≡ prefix ++ suffix → Sufficient suffix
      suf []               refl = suffices
      suf (_ ∷ _) {suffix} eq   = hyp suffix eq

-- destructors

module Destructors where

  acc-inverse : ∀ ys → Sufficient (x ∷ xs ++ ys) → Sufficient ys
  acc-inverse ys (acc hyp) = hyp ys refl

  ++⁻ : ∀ xs {ys : List A} → Sufficient (xs ++ ys) → Sufficient ys
  ++⁻ []            suffices = suffices
  ++⁻ (x ∷ xs) {ys} suffices = acc-inverse ys suffices

  ∷⁻ : Sufficient (x ∷ xs) → Sufficient xs
  ∷⁻ {x = x} = ++⁻ [ x ]


------------------------------------------------------------------------
-- Sufficient view covering property

module View where

  open Constructors

  sufficient : (xs : List A) → Sufficient xs
  sufficient []       = []⁺
  sufficient (x ∷ xs) = ∷⁺ (sufficient xs)

------------------------------------------------------------------------
-- Recursion on the sufficient view

module _ (B : List A → Set b) (rec : ∀ ys → (ih : suffAcc B ys) → B ys)
  where

  open View

  suffRec′ : ∀ {zs} → Sufficient zs → B zs
  suffRec′ {zs} (acc hyp) = rec zs (λ xs eq → suffRec′ (hyp xs eq))

  suffRec : ∀ zs → B zs
  suffRec zs = suffRec′ (sufficient zs)
