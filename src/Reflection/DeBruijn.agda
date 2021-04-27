------------------------------------------------------------------------
-- The Agda standard library
--
-- Weakening, strengthening and free variable check for reflected terms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.DeBruijn where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; nothing; just)
import Data.Maybe.Categorical as Maybe
import Function.Identity.Categorical as Identity
open import Category.Applicative using (RawApplicative)

open import Reflection
open import Reflection.Argument.Visibility using (Visibility)
import Reflection.Traversal as Traverse

private
  variable A : Set

------------------------------------------------------------------------
-- Weakening

module _ where

  open Traverse Identity.applicative

  private

    wkVar : ℕ → Cxt → ℕ → ℕ
    wkVar by (from , _) i = if i <ᵇ from then i else i + by

    actions : ℕ → Actions
    actions k = record defaultActions { onVar = wkVar k }

  weakenFrom′ : (Actions → Cxt → A → A) → (from by : ℕ) → A → A
  weakenFrom′ trav from by = trav (actions by) (from , []) -- not using the context part

  weakenFrom : (from by : ℕ) → Term → Term
  weakenFrom = weakenFrom′ traverseTerm

  weaken : (by : ℕ) → Term → Term
  weaken = weakenFrom 0

  weakenArgs : (by : ℕ) → Args Term → Args Term
  weakenArgs = weakenFrom′ traverseArgs 0

  weakenClauses : (by : ℕ) → Clauses → Clauses
  weakenClauses = weakenFrom′ traverseClauses 0


------------------------------------------------------------------------
-- η-expansion

private
  η : Visibility → (Args Term → Term) → Args Term → Term
  η h f args =
    lam h (abs "x" (f (weakenArgs 1 args ++
                       arg (arg-info h defaultModality) (var 0 []) ∷
                       [])))

η-expand : Visibility → Term → Term
η-expand h (var x      args) = η h (var (suc x)) args
η-expand h (con c      args) = η h (con c) args
η-expand h (def f      args) = η h (def f) args
η-expand h (pat-lam cs args) = η h (pat-lam (weakenClauses 1 cs)) args
η-expand h (meta x     args) = η h (meta x) args
η-expand h t@(lam _ _)       = t
η-expand h t@(pi _ _)        = t
η-expand h t@(agda-sort _)   = t
η-expand h t@(lit _)         = t
η-expand h t@unknown         = t


------------------------------------------------------------------------
-- Strengthening

module _ where

  open Traverse Maybe.applicative

  private
    strVar : ℕ → Cxt → ℕ → Maybe ℕ
    strVar by (from , Γ) i with i <ᵇ from | i <ᵇ from + by
    ... | true | _    = just i
    ... | _    | true = nothing
    ... | _    | _    = just (i ∸ by)

    actions : ℕ → Actions
    actions by = record defaultActions { onVar = strVar by }

  strengthenFromBy′ : (Actions → Cxt → A → Maybe A) → (from by : ℕ) → A → Maybe A
  strengthenFromBy′ trav from by = trav (actions by) (from , []) -- not using the context part

  strengthenFromBy : (from by : ℕ) → Term → Maybe Term
  strengthenFromBy = strengthenFromBy′ traverseTerm

  strengthenBy : (by : ℕ) → Term → Maybe Term
  strengthenBy = strengthenFromBy 0

  strengthenFrom : (from : ℕ) → Term → Maybe Term
  strengthenFrom from = strengthenFromBy from 1

  strengthen : Term → Maybe Term
  strengthen = strengthenFromBy 0 1


------------------------------------------------------------------------
-- Free variable check

module _ where

  private
    anyApplicative : RawApplicative (λ _ → Bool)
    anyApplicative .RawApplicative.pure _ = false
    anyApplicative .RawApplicative._⊛_    = _∨_

  open Traverse anyApplicative

  private
    fvVar : ℕ → Cxt → ℕ → Bool
    fvVar i (n , _) x = i + n ≡ᵇ x

    actions : ℕ → Actions
    actions i = record defaultActions { onVar = fvVar i }

  _∈FV_ : ℕ → Term → Bool
  i ∈FV t = traverseTerm (actions i) (0 , []) t
