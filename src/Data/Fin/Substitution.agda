------------------------------------------------------------------------
-- The Agda standard library
--
-- Substitutions
------------------------------------------------------------------------

-- Uses a variant of Conor McBride's technique from "Type-Preserving
-- Renaming and Substitution".

-- See Data.Fin.Substitution.Example for an example of how this module
-- can be used: a definition of substitution for the untyped
-- λ-calculus.

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Substitution where

open import Data.Nat hiding (_⊔_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Vec.Base
open import Function as Fun using (flip)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  as Star using (Star; ε; _◅_)
open import Level using (Level; _⊔_)
import Level as L
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- General functionality

-- A Sub T m n is a substitution which, when applied to something with
-- at most m variables, yields something with at most n variables.

Sub : ∀ {ℓ} → Pred ℕ ℓ → ℕ → ℕ → Set ℓ
Sub T m n = Vec (T n) m

-- A /reversed/ sequence of matching substitutions.

Subs : ∀ {ℓ} → Pred ℕ ℓ → ℕ → ℕ → Set ℓ
Subs T = flip (Star (flip (Sub T)))

-- Some simple substitutions.

record Simple {ℓ : Level} (T : Pred ℕ ℓ) : Set ℓ where
  infix  10 _↑
  infixl 10 _↑⋆_ _↑✶_

  field
    var    : ∀ {n} → Fin n → T n      -- Takes variables to Ts.
    weaken : ∀ {n} → T n → T (suc n)  -- Weakens Ts.

  -- Lifting.

  _↑ : ∀ {m n} → Sub T m n → Sub T (suc m) (suc n)
  ρ ↑ = var zero ∷ map weaken ρ

  _↑⋆_ : ∀ {m n} → Sub T m n → ∀ k → Sub T (k + m) (k + n)
  ρ ↑⋆ zero  = ρ
  ρ ↑⋆ suc k = (ρ ↑⋆ k) ↑

  _↑✶_ : ∀ {m n} → Subs T m n → ∀ k → Subs T (k + m) (k + n)
  ρs ↑✶ k = Star.gmap (_+_ k) (λ ρ → ρ ↑⋆ k) ρs

  -- The identity substitution.

  id : ∀ {n} → Sub T n n
  id {zero}  = []
  id {suc n} = id ↑

  -- Weakening.

  wk⋆ : ∀ k {n} → Sub T n (k + n)
  wk⋆ zero    = id
  wk⋆ (suc k) = map weaken (wk⋆ k)

  wk : ∀ {n} → Sub T n (suc n)
  wk = wk⋆ 1

  -- A substitution which only replaces the first variable.

  sub : ∀ {n} → T n → Sub T (suc n) n
  sub t = t ∷ id

-- Application of substitutions.

record Application {ℓ₁ ℓ₂ : Level} (T₁ : Pred ℕ ℓ₁) (T₂ : Pred ℕ ℓ₂) :
    Set (ℓ₁ ⊔ ℓ₂) where
  infixl 8 _/_ _/✶_
  infixl 9 _⊙_

  -- Post-application of substitutions to things.

  field _/_ : ∀ {m n} → T₁ m → Sub T₂ m n → T₁ n

  -- Reverse composition. (Fits well with post-application.)

  _⊙_ : ∀ {m n k} → Sub T₁ m n → Sub T₂ n k → Sub T₁ m k
  ρ₁ ⊙ ρ₂ = map (λ t → t / ρ₂) ρ₁

  -- Application of multiple substitutions.

  _/✶_ : ∀ {m n} → T₁ m → Subs T₂ m n → T₁ n
  _/✶_ = Star.gfold Fun.id _ (flip _/_) {k = zero}

-- A combination of the two records above.

record Subst {ℓ : Level} (T : Pred ℕ ℓ) : Set ℓ where
  field
    simple      : Simple      T
    application : Application T T

  open Simple      simple      public
  open Application application public

  -- Composition of multiple substitutions.

  ⨀ : ∀ {m n} → Subs T m n → Sub T m n
  ⨀ ε        = id
  ⨀ (ρ ◅ ε)  = ρ  -- Convenient optimisation; simplifies some proofs.
  ⨀ (ρ ◅ ρs) = ⨀ ρs ⊙ ρ

------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Liftings from T₁ to T₂.

record Lift {ℓ₁ ℓ₂ : Level} (T₁ : Pred ℕ ℓ₁) (T₂ : Pred ℕ ℓ₂) :
    Set (ℓ₁ ⊔ ℓ₂) where
  field
    simple : Simple T₁
    lift   : ∀ {n} → T₁ n → T₂ n

  open Simple simple public

-- Variable substitutions (renamings).

module VarSubst where

  subst : Subst Fin
  subst = record
    { simple      = record { var = Fun.id; weaken = suc }
    ; application = record { _/_ = flip lookup }
    }

  open Subst subst public

-- "Term" substitutions.

record TermSubst (T : Pred ℕ L.zero) : Set₁ where
  field
    var : ∀ {n} → Fin n → T n
    app : ∀ {T′ : Pred ℕ L.zero} → Lift T′ T → ∀ {m n} → T m → Sub T′ m n → T n

  module Lifted {T′ : Pred ℕ L.zero} (lift : Lift T′ T) where
    application : Application T T′
    application = record { _/_ = app lift }

    open Lift lift public
    open Application application public

  varLift : Lift Fin T
  varLift = record { simple = VarSubst.simple; lift = var }

  infix 8 _/Var_

  _/Var_ : ∀ {m n} → T m → Sub Fin m n → T n
  _/Var_ = app varLift

  simple : Simple T
  simple = record
    { var    = var
    ; weaken = λ t → t /Var VarSubst.wk
    }

  termLift : Lift T T
  termLift = record { simple = simple; lift = Fun.id }

  subst : Subst T
  subst = record
    { simple      = simple
    ; application = Lifted.application termLift
    }

  open Subst subst public hiding (var; simple)
