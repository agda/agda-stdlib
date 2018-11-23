open import Relation.Binary hiding (_⇒_)

module Category.Monad.Monotone.Error {ℓ}(pre : Preorder ℓ ℓ ℓ)(Exc : Set ℓ) where

open import Function
open import Level hiding (lift)
open import Data.Sum

open import Relation.Unary
open import Relation.Unary.Closure.Preorder pre
open import Relation.Unary.PredicateTransformer

open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.Identity pre

open Preorder pre renaming (Carrier to I)

ErrorT : Pt I ℓ → Pt I ℓ
ErrorT M P = M (λ i → Exc ⊎ P i)

Error = ErrorT Identity

record ErrorMonad (M : Pt I ℓ) : Set (suc ℓ) where
  field
    throw      : ∀ {P i} → Exc → M P i
    try_catch_ : ∀ {P}   → M P ⊆ (□ (const Exc ⇒ M P)) ⇒ M P

module _ {M} (Mon : RawMPMonad M) where
  private module M = RawMPMonad Mon

  open RawMPMonad
  errorT-monad : RawMPMonad (ErrorT M)
  return errorT-monad px   = M.return (inj₂ px)
  _≥=_   errorT-monad px f =
    px M.≥= λ where
      v (inj₁ e) → M.return (inj₁ e)
      v (inj₂ x) → f v x

  open ErrorMonad
  errorT-monad-ops : ErrorMonad (ErrorT M)
  throw      errorT-monad-ops e   = M.return (inj₁ e)
  try_catch_ errorT-monad-ops c f =
    c M.≥= λ where
      v (inj₁ e) → f v e
      v (inj₂ x) → M.return (inj₂ x)

  lift-error : ∀ {P} → M P ⊆ ErrorT M P
  lift-error x = x M.>>= (λ z → M.return (inj₂ z))
