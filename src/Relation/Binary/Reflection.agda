------------------------------------------------------------------------
-- The Agda standard library
--
-- Helpers intended to ease the development of "tactics" which use
-- proof by reflection
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base as Vec using (Vec; allFin)
open import Function.Base using (id; _⟨_⟩_)
open import Function.Bundles using (module Equivalence)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

-- Think of the parameters as follows:
--
-- * Expr:    A representation of code.
-- * var:     The Expr type should support a notion of variables.
-- * ⟦_⟧:     Computes the semantics of an expression. Takes an
--            environment mapping variables to something.
-- * ⟦_⇓⟧:    Computes the semantics of the normal form of the
--            expression.
-- * correct: Normalisation preserves the semantics.
--
-- Given these parameters two "tactics" are returned, prove and solve.
--
-- For an example of the use of this module, see Algebra.RingSolver.

module Relation.Binary.Reflection
         {e a s}
         {Expr : ℕ → Set e} {A : Set a}
         (Sem : Setoid a s)
         (var : ∀ {n} → Fin n → Expr n)
         (⟦_⟧ ⟦_⇓⟧ : ∀ {n} → Expr n → Vec A n → Setoid.Carrier Sem)
         (correct : ∀ {n} (e : Expr n) ρ →
                    ⟦ e ⇓⟧ ρ ⟨ Setoid._≈_ Sem ⟩ ⟦ e ⟧ ρ)
         where

open import Data.Vec.N-ary
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open Setoid Sem
open ≈-Reasoning Sem

-- If two normalised expressions are semantically equal, then their
-- non-normalised forms are also equal.

prove : ∀ {n} (ρ : Vec A n) e₁ e₂ →
        ⟦ e₁ ⇓⟧ ρ ≈ ⟦ e₂ ⇓⟧ ρ →
        ⟦ e₁  ⟧ ρ ≈ ⟦ e₂  ⟧ ρ
prove ρ e₁ e₂ hyp = begin
  ⟦ e₁  ⟧ ρ ≈⟨ sym (correct e₁ ρ) ⟩
  ⟦ e₁ ⇓⟧ ρ ≈⟨ hyp ⟩
  ⟦ e₂ ⇓⟧ ρ ≈⟨ correct e₂ ρ ⟩
  ⟦ e₂  ⟧ ρ ∎

-- Applies the function to all possible "variables".

close : ∀ {A : Set e} n → N-ary n (Expr n) A → A
close n f = f $ⁿ Vec.map var (allFin n)

-- A variant of prove which should in many cases be easier to use,
-- because variables and environments are handled in a less explicit
-- way.
--
-- If the type signature of solve is a bit daunting, then it may be
-- helpful to instantiate n with a small natural number and normalise
-- the remainder of the type.

solve : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
  Eqʰ n _≈_ (curryⁿ ⟦ proj₁ (close n f) ⇓⟧) (curryⁿ ⟦ proj₂ (close n f) ⇓⟧) →
  Eq  n _≈_ (curryⁿ ⟦ proj₁ (close n f)  ⟧) (curryⁿ ⟦ proj₂ (close n f)  ⟧)
solve n f hyp =
  curryⁿ-cong _≈_ ⟦ proj₁ (close n f) ⟧ ⟦ proj₂ (close n f) ⟧
    (λ ρ → prove ρ (proj₁ (close n f)) (proj₂ (close n f))
             (curryⁿ-cong⁻¹ _≈_
                ⟦ proj₁ (close n f) ⇓⟧ ⟦ proj₂ (close n f) ⇓⟧
                (Eqʰ-to-Eq n _≈_ hyp) ρ))

-- A variant of solve which does not require that the normal form
-- equality is proved for an arbitrary environment.

solve₁ : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
         ∀ⁿ n (curryⁿ λ ρ →
                 ⟦ proj₁ (close n f) ⇓⟧ ρ ≈ ⟦ proj₂ (close n f) ⇓⟧ ρ →
                 ⟦ proj₁ (close n f)  ⟧ ρ ≈ ⟦ proj₂ (close n f)  ⟧ ρ)
solve₁ n f =
  Equivalence.from (uncurry-∀ⁿ n) λ ρ →
    ≡.subst id (≡.sym (left-inverse (λ _ → _ ≈ _ → _ ≈ _) ρ))
      (prove ρ (proj₁ (close n f)) (proj₂ (close n f)))

-- A variant of _,_ which is intended to make uses of solve and solve₁
-- look a bit nicer.

infix 4 _⊜_

_⊜_ : ∀ {n} → Expr n → Expr n → Expr n × Expr n
_⊜_ = _,_
