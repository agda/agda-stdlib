------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Negation where

open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; if_then_else_; not)
open import Data.Empty
open import Data.Product as Prod
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function
open import Level
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary

private
  variable
    a p q r w : Level
    A : Set a
    P : Set p
    Q : Set q
    R : Set r
    Whatever : Set w

------------------------------------------------------------------------
-- Uses of negation

contradiction : P → ¬ P → Whatever
contradiction p ¬p = ⊥-elim (¬p p)

contraposition : (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

-- Note also the following use of flip:

private
  note : (P → ¬ Q) → Q → ¬ P
  note = flip

-- If we can decide P, then we can decide its negation.

¬-reflects : ∀ {b} → Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

¬? : Dec P → Dec (¬ P)
does  (¬? p?) = not (does p?)
proof (¬? p?) = ¬-reflects (proof p?)

------------------------------------------------------------------------
-- Quantifier juggling

module _ {P : Pred A p} where

  ∃⟶¬∀¬ : ∃ P → ¬ (∀ x → ¬ P x)
  ∃⟶¬∀¬ = flip uncurry

  ∀⟶¬∃¬ : (∀ x → P x) → ¬ ∃ λ x → ¬ P x
  ∀⟶¬∃¬ ∀xPx (x , ¬Px) = ¬Px (∀xPx x)

  ¬∃⟶∀¬ : ¬ ∃ (λ x → P x) → ∀ x → ¬ P x
  ¬∃⟶∀¬ = curry

  ∀¬⟶¬∃ : (∀ x → ¬ P x) → ¬ ∃ (λ x → P x)
  ∀¬⟶¬∃ = uncurry

  ∃¬⟶¬∀ : ∃ (λ x → ¬ P x) → ¬ (∀ x → P x)
  ∃¬⟶¬∀ = flip ∀⟶¬∃¬

------------------------------------------------------------------------
-- Double-negation

¬¬-map : (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contraposition (contraposition f)

-- Stability under double-negation.

Stable : Set p → Set p
Stable P = ¬ ¬ P → P

-- Everything is stable in the double-negation monad.

stable : ¬ ¬ Stable P
stable ¬[¬¬p→p] = ¬[¬¬p→p] (λ ¬¬p → ⊥-elim (¬¬p (¬[¬¬p→p] ∘ const)))

-- Negated predicates are stable.

negated-stable : Stable (¬ P)
negated-stable ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)

-- Decidable predicates are stable.

decidable-stable : Dec P → Stable P
decidable-stable (yes p) ¬¬p = p
decidable-stable (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬-drop-Dec : Dec (¬ ¬ P) → Dec (¬ P)
¬-drop-Dec ¬¬p? = map′ negated-stable contradiction (¬? ¬¬p?)

-- Double-negation is a monad (if we assume that all elements of ¬ ¬ P
-- are equal).

¬¬-Monad : RawMonad (λ (P : Set p) → ¬ ¬ P)
¬¬-Monad = record
  { return = contradiction
  ; _>>=_  = λ x f → negated-stable (¬¬-map f x)
  }

¬¬-push : ∀ {P : Set p} {Q : P → Set q} →
          ¬ ¬ ((x : P) → Q x) → (x : P) → ¬ ¬ Q x
¬¬-push ¬¬P⟶Q P ¬Q = ¬¬P⟶Q (λ P⟶Q → ¬Q (P⟶Q P))

-- A double-negation-translated variant of excluded middle (or: every
-- nullary relation is decidable in the double-negation monad).

excluded-middle : ¬ ¬ Dec P
excluded-middle ¬h = ¬h (no (λ p → ¬h (yes p)))

-- If Whatever is instantiated with ¬ ¬ something, then this function
-- is call with current continuation in the double-negation monad, or,
-- if you will, a double-negation translation of Peirce's law.
--
-- In order to prove ¬ ¬ P one can assume ¬ P and prove ⊥. However,
-- sometimes it is nice to avoid leaving the double-negation monad; in
-- that case this function can be used (with Whatever instantiated to
-- ⊥).

call/cc : ((P → Whatever) → ¬ ¬ P) → ¬ ¬ P
call/cc hyp ¬p = hyp (λ p → ⊥-elim (¬p p)) ¬p

-- The "independence of premise" rule, in the double-negation monad.
-- It is assumed that the index set (Q) is inhabited.

independence-of-premise : ∀ {P : Set p} {Q : Set q} {R : Q → Set r} →
                          Q → (P → Σ Q R) → ¬ ¬ (Σ[ x ∈ Q ] (P → R x))
independence-of-premise {P = P} q f = ¬¬-map helper excluded-middle
  where
  helper : Dec P → _
  helper (yes p) = Prod.map id const (f p)
  helper (no ¬p) = (q , ⊥-elim ∘′ ¬p)

-- The independence of premise rule for binary sums.

independence-of-premise-⊎ : (P → Q ⊎ R) → ¬ ¬ ((P → Q) ⊎ (P → R))
independence-of-premise-⊎ {P = P} f = ¬¬-map helper excluded-middle
  where
  helper : Dec P → _
  helper (yes p) = Sum.map const const (f p)
  helper (no ¬p) = inj₁ (⊥-elim ∘′ ¬p)

private

  -- Note that independence-of-premise-⊎ is a consequence of
  -- independence-of-premise (for simplicity it is assumed that Q and
  -- R have the same type here):

  corollary : {P : Set p} {Q R : Set q} →
              (P → Q ⊎ R) → ¬ ¬ ((P → Q) ⊎ (P → R))
  corollary {P = P} {Q} {R} f =
    ¬¬-map helper (independence-of-premise
                     true ([ _,_ true , _,_ false ] ∘′ f))
    where
    helper : ∃ (λ b → P → if b then Q else R) → (P → Q) ⊎ (P → R)
    helper (true  , f) = inj₁ f
    helper (false , f) = inj₂ f


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

Excluded-Middle : (ℓ : Level) → Set (suc ℓ)
Excluded-Middle p = {P : Set p} → Dec P
{-# WARNING_ON_USAGE Excluded-Middle
"Warning: Excluded-Middle was deprecated in v1.0.
Please use ExcludedMiddle from `Axiom.ExcludedMiddle` instead."
#-}

Double-Negation-Elimination : (ℓ : Level) → Set (suc ℓ)
Double-Negation-Elimination p = {P : Set p} → Stable P
{-# WARNING_ON_USAGE Double-Negation-Elimination
"Warning: Double-Negation-Elimination was deprecated in v1.0.
Please use DoubleNegationElimination from `Axiom.DoubleNegationElimination` instead."
#-}
