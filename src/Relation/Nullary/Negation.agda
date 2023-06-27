------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Negation where

open import Effect.Monad using (RawMonad; mkRawMonad)
open import Data.Bool.Base using (Bool; false; true; if_then_else_; not)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base as Prod using (_,_; Σ; Σ-syntax; ∃; curry; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Base using (flip; _∘_; const; _∘′_)
open import Level using (Level)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; excluded-middle)
open import Relation.Unary using (Universal)

private
  variable
    a p q r w : Level
    A : Set a
    P : Set p
    Q : Set q
    R : Set r
    Whatever : Set w

------------------------------------------------------------------------
-- Re-export public definitions

open import Relation.Nullary.Negation.Core public

------------------------------------------------------------------------
-- Quantifier juggling

module _ {P : A → Set p} where

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
-- Double Negation

-- Double-negation is a monad (if we assume that all elements of ¬ ¬ P
-- are equal).

¬¬-Monad : RawMonad {p} DoubleNegation
¬¬-Monad = mkRawMonad
  DoubleNegation
  contradiction
  (λ x f → negated-stable (¬¬-map f x))

¬¬-push : {Q : P → Set q} →
          DoubleNegation Π[ Q ] → Π[ DoubleNegation ∘ Q ]
¬¬-push ¬¬P⟶Q P ¬Q = ¬¬P⟶Q (λ P⟶Q → ¬Q (P⟶Q P))

-- If Whatever is instantiated with ¬ ¬ something, then this function
-- is call with current continuation in the double-negation monad, or,
-- if you will, a double-negation translation of Peirce's law.
--
-- In order to prove ¬ ¬ P one can assume ¬ P and prove ⊥. However,
-- sometimes it is nice to avoid leaving the double-negation monad; in
-- that case this function can be used (with Whatever instantiated to
-- ⊥).

call/cc : ((P → Whatever) → DoubleNegation P) → DoubleNegation P
call/cc hyp ¬p = hyp (λ p → ⊥-elim (¬p p)) ¬p

-- The "independence of premise" rule, in the double-negation monad.
-- It is assumed that the index set (Q) is inhabited.

independence-of-premise : {R : Q → Set r} →
                          Q → (P → Σ Q R) → DoubleNegation (Σ[ x ∈ Q ] (P → R x))
independence-of-premise {P = P} q f = ¬¬-map helper excluded-middle
  where
  helper : Dec P → _
  helper (yes p) = Prod.map₂ const (f p)
  helper (no ¬p) = (q , ⊥-elim ∘′ ¬p)

-- The independence of premise rule for binary sums.

independence-of-premise-⊎ : (P → Q ⊎ R) → DoubleNegation ((P → Q) ⊎ (P → R))
independence-of-premise-⊎ {P = P} f = ¬¬-map helper excluded-middle
  where
  helper : Dec P → _
  helper (yes p) = Sum.map const const (f p)
  helper (no ¬p) = inj₁ (⊥-elim ∘′ ¬p)

private

  -- Note that independence-of-premise-⊎ is a consequence of
  -- independence-of-premise (for simplicity it is assumed that Q and
  -- R have the same type here):

  corollary : {Q R : Set q} →
              (P → Q ⊎ R) → DoubleNegation ((P → Q) ⊎ (P → R))
  corollary {P = P} {Q} {R} f =
    ¬¬-map helper (independence-of-premise
                     true ([ _,_ true , _,_ false ] ∘′ f))
    where
    helper : ∃ (λ b → P → if b then Q else R) → (P → Q) ⊎ (P → R)
    helper (true  , f) = inj₁ f
    helper (false , f) = inj₂ f
