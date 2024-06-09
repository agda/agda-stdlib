------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Negation where

open import Data.Bool.Base using (Bool; false; true; if_then_else_)
open import Data.Product.Base as Product using (_,_; Σ; Σ-syntax; ∃; curry; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Effect.Monad using (RawMonad; mkRawMonad)
open import Function.Base using (flip; _∘_; const; _∘′_)
open import Level using (Level)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; ¬¬-excluded-middle)
open import Relation.Unary using (Universal; Pred)

private
  variable
    a b c d p w : Level
    A B C D : Set a
    P : Pred A p
    Whatever : Set w

------------------------------------------------------------------------
-- Re-export public definitions

open import Relation.Nullary.Negation.Core public

------------------------------------------------------------------------
-- Quantifier juggling

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

¬¬-Monad : RawMonad {a} DoubleNegation
¬¬-Monad = mkRawMonad
  DoubleNegation
  contradiction
  (λ x f → negated-stable (¬¬-map f x))

¬¬-push : DoubleNegation Π[ P ] → Π[ DoubleNegation ∘ P ]
¬¬-push ¬¬∀P a ¬Pa = ¬¬∀P (λ ∀P → ¬Pa (∀P a))

-- If Whatever is instantiated with ¬ ¬ something, then this function
-- is call with current continuation in the double-negation monad, or,
-- if you will, a double-negation translation of Peirce's law.
--
-- In order to prove ¬ ¬ P one can assume ¬ P and prove ⊥. However,
-- sometimes it is nice to avoid leaving the double-negation monad; in
-- that case this function can be used (with Whatever instantiated to
-- ⊥).

call/cc : ((A → Whatever) → DoubleNegation A) → DoubleNegation A
call/cc hyp ¬a = hyp (flip contradiction ¬a) ¬a

-- The "independence of premise" rule, in the double-negation monad.
-- It is assumed that the index set (A) is inhabited.

independence-of-premise : A → (B → Σ A P) → DoubleNegation (Σ[ x ∈ A ] (B → P x))
independence-of-premise {A = A} {B = B} {P = P} q f = ¬¬-map helper ¬¬-excluded-middle
  where
  helper : Dec B → Σ[ x ∈ A ] (B → P x)
  helper (yes p) = Product.map₂ const (f p)
  helper (no ¬p) = (q , flip contradiction ¬p)

-- The independence of premise rule for binary sums.

independence-of-premise-⊎ : (A → B ⊎ C) → DoubleNegation ((A → B) ⊎ (A → C))
independence-of-premise-⊎ {A = A} {B = B} {C = C} f = ¬¬-map helper ¬¬-excluded-middle
  where
  helper : Dec A → (A → B) ⊎ (A → C)
  helper (yes p) = Sum.map const const (f p)
  helper (no ¬p) = inj₁ (flip contradiction ¬p)

private

  -- Note that independence-of-premise-⊎ is a consequence of
  -- independence-of-premise (for simplicity it is assumed that Q and
  -- R have the same type here):

  corollary : {B C : Set b} → (A → B ⊎ C) → DoubleNegation ((A → B) ⊎ (A → C))
  corollary {A = A} {B = B} {C = C} f =
    ¬¬-map helper (independence-of-premise true ([ _,_ true , _,_ false ] ∘′ f))
    where
    helper : ∃ (λ b → A → if b then B else C) → (A → B) ⊎ (A → C)
    helper (true  , f) = inj₁ f
    helper (false , f) = inj₂ f
