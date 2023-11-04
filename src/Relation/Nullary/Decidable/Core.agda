------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
--
-- This file contains some core definitions which are re-exported by
-- Relation.Nullary.Decidable
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Decidable.Core where

open import Level using (Level; Lift)
open import Data.Bool.Base using (Bool; T; false; true; not; _∧_; _∨_)
open import Data.Unit.Base using (⊤)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_∘_; const; _$_; flip)
open import Relation.Nullary.Reflects as Reflects
  using (Reflects; ofʸ; ofⁿ; of; invert; Recomputable)
open import Relation.Nullary.Negation.Core
  using (¬_; contradiction; Stable; DoubleNegation; negated-stable)

private
  variable
    a : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition.

-- Decidability proofs have two parts: the `does` term which contains
-- the boolean result and the `proof` term which contains a proof that
-- reflects the boolean result. This definition allows the boolean
-- part of the decision procedure to compute independently from the
-- proof. This leads to better computational behaviour when we only care
-- about the result and not the proof. See README.Design.Decidability
-- for further details.

infix 2 _because_

record Dec (A : Set a) : Set a where
  constructor _because_
  field
    does  : Bool
    proof : Reflects A does

open Dec public

-- lazier versions of `yes` and `no`
pattern yes′ [a] =  true because  [a]
pattern no′ [¬a] = false because [¬a]

-- now these are derived patterns, but could be re-expressed using `of`
pattern yes  a  = yes′ (ofʸ a)
pattern no [¬a] = no′ (ofⁿ [¬a])

------------------------------------------------------------------------
-- Flattening

module _ {A : Set a} where

  From-yes : Dec A → Set a
  From-yes a? = if (does a?) then A else Lift a ⊤

  From-no : Dec A → Set a
  From-no  a? = if (does a?) then Lift a ⊤ else ¬ A

------------------------------------------------------------------------
-- Recompute

-- Given an irrelevant proof of a decidable type, a proof can
-- be recomputed and subsequently used in relevant contexts.
recompute : Dec A → .A → A
recompute = Reflects.recompute ∘ proof

------------------------------------------------------------------------
-- Interaction with negation, sum, product etc.

infixr 1 _⊎-dec_
infixr 2 _×-dec_ _→-dec_

T? : ∀ x → Dec (T x)
T? x = x because T-reflects x

¬? : Dec A → Dec (¬ A)
does  (¬? a?) = not (does a?)
proof (¬? a?) = Reflects.¬-reflects (proof a?)

_×-dec_ : Dec A → Dec B → Dec (A × B)
does  (a? ×-dec b?) = does a? ∧ does b?
proof (a? ×-dec b?) = proof a? Reflects.×-reflects proof b?

_⊎-dec_ : Dec A → Dec B → Dec (A ⊎ B)
does  (a? ⊎-dec b?) = does a? ∨ does b?
proof (a? ⊎-dec b?) = proof a? Reflects.⊎-reflects proof b?

_→-dec_ : Dec A → Dec B → Dec (A → B)
does  (a? →-dec b?) = not (does a?) ∨ does b?
proof (a? →-dec b?) = proof a? Reflects.→-reflects proof b?

------------------------------------------------------------------------
-- Relationship with booleans

-- `isYes` is a stricter version of `does`. The lack of computation
-- means that we can recover the proposition `P` from `isYes a?` by
-- unification. This is useful when we are using the decision procedure
-- for proof automation.

isYes : Dec A → Bool
isYes (yes′ _) = true
isYes (no′  _) = false

isNo : Dec A → Bool
isNo = not ∘ isYes

True : Dec A → Set
True = T ∘ isYes

False : Dec A → Set
False = T ∘ isNo

-- The traditional name for isYes is ⌊_⌋, indicating the stripping of evidence.
⌊_⌋ = isYes

------------------------------------------------------------------------
-- Witnesses

-- Gives a witness to the "truth".
toWitness : {a? : Dec A} → True a? → A
toWitness {a? = yes′ [a]} _ = invert [a]
toWitness {a? = no′  _ } ()

-- Establishes a "truth", given a witness.
fromWitness : {a? : Dec A} → A → True a?
fromWitness {a? = yes′  _ } = const _
fromWitness {a? = no′ [¬a]} = invert [¬a]

-- Variants for False.
toWitnessFalse : {a? : Dec A} → False a? → ¬ A
toWitnessFalse {a? = yes′  _ } ()
toWitnessFalse {a? = no′ [¬a]} _  = invert [¬a]

fromWitnessFalse : {a? : Dec A} → ¬ A → False a?
fromWitnessFalse {a? = yes′ [a]} = flip _$_ (invert [a])
fromWitnessFalse {a? = no′   _ } = const _

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.
from-yes : (a? : Dec A) → From-yes a?
from-yes (yes′ [a]) = invert [a]
from-yes (no′   _ ) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.
from-no : (a? : Dec A) → From-no a?
from-no (no′ [¬a]) = invert [¬a]
from-no (yes′  _ ) = _

------------------------------------------------------------------------
-- Maps

map′ : (A → B) → (B → A) → Dec A → Dec B
does  (map′ A→B B→A a?)        = does a?
proof (map′ A→B B→A (yes′ [a])) = of (A→B (invert [a]))
proof (map′ A→B B→A (no′ [¬a])) = of (invert [¬a] ∘ B→A)

------------------------------------------------------------------------
-- Relationship with double-negation

-- Decidable predicates are stable.

decidable-stable : Dec A → Stable A
decidable-stable (yes′ [a]) ¬¬a = invert [a]
decidable-stable (no′ [¬a]) ¬¬a = contradiction (invert [¬a]) ¬¬a

¬-drop-Dec : Dec (¬ ¬ A) → Dec (¬ A)
¬-drop-Dec ¬¬a? = map′ negated-stable contradiction (¬? ¬¬a?)

-- A double-negation-translated variant of excluded middle (or: every
-- nullary relation is decidable in the double-negation monad).

¬¬-excluded-middle : DoubleNegation (Dec A)
¬¬-excluded-middle ¬?a = ¬?a (no (λ a → ¬?a (yes a)))


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

excluded-middle = ¬¬-excluded-middle
{-# WARNING_ON_USAGE excluded-middle
"Warning: excluded-middle was deprecated in v2.0.
Please use ¬¬-excluded-middle instead."
#-}
