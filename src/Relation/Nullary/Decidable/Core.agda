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
open import Data.Bool.Base
open import Data.Unit.Base using (⊤)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (id; _∘_; const; _$_; flip)
open import Relation.Nullary.Reflects as Reflects
  using (Reflects; of; invert; Recomputable)
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

-- lazier 'pattern' _ᵖ versions of `yes` and `no`
pattern yesᵖ [a] =  true because  [a]
pattern noᵖ [¬a] = false because [¬a]

-- now these original forms are derived patterns
pattern yes a = yesᵖ (Reflects.ofʸ a)
pattern no ¬a = noᵖ (Reflects.ofⁿ ¬a)

-- but can be re-expressed as term constructions _ᵗ using `of`
yesᵗ : A → Dec A
yesᵗ a = yesᵖ (of a)

noᵗ : ¬ A → Dec A
noᵗ ¬a = noᵖ (of ¬a)

------------------------------------------------------------------------
-- Characterisation : Dec A iff there is a Bool b reflecting it via T

-- forwards direction: use `does`

does-complete : ∀ (A? : Dec A) → A → T (does A?)
does-complete (yesᵖ  _ ) _ = _
does-complete (noᵖ [¬a]) a = contradiction a (invert [¬a])

does-sound : ∀ (A? : Dec A) → T (does A?) → A
does-sound (yesᵖ [a]) _ = invert [a]
does-sound (noᵖ   _ ) ()

-- backwards direction: inherit from `Reflects`

fromEquivalence : ∀ {b} → (T b → A) → (A → T b) → Dec A
fromEquivalence {b = b} sound complete
  = b because (Reflects.fromEquivalence sound complete)

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
recompute : Dec A → Recomputable A
recompute = Reflects.recompute ∘ proof

------------------------------------------------------------------------
-- Interaction with negation, sum, product etc.

infixr 1 _⊎-dec_
infixr 2 _×-dec_ _→-dec_

T? : ∀ b → Dec (T b)
T? b = b because Reflects.T-reflects b -- ≗ fromEquivalence id id

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
isYes (yesᵖ _) = true
isYes (noᵖ  _) = false

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
toWitness {a? = yesᵖ [a]} _ = invert [a]
toWitness {a? = noᵖ  _ } ()

-- Establishes a "truth", given a witness.
fromWitness : {a? : Dec A} → A → True a?
fromWitness {a? = yesᵖ  _ } = const _
fromWitness {a? = noᵖ [¬a]} = invert [¬a]

-- Variants for False.
toWitnessFalse : {a? : Dec A} → False a? → ¬ A
toWitnessFalse {a? = yesᵖ  _ } ()
toWitnessFalse {a? = noᵖ [¬a]} _  = invert [¬a]

fromWitnessFalse : {a? : Dec A} → ¬ A → False a?
fromWitnessFalse {a? = yesᵖ [a]} = flip _$_ (invert [a])
fromWitnessFalse {a? = noᵖ   _ } = const _

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.
from-yes : (a? : Dec A) → From-yes a?
from-yes (yesᵖ [a]) = invert [a]
from-yes (noᵖ   _ ) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.
from-no : (a? : Dec A) → From-no a?
from-no (noᵖ [¬a]) = invert [¬a]
from-no (yesᵖ  _ ) = _

------------------------------------------------------------------------
-- Maps

map′ : (A → B) → (B → A) → Dec A → Dec B
does  (map′ A→B B→A a?)         = does a?
proof (map′ A→B B→A (yesᵖ [a])) = of (A→B (invert [a]))
proof (map′ A→B B→A (noᵖ [¬a])) = of (invert [¬a] ∘ B→A)

------------------------------------------------------------------------
-- Relationship with double-negation

-- Decidable predicates are stable.

decidable-stable : Dec A → Stable A
decidable-stable (yesᵖ [a]) ¬¬a = invert [a]
decidable-stable (noᵖ [¬a]) ¬¬a = contradiction (invert [¬a]) ¬¬a

¬-drop-Dec : Dec (¬ ¬ A) → Dec (¬ A)
¬-drop-Dec ¬¬a? = map′ negated-stable contradiction (¬? ¬¬a?)

-- A double-negation-translated variant of excluded middle (or: every
-- nullary relation is decidable in the double-negation monad).

¬¬-excluded-middle : DoubleNegation (Dec A)
¬¬-excluded-middle ¬?a = ¬?a (noᵗ (λ a → ¬?a (yesᵗ a)))


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
