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

-- decToMaybe was deprecated in v2.1 #2330/#2336
-- this can go through `Data.Maybe.Base` once that deprecation is fully done.
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

open import Agda.Builtin.Equality using (_≡_)
open import Level using (Level)
open import Data.Bool.Base using (Bool; T; false; true; not; _∧_; _∨_)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; const; _$_; flip)
open import Relation.Nullary.Recomputable as Recomputable hiding (recompute-constant)
open import Relation.Nullary.Reflects as Reflects hiding (recompute; recompute-constant)
open import Relation.Nullary.Negation.Core
  using (¬_; Stable; negated-stable; contradiction; DoubleNegation)


private
  variable
    a b : Level
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

pattern yes a =  true because ofʸ  a
pattern no ¬a = false because ofⁿ ¬a

------------------------------------------------------------------------
-- Flattening

module _ {A : Set a} where

  From-yes : Dec A → Set a
  From-yes (true  because _) = A
  From-yes (false because _) = ⊤

  From-no : Dec A → Set a
  From-no (false because _) = ¬ A
  From-no (true  because _) = ⊤

------------------------------------------------------------------------
-- Recompute

-- Given an irrelevant proof of a decidable type, a proof can
-- be recomputed and subsequently used in relevant contexts.

recompute : Dec A → Recomputable A
recompute = Reflects.recompute ∘ proof

recompute-constant : (a? : Dec A) (p q : A) → recompute a? p ≡ recompute a? q
recompute-constant = Recomputable.recompute-constant ∘ recompute

------------------------------------------------------------------------
-- Interaction with negation, sum, product etc.

infixr 1 _⊎-dec_
infixr 2 _×-dec_ _→-dec_

T? : ∀ x → Dec (T x)
T? x = x because T-reflects x

¬? : Dec A → Dec (¬ A)
does  (¬? a?) = not (does a?)
proof (¬? a?) = ¬-reflects (proof a?)

_×-dec_ : Dec A → Dec B → Dec (A × B)
does  (a? ×-dec b?) = does a? ∧ does b?
proof (a? ×-dec b?) = proof a? ×-reflects proof b?

_⊎-dec_ : Dec A → Dec B → Dec (A ⊎ B)
does  (a? ⊎-dec b?) = does a? ∨ does b?
proof (a? ⊎-dec b?) = proof a? ⊎-reflects proof b?

_→-dec_ : Dec A → Dec B → Dec (A → B)
does  (a? →-dec b?) = not (does a?) ∨ does b?
proof (a? →-dec b?) = proof a? →-reflects proof b?

------------------------------------------------------------------------
-- Relationship with Maybe

dec⇒maybe : Dec A → Maybe A
dec⇒maybe ( true because [a]) = just (invert [a])
dec⇒maybe (false because  _ ) = nothing

------------------------------------------------------------------------
-- Relationship with Sum

toSum : Dec A → A ⊎ ¬ A
toSum ( true because  [p]) = inj₁ (invert  [p])
toSum (false because [¬p]) = inj₂ (invert [¬p])

fromSum : A ⊎ ¬ A → Dec A
fromSum (inj₁ p)  = yes p
fromSum (inj₂ ¬p) = no ¬p

------------------------------------------------------------------------
-- Relationship with booleans

-- `isYes` is a stricter version of `does`. The lack of computation
-- means that we can recover the proposition `P` from `isYes a?` by
-- unification. This is useful when we are using the decision procedure
-- for proof automation.

isYes : Dec A → Bool
isYes (true  because _) = true
isYes (false because _) = false

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
toWitness {a? = true  because [a]} _  = invert [a]
toWitness {a? = false because  _ } ()

-- Establishes a "truth", given a witness.
fromWitness : {a? : Dec A} → A → True a?
fromWitness {a? = true  because   _ } = const _
fromWitness {a? = false because [¬a]} = invert [¬a]

-- Variants for False.
toWitnessFalse : {a? : Dec A} → False a? → ¬ A
toWitnessFalse {a? = true  because   _ } ()
toWitnessFalse {a? = false because [¬a]} _  = invert [¬a]

fromWitnessFalse : {a? : Dec A} → ¬ A → False a?
fromWitnessFalse {a? = true  because [a]} = flip _$_ (invert [a])
fromWitnessFalse {a? = false because  _ } = const _

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.
from-yes : (a? : Dec A) → From-yes a?
from-yes (true  because [a]) = invert [a]
from-yes (false because _ ) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.
from-no : (a? : Dec A) → From-no a?
from-no (false because [¬a]) = invert [¬a]
from-no (true  because   _ ) = _

------------------------------------------------------------------------
-- Maps

map′ : (A → B) → (B → A) → Dec A → Dec B
does  (map′ A→B B→A a?)                   = does a?
proof (map′ A→B B→A (true  because  [a])) = of (A→B (invert [a]))
proof (map′ A→B B→A (false because [¬a])) = of (invert [¬a] ∘ B→A)

------------------------------------------------------------------------
-- Relationship with double-negation

-- Decidable predicates are stable.

decidable-stable : Dec A → Stable A
decidable-stable (true  because  [a]) ¬¬a = invert [a]
decidable-stable (false because [¬a]) ¬¬a = contradiction (invert [¬a]) ¬¬a

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

-- Version 2.1

decToMaybe = dec⇒maybe
{-# WARNING_ON_USAGE decToMaybe
"Warning: decToMaybe was deprecated in v2.1.
Please use Relation.Nullary.Decidable.Core.dec⇒maybe instead."
#-}

fromDec = toSum
{-# WARNING_ON_USAGE fromDec
"Warning: fromDec was deprecated in v2.1.
Please use Relation.Nullary.Decidable.Core.toSum instead."
#-}

toDec = fromSum
{-# WARNING_ON_USAGE toDec
"Warning: toDec was deprecated in v2.1.
Please use Relation.Nullary.Decidable.Core.fromSum instead."
#-}
