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
open import Data.Bool.Base using (Bool; false; true; not; T; _∧_; _∨_)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_∘_; const; _$_; flip)
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation.Core

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Definition.

-- Decidability proofs have two parts: the `does` term which contains
-- the boolean result and the `proof` term which contains a proof that
-- reflects the boolean result. This definition allows the boolean
-- part of the decision procedure to compute independently from the
-- proof. This leads to better computational behaviour when we only care
-- about the result and not the proof. See README.Decidability for
-- further details.

infix 2 _because_

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does

open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

------------------------------------------------------------------------
-- Recompute

-- Given an irrelevant proof of a decidable type, a proof can
-- be recomputed and subsequently used in relevant contexts.
recompute : ∀ {a} {A : Set a} → Dec A → .A → A
recompute (yes x) _ = x
recompute (no ¬p) x = ⊥-elim (¬p x)

------------------------------------------------------------------------
-- Interaction with negation, sum, product etc.

infixr 1 _⊎-dec_
infixr 2 _×-dec_ _→-dec_

¬? : Dec P → Dec (¬ P)
does  (¬? p?) = not (does p?)
proof (¬? p?) = ¬-reflects (proof p?)

_×-dec_ : Dec P → Dec Q → Dec (P × Q)
does  (p? ×-dec q?) = does p? ∧ does q?
proof (p? ×-dec q?) = proof p? ×-reflects proof q?

_⊎-dec_ : Dec P → Dec Q → Dec (P ⊎ Q)
does  (p? ⊎-dec q?) = does p? ∨ does q?
proof (p? ⊎-dec q?) = proof p? ⊎-reflects proof q?

_→-dec_ : Dec P → Dec Q → Dec (P → Q)
does  (p? →-dec q?) = not (does p?) ∨ does q?
proof (p? →-dec q?) = proof p? →-reflects proof q?

------------------------------------------------------------------------
-- Relationship with booleans

-- `isYes` is a stricter version of `does`. The lack of computation means that
-- we can recover the proposition `P` from `isYes P?` by unification. This is
-- useful when we are using the decision procedure for proof automation.

isYes : Dec P → Bool
isYes (true  because _) = true
isYes (false because _) = false

isNo : Dec P → Bool
isNo = not ∘ isYes

True : Dec P → Set
True Q = T (isYes Q)

False : Dec P → Set
False Q = T (isNo Q)

-- The traditional name for isYes is ⌊_⌋, indicating the stripping of evidence.
⌊_⌋ = isYes

------------------------------------------------------------------------
-- Witnesses

-- Gives a witness to the "truth".
toWitness : {Q : Dec P} → True Q → P
toWitness {Q = true  because [p]} _  = invert [p]
toWitness {Q = false because  _ } ()

-- Establishes a "truth", given a witness.
fromWitness : {Q : Dec P} → P → True Q
fromWitness {Q = true  because   _ } = const _
fromWitness {Q = false because [¬p]} = invert [¬p]

-- Variants for False.
toWitnessFalse : {Q : Dec P} → False Q → ¬ P
toWitnessFalse {Q = true  because   _ } ()
toWitnessFalse {Q = false because [¬p]} _  = invert [¬p]

fromWitnessFalse : {Q : Dec P} → ¬ P → False Q
fromWitnessFalse {Q = true  because [p]} = flip _$_ (invert [p])
fromWitnessFalse {Q = false because  _ } = const _

module _ {p} {P : Set p} where

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.

  From-yes : Dec P → Set p
  From-yes (true  because _) = P
  From-yes (false because _) = Lift p ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (true  because [p]) = invert [p]
  from-yes (false because _ ) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.

  From-no : Dec P → Set p
  From-no (false because _) = ¬ P
  From-no (true  because _) = Lift p ⊤

  from-no : (p : Dec P) → From-no p
  from-no (false because [¬p]) = invert [¬p]
  from-no (true  because   _ ) = _

------------------------------------------------------------------------
-- Maps

map′ : (P → Q) → (Q → P) → Dec P → Dec Q
does  (map′ P→Q Q→P p?)                   = does p?
proof (map′ P→Q Q→P (true  because  [p])) = ofʸ (P→Q (invert [p]))
proof (map′ P→Q Q→P (false because [¬p])) = ofⁿ (invert [¬p] ∘ Q→P)

------------------------------------------------------------------------
-- Relationship with double-negation

-- Decidable predicates are stable.

decidable-stable : Dec P → Stable P
decidable-stable (yes p) ¬¬p = p
decidable-stable (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬-drop-Dec : Dec (¬ ¬ P) → Dec (¬ P)
¬-drop-Dec ¬¬p? = map′ negated-stable contradiction (¬? ¬¬p?)

-- A double-negation-translated variant of excluded middle (or: every
-- nullary relation is decidable in the double-negation monad).

excluded-middle : DoubleNegation (Dec P)
excluded-middle ¬h = ¬h (no (λ p → ¬h (yes p)))
