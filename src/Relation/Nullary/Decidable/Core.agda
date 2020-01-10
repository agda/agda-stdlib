------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
--
-- This file contains some core definitions which are re-exported by
-- Relation.Nullary.Decidable
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Decidable.Core where

open import Level using (Level; Lift)
open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Unit.Base using (⊤)
open import Data.Empty
open import Data.Product
open import Function.Base

open import Agda.Builtin.Equality
open import Relation.Nullary.Reflects
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

-- `isYes` is a stricter version of `does`. The lack of computation means that
-- we can recover the proposition `P` from `isYes P?` by unification. This is
-- useful when we are using the decision procedure for proof automation.

isYes : Dec P → Bool
isYes ( true because _) = true
isYes (false because _) = false

isYes≗does : (P? : Dec P) → isYes P? ≡ does P?
isYes≗does ( true because _) = refl
isYes≗does (false because _) = refl

-- The traditional name for isYes is ⌊_⌋, indicating the stripping of evidence.
⌊_⌋ = isYes

isNo : Dec P → Bool
isNo = not ∘ isYes

True : Dec P → Set
True Q = T (isYes Q)

False : Dec P → Set
False Q = T (isNo Q)

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

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.

module _ {p} {P : Set p} where

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
-- Result of decidability

dec-true : (p? : Dec P) → P → does p? ≡ true
dec-true (true  because   _ ) p = refl
dec-true (false because [¬p]) p = ⊥-elim (invert [¬p] p)

dec-false : (p? : Dec P) → ¬ P → does p? ≡ false
dec-false (false because  _ ) ¬p = refl
dec-false (true  because [p]) ¬p = ⊥-elim (¬p (invert [p]))

dec-yes : (p? : Dec P) → P → ∃ λ p′ → p? ≡ yes p′
dec-yes p? p with dec-true p? p
dec-yes (yes p′) p | refl = p′ , refl

dec-no : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
dec-no p? ¬p with dec-false p? ¬p
dec-no (no ¬p′) ¬p | refl = ¬p′ , refl

dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
dec-yes-irr p? irr p with dec-yes p? p
... | p′ , eq rewrite irr p p′ = eq

------------------------------------------------------------------------
-- Maps

map′ : (P → Q) → (Q → P) → Dec P → Dec Q
does  (map′ P→Q Q→P p?)                   = does p?
proof (map′ P→Q Q→P (true  because  [p])) = ofʸ (P→Q (invert [p]))
proof (map′ P→Q Q→P (false because [¬p])) = ofⁿ (invert [¬p] ∘ Q→P)
