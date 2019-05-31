------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about the `Axiom` modules.
------------------------------------------------------------------------

module README.Axiom where

open import Level using (0ℓ)

------------------------------------------------------------------------
-- Introduction

-- Several rules that are used without thought in written mathematics
-- cannot be proved in Agda. The modules in the `Axiom` folder
-- provide types expressing some of these rules that users may want to
-- use even when they're not provable in Agda.

------------------------------------------------------------------------
-- Example: law of excluded middle

-- In classical logic the law of excluded middle states that for any
-- proposition `P` either `P` or `¬P` must hold. This is impossible
-- to prove in Agda because Agda is a constructive system and so any
-- proof of the excluded middle would have to build a term of either
-- type `P` or `¬P`. This is clearly impossible without any knowledge
-- of what proposition `P` is.

-- The types for which `P` or `¬P` holds is called `Dec P` in the
-- standard library (short for `Decidable`).

open import Relation.Nullary using (Dec)

-- The type of the proof of saying that excluded middle holds for
-- all types at universe level 0ℓ is therefore:
--
--   ExcludedMiddle ℓ = ∀ {P : Set ℓ} → Dec P
--
-- and this type is exactly the one found in `Axiom.ExcludedMiddle`:

open import Axiom.ExcludedMiddle

-- There are two different ways that the axiom can be introduced into
-- your Agda development. The first option is to postulate it:

postulate excludedMiddle : ExcludedMiddle 0ℓ

-- This has the advantage that it only neesd to be postulated once
-- and it can then be imported into many different modules as with any
-- other proof. The downside is that the resulting Agda code will no
-- longer type check under the --safe flag.

-- The second approach is to pass it as a module parameter:

module Proof (excludedMiddle : ExcludedMiddle 0ℓ) where

-- The advantage of this approach is that the resulting Agda
-- development can still be type checked under the --safe flag.
-- Intuitively the reason for this is that when postulating it
-- you are telling Agda that excluded middle does hold (which is clearly
-- untrue as discussed above). In contrast when passing it as a module
-- parameter you are telling Agda that **if** excluded middle was true
-- then the following proofs would hold, which is logically valid.

-- The disadvantage of this approach is that it is now necessary to
-- include the excluded middle assumption as a parameter in every module
-- that you want to use it in. Additionally the modules can never
-- be fully instantiated (without postulating excluded middle).

------------------------------------------------------------------------
-- Other axioms

-- Double negation elimination
--   (∀ P → ¬ ¬ P → P)

import Axiom.DoubleNegationElimination

-- Function extensionality
--   (∀ f g → (∀ x → f x ≡ g x) → f ≡ g)

import Axiom.Extensionality.Propositional
import Axiom.Extensionality.Heterogeneous

-- Uniqueness of identity proofs (UIP)
--  (∀ x y (p q : x ≡ y) → p ≡ q)

import Axiom.UniquenessOfIdentityProofs
