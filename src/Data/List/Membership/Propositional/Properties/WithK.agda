------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership, that rely on
-- the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.List.Membership.Propositional.Properties.WithK where

open import Data.List.Base
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
import Data.List.Membership.Setoid.Properties as Membership
open import Relation.Unary using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.PropositionalEquality.WithK

------------------------------------------------------------------------
-- Irrelevance

unique⇒irrelevant : ∀ {a} {A : Set a} {xs : List A} →
                    Unique xs → Irrelevant (_∈ xs)
unique⇒irrelevant = Membership.unique⇒irrelevant (≡.setoid _) ≡-irrelevant
