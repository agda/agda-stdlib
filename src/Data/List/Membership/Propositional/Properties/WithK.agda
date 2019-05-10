------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership, that rely on
-- the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.List.Membership.Propositional.Properties.WithK where

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
import Data.List.Membership.Setoid.Properties as Membershipₛ
open import Relation.Unary using (Irrelevant)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary.PropositionalEquality.WithK

------------------------------------------------------------------------
-- Irrelevance

irrelevant : ∀ {a} {A : Set a} {xs : List A} →
             Unique xs → Irrelevant (_∈ xs)
irrelevant = Membershipₛ.irrelevant (P.setoid _) ≡-irrelevant
