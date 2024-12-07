------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership, that rely on
-- the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.List.Membership.Propositional.Properties.WithK where

open import Level using (Level)
open import Function.Bundles using (Equivalence)
open import Data.List.Base
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
import Data.List.Membership.Setoid.Properties as Membership
open import Data.List.Relation.Binary.BagAndSetEquality using (_∼[_]_; set; bag)
open import Data.Product using (_,_)
open import Relation.Unary using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)

private
  variable
    a : Level
    A : Set a
    xs ys : List A

------------------------------------------------------------------------
-- Irrelevance

unique⇒irrelevant : Unique xs → Irrelevant (_∈ xs)
unique⇒irrelevant = Membership.unique⇒irrelevant (≡.setoid _) ≡-irrelevant

unique∧set⇒bag : Unique xs → Unique ys → xs ∼[ set ] ys → xs ∼[ bag ] ys
unique∧set⇒bag p p′ eq = record
  { Equivalence eq
  ; inverse = (λ _ → unique⇒irrelevant p′ _ _) , (λ _ → unique⇒irrelevant p _ _) }
