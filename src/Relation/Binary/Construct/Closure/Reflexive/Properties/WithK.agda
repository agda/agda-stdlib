------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures which rely on the K rule
------------------------------------------------------------------------

{-# OPTIONS --safe --with-K #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties.WithK where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Product as Prod
open import Data.Sum as Sum
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Reflexive
open import Relation.Binary.Construct.Closure.Reflexive.Properties public
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong)
open import Relation.Nullary.Negation using (contradiction)

module _ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} where

  irrel : Irrelevant _∼_ → Irreflexive _≡_ _∼_ → Irrelevant (Refl _∼_)
  irrel irrel irrefl [ x∼y₁ ] [ x∼y₂ ] = cong [_] (irrel x∼y₁ x∼y₂)
  irrel irrel irrefl [ x∼y ]  refl     = contradiction x∼y (irrefl refl)
  irrel irrel irrefl refl     [ x∼y ]  = contradiction x∼y (irrefl refl)
  irrel irrel irrefl refl     refl     = refl
