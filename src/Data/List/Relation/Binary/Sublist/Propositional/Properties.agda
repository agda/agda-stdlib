------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Properties {a} {A : Set a} where

open import Data.List using (map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (here-injective; there-injective)
open import Data.List.Relation.Binary.Sublist.Propositional
  hiding (map)
import Data.List.Relation.Binary.Sublist.Setoid.Properties
  as SetoidProperties
open import Function
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary as U using (Pred)

------------------------------------------------------------------------
-- Re-exporting setoid properties

open SetoidProperties (P.setoid A) public
  hiding (map⁺)

------------------------------------------------------------------------
-- map

module _ {b} {B : Set b} where

  map⁺ : ∀ {as bs} (f : A → B) → as ⊆ bs → map f as ⊆ map f bs
  map⁺ f = SetoidProperties.map⁺ (setoid A) (setoid B) (cong f)

------------------------------------------------------------------------
-- The `lookup` function induced by a proof that `xs ⊆ ys` is injective

module _ {p} {P : Pred A p} where

  lookup-injective : ∀ {xs ys} {p : xs ⊆ ys} {v w : Any P xs} →
                     lookup p v ≡ lookup p w → v ≡ w
  lookup-injective {p = []}       {}
  lookup-injective {p = _   ∷ʳ _} {v}       {w}       =
    lookup-injective ∘′ there-injective
  lookup-injective {p = x≡y ∷ _}  {here pv} {here pw} =
    cong here ∘′ subst-injective x≡y ∘′ here-injective
  lookup-injective {p = _ ∷ _}    {there v} {there w} =
    cong there ∘′ lookup-injective ∘′ there-injective
