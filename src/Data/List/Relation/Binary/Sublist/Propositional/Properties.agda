------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Properties {a} {A : Set a} where

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (here-injective; there-injective)
open import Data.List.Relation.Binary.Sublist.Propositional {a} {A}

open import Function

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary as U using (Pred)

------------------------------------------------------------------------
-- Re-exporting setoid properties

open import Data.List.Relation.Binary.Sublist.Setoid.Properties (P.setoid A) public

------------------------------------------------------------------------
-- The `loookup` function induced by a proof that `xs ⊆ ys` is injective

module _ {p} {P : Pred A p} where

  lookup-injective : ∀ {xs ys} {p : xs ⊆ ys} {v w : Any P xs} →
                     lookup p v ≡ lookup p w → v ≡ w
  lookup-injective {p = []} {}
  lookup-injective {p = _ ∷ʳ _} {v} {w} = lookup-injective ∘′ there-injective
  lookup-injective {p = x≡y ∷ _} {here pv} {here pw} =
    cong here ∘′ subst-injective x≡y ∘′ here-injective
  lookup-injective {p = _ ∷ _} {there v} {there w} =
    cong there ∘′ lookup-injective ∘′ there-injective
  lookup-injective {p = _ ∷ _} {here _} {there _} = λ ()
  lookup-injective {p = _ ∷ _} {there _} {here _} = λ ()
