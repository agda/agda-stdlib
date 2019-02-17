------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Properties {a} {A : Set a} where

open import Data.Empty
open import Data.List.Base hiding (lookup; _∷ʳ_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (here-injective; there-injective)
open import Data.Maybe as Maybe using (nothing; just)
open import Data.Maybe.Relation.Unary.All as MAll using (nothing; just)
open import Data.Nat.Base
open import Data.Nat.Properties

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary
import Relation.Nullary.Decidable as D
open import Relation.Unary as U using (Pred)

open import Data.List.Relation.Binary.Sublist.Propositional {a} {A}
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
