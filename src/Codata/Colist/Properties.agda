------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Colist type
------------------------------------------------------------------------

module Codata.Colist.Properties where

open import Size
open import Codata.Thunk
open import Codata.Conat
open import Codata.Colist
open import Codata.Colist.Bisimilarity
open import Function
open import Relation.Binary.PropositionalEquality as Eq

-- Functor laws

module _ {a} {A : Set a} where

 map-identity : ∀ (as : Colist A ∞) {i} → i ⊢ map id as ≈ as
 map-identity []       = []
 map-identity (a ∷ as) = Eq.refl ∷ λ where .force → map-identity (as .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 map-map-fusion : ∀ (f : A → B) (g : B → C) as {i} → i ⊢ map g (map f as) ≈ map (g ∘ f) as
 map-map-fusion f g []       = []
 map-map-fusion f g (a ∷ as) = Eq.refl ∷ λ where .force → map-map-fusion f g (as .force)

