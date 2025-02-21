------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the propositional suffix relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Suffix.Propositional.Properties {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (++-monoid)

open import Data.List.Relation.Binary.Suffix.Heterogeneous
  using (Suffix; here; there; fromView; _++_)
open import Data.List.Relation.Binary.Prefix.Homogeneous.Properties
import Data.List.Relation.Binary.Pointwise as Pointwise

open import Algebra.Properties.Monoid.Divisibility (++-monoid A)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary using (_⇒_)

------------------------------------------------------------------------
-- The inductive definition of the propositional Suffix relation is
-- equivalent to the notion of right divisibility induced by the
-- (List A, _++_, []) monoid

Suffix-as-∣ʳ : Suffix _≡_ ⇒ _∣ʳ_
Suffix-as-∣ʳ (here equal) = ∣ʳ-reflexive (Pointwise.Pointwise-≡⇒≡ equal)
Suffix-as-∣ʳ (there suff) = x∣ʳy⇒x∣ʳzy (_ ∷ []) (Suffix-as-∣ʳ suff)

∣ʳ-as-Suffix : _∣ʳ_ ⇒ Suffix _≡_
∣ʳ-as-Suffix (rest , refl) = fromView (rest ++ Pointwise.refl refl)
