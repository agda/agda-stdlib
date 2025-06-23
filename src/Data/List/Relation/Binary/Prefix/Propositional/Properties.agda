------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the propositional prefix relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Prefix.Propositional.Properties {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (++-monoid)

open import Data.List.Relation.Binary.Prefix.Heterogeneous
  using (Prefix; []; _∷_; fromView; _++_)
open import Data.List.Relation.Binary.Prefix.Homogeneous.Properties
import Data.List.Relation.Binary.Pointwise as Pointwise

open import Algebra.Properties.Monoid.Divisibility (++-monoid A)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary using (_⇒_)

------------------------------------------------------------------------
-- The inductive definition of the propositional Prefix relation is
-- equivalent to the notion of left divisibility induced by the
-- (List A, _++_, []) monoid

Prefix-as-∣ˡ : Prefix _≡_ ⇒ _∣ˡ_
Prefix-as-∣ˡ []          = ε∣ˡ _
Prefix-as-∣ˡ (refl ∷ tl) = x∣ˡy⇒zx∣ˡzy (_ ∷ []) (Prefix-as-∣ˡ tl)

∣ˡ-as-Prefix : _∣ˡ_ ⇒ Prefix _≡_
∣ˡ-as-Prefix (rest , refl) = fromView (Pointwise.refl refl ++ rest)
