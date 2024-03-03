------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties that are related to pointwise lifting of binary
-- relations to sigma types and make use of heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Relation.Binary.Pointwise.Dependent.WithK where

open import Data.Product.Base using (Σ; uncurry; _,_)
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Function.Base
open import Function.Bundles using (Inverse)
open import Level using (Level)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡

private
  variable
    a b : Level
    I : Set a
    A : I → Set a

------------------------------------------------------------------------
-- The propositional equality setoid over sigma types can be
-- decomposed using Pointwise

Pointwise-≡⇒≡ : Pointwise A _≡_ (λ x y → x ≅ y) ⇒ _≡_
Pointwise-≡⇒≡ (≡.refl , ≅.refl) = ≡.refl

≡⇒Pointwise-≡ : _≡_ ⇒ Pointwise A _≡_ (λ x y → x ≅ y)
≡⇒Pointwise-≡ ≡.refl = (≡.refl , ≅.refl)

Pointwise-≡↔≡ : Inverse (setoid (≡.setoid I) (≅.indexedSetoid A)) (≡.setoid (Σ I A))
Pointwise-≡↔≡ = record
  { to         = id
  ; to-cong    = Pointwise-≡⇒≡
  ; from       = id
  ; from-cong  = ≡⇒Pointwise-≡
  ; inverse    = (λ {(≡.refl , ≅.refl) → ≡.refl}) , λ {≡.refl → (≡.refl , ≅.refl)}
  }
