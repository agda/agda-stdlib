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
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P

private
  variable
    a b : Level
    I : Set a
    A : I → Set a

------------------------------------------------------------------------
-- The propositional equality setoid over sigma types can be
-- decomposed using Pointwise

Pointwise-≡⇒≡ : Pointwise A _≡_ (λ x y → x ≅ y) ⇒ _≡_
Pointwise-≡⇒≡ (P.refl , H.refl) = P.refl

≡⇒Pointwise-≡ : _≡_ ⇒ Pointwise A _≡_ (λ x y → x ≅ y)
≡⇒Pointwise-≡ P.refl = (P.refl , H.refl)

Pointwise-≡↔≡ : Inverse (setoid (P.setoid I) (H.indexedSetoid A)) (P.setoid (Σ I A))
Pointwise-≡↔≡ = record
  { to         = id
  ; to-cong    = Pointwise-≡⇒≡
  ; from       = id
  ; from-cong  = ≡⇒Pointwise-≡
  ; inverse    = (λ {(P.refl , H.refl) → P.refl}) , λ {P.refl → (P.refl , H.refl)}
  }
