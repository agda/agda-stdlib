------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties that are related to pointwise lifting of binary
-- relations to sigma types and make use of heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Relation.Binary.Pointwise.Dependent.WithK where

open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Function
open import Function.Inverse using (Inverse)
open import Relation.Binary using (_⇒_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- The propositional equality setoid over sigma types can be
-- decomposed using Pointwise

module _ {a b} {A : Set a} {B : A → Set b} where

  Pointwise-≡⇒≡ : Pointwise B _≡_ (λ x y → x ≅ y) ⇒ _≡_
  Pointwise-≡⇒≡ (P.refl , H.refl) = P.refl

  ≡⇒Pointwise-≡ : _≡_ ⇒ Pointwise B _≡_ (λ x y → x ≅ y)
  ≡⇒Pointwise-≡ P.refl = (P.refl , H.refl)

  Pointwise-≡↔≡ : Inverse (setoid (P.setoid A) (H.indexedSetoid B))
                  (P.setoid (Σ A B))
  Pointwise-≡↔≡ = record
    { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
    ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
    ; inverse-of = record
      { left-inverse-of  = uncurry (λ _ _ → (P.refl , H.refl))
      ; right-inverse-of = λ _ → P.refl
      }
    }
