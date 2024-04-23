------------------------------------------------------------------------
-- The Agda standard library
--
-- Code related to vector equality over propositional equality that
-- makes use of heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Vec.Relation.Binary.Equality.Propositional.WithK
  {a} {A : Set a} where

open import Data.Vec.Base using (Vec)
open import Data.Vec.Relation.Binary.Equality.Propositional {A = A}
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅)

≋⇒≅ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
      xs ≋ ys → xs ≅ ys
≋⇒≅ p with refl <- length-equal p = ≡-to-≅ (≋⇒≡ p)
