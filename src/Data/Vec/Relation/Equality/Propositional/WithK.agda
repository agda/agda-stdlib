------------------------------------------------------------------------
-- The Agda standard library
--
-- Code related to vector equality over propositional equality that
-- makes use of heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Vec.Relation.Equality.Propositional.WithK
  {a} {A : Set a} where

open import Data.Vec
open import Data.Vec.Relation.Equality.Propositional {A = A}
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

≋⇒≅ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
      xs ≋ ys → xs ≅ ys
≋⇒≅ p with length-equal p
... | refl = H.≡-to-≅ (≋⇒≡ p)
