------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties, related to reflexive transitive closures, that rely on
-- the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module
  Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.WithK
  where

open import Function.Base using (_∋_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- Equality

module _ {i t} {I : Set i} {T : Rel I t} {i j k} {x y : T i j} {xs ys}
  where

  ◅-injectiveˡ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → x ≡ y
  ◅-injectiveˡ refl = refl

  ◅-injectiveʳ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → xs ≡ ys
  ◅-injectiveʳ refl = refl
