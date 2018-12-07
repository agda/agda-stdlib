------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties, related to reflexive transitive closures, that rely on
-- the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module
  Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.WithK
  where

open import Function
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Equality

module _ {i t} {I : Set i} {T : Rel I t} {i j k} {x y : T i j} {xs ys}
  where

  ◅-injectiveˡ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → x ≡ y
  ◅-injectiveˡ refl = refl

  ◅-injectiveʳ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → xs ≡ ys
  ◅-injectiveʳ refl = refl
