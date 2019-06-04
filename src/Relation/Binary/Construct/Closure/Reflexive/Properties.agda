------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties where

open import Data.Product as Prod
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Reflexive
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import Relation.Nullary
open import Relation.Unary using (Pred)

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Properties

module _ {P : Rel A ℓ₁} {Q : Rel B ℓ₂} where

  =[]⇒ : ∀ {f : A → B} → P =[ f ]⇒ Q → Refl P =[ f ]⇒ Refl Q
  =[]⇒ x [ x∼y ] = [ x x∼y ]
  =[]⇒ x refl    = refl

module _ {_~_ : Rel A ℓ} where

  respˡ : ∀ {P : REL A B p} → P Respectsˡ _~_ → P Respectsˡ (Refl _~_)
  respˡ p-respˡ-~ [ x∼y ] = p-respˡ-~ x∼y
  respˡ _         refl    = id

  respʳ : ∀ {P : REL B A p} → P Respectsʳ _~_ → P Respectsʳ (Refl _~_)
  respʳ = respˡ

module _ {_~_ : Rel A ℓ} where

  sym : Symmetric _~_ → Symmetric (Refl _~_)
  sym ~-sym [ x∼y ] = [ ~-sym x∼y ]
  sym ~-sym refl    = refl

  trans : Transitive _~_ → Transitive (Refl _~_)
  trans ~-trans [ x∼y ] [ x∼y₁ ] = [ ~-trans x∼y x∼y₁ ]
  trans ~-trans [ x∼y ] refl     = [ x∼y ]
  trans ~-trans refl    [ x∼y ]  = [ x∼y ]
  trans ~-trans refl    refl     = refl

  dec : Decidable {A = A} _≡_ → Decidable _~_ → Decidable (Refl _~_)
  dec ≡-dec ~-dec a b with ≡-dec a b | ~-dec a b
  ... | _        | yes q = yes [ q ]
  ... | yes refl | _     = yes refl
  ... | no ¬p    | no ¬q = no λ { refl → ¬p refl; [ p ] → ¬q p }

  decidable : Trichotomous _≡_ _~_ → Decidable (Refl _~_)
  decidable ~-tri a b with ~-tri a b
  ... | tri< a~b  _  _ = yes [ a~b ]
  ... | tri≈ _  refl _ = yes refl
  ... | tri> ¬a ¬b   _ = no λ { refl → ¬b refl ; [ p ] → ¬a p }

module _ {_~_ : Rel A ℓ} {P : Pred A p} where

  resp : P Respects _~_ → P Respects (Refl _~_)
  resp p-resp-~ [ x∼y ] = p-resp-~ x∼y
  resp _        refl    = id

module _ {_~_ : Rel A ℓ} {P : Rel A p} where

  resp₂ : P Respects₂ _~_ → P Respects₂ (Refl _~_)
  resp₂ = Prod.map respˡ respʳ
