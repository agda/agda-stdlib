------------------------------------------------------------------------
-- The Agda standard library
--
-- Patterns used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Pattern where

open import Data.Product
import Data.String as String
import Reflection.Literal as Literal
import Reflection.Name as Name
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Reflection.Argument

------------------------------------------------------------------------
-- Re-exporting the builtin type and constructors

open import Agda.Builtin.Reflection public using (Pattern)
open Pattern public

con-injective₁ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → c ≡ c′
con-injective₁ refl = refl

con-injective₂ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → args ≡ args′
con-injective₂ refl = refl

con-injective : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → c ≡ c′ × args ≡ args′
con-injective = < con-injective₁ , con-injective₂ >

var-injective : ∀ {x y} → var x ≡ var y → x ≡ y
var-injective refl = refl

lit-injective : ∀ {x y} → Pattern.lit x ≡ lit y → x ≡ y
lit-injective refl = refl

proj-injective : ∀ {x y} → proj x ≡ proj y → x ≡ y
proj-injective refl = refl

open import Data.List.Base
open import Data.List.Properties

_≟s_ : Decidable (_≡_ {A = Args Pattern})
_≟_  : Decidable (_≡_ {A = Pattern})

con c ps ≟ con c′ ps′ = Dec.map′ (uncurry (cong₂ con)) con-injective (c Name.≟ c′ ×-dec ps ≟s ps′)
var s    ≟ var s′     = Dec.map′ (cong var) var-injective (s String.≟ s′)
lit l    ≟ lit l′     = Dec.map′ (cong lit) lit-injective (l Literal.≟ l′)
proj a   ≟ proj a′    = Dec.map′ (cong proj) proj-injective (a Name.≟ a′)

con x x₁ ≟ dot = no (λ ())
con x x₁ ≟ var x₂ = no (λ ())
con x x₁ ≟ lit x₂ = no (λ ())
con x x₁ ≟ proj x₂ = no (λ ())
con x x₁ ≟ absurd = no (λ ())
dot ≟ con x x₁ = no (λ ())
dot ≟ dot = yes refl
dot ≟ var x = no (λ ())
dot ≟ lit x = no (λ ())
dot ≟ proj x = no (λ ())
dot ≟ absurd = no (λ ())
var s ≟ con x x₁ = no (λ ())
var s ≟ dot = no (λ ())
var s ≟ lit x = no (λ ())
var s ≟ proj x = no (λ ())
var s ≟ absurd = no (λ ())
lit x ≟ con x₁ x₂ = no (λ ())
lit x ≟ dot = no (λ ())
lit x ≟ var _ = no (λ ())
lit x ≟ proj x₁ = no (λ ())
lit x ≟ absurd = no (λ ())
proj x ≟ con x₁ x₂ = no (λ ())
proj x ≟ dot = no (λ ())
proj x ≟ var _ = no (λ ())
proj x ≟ lit x₁ = no (λ ())
proj x ≟ absurd = no (λ ())
absurd ≟ con x x₁ = no (λ ())
absurd ≟ dot = no (λ ())
absurd ≟ var _ = no (λ ())
absurd ≟ lit x = no (λ ())
absurd ≟ proj x = no (λ ())
absurd ≟ absurd = yes refl

[]             ≟s []       = yes refl
(arg i p ∷ xs) ≟s (arg j q ∷ ys) =
  Dec.map′ (uncurry (cong₂ _∷_)) ∷-injective
  (unArg-dec (p ≟ q) ×-dec xs ≟s ys)

[]      ≟s (_ ∷ _) = no λ()
(_ ∷ _) ≟s []      = no λ()
