------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Stream type
------------------------------------------------------------------------

module Codata.Stream.Properties where

open import Size
open import Data.Nat.Base
import Data.Vec as Vec
open import Codata.Thunk
open import Codata.Stream
open import Codata.Stream.Bisimilarity
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module _ {a b} {A : Set a} {B : Set b} where

 lookup-repeat-identity : (n : ℕ) (a : A) → lookup n (repeat a) ≡ a
 lookup-repeat-identity zero    a = Eq.refl
 lookup-repeat-identity (suc n) a = lookup-repeat-identity n a

 take-repeat-identity : (n : ℕ) (a : A) → take n (repeat a) ≡ Vec.replicate a
 take-repeat-identity zero    a = Eq.refl
 take-repeat-identity (suc n) a = Eq.cong (a Vec.∷_) (take-repeat-identity n a)

module _ {a b} {A : Set a} {B : Set b} where

 map-repeat-commute : ∀ (f : A → B) a {i} → i ⊢ map f (repeat a) ≈ repeat (f a)
 map-repeat-commute f a = Eq.refl ∷ λ where .force → map-repeat-commute f a

 repeat-ap-identity : ∀ (f : A → B) as {i} → i ⊢ ap (repeat f) as ≈ map f as
 repeat-ap-identity f (a ∷ as) = Eq.refl ∷ λ where .force → repeat-ap-identity f (as .force)

 ap-repeat-identity : ∀ (fs : Stream (A → B) ∞) (a : A) {i} → i ⊢ ap fs (repeat a) ≈ map (_$ a) fs
 ap-repeat-identity (f ∷ fs) a = Eq.refl ∷ λ where .force → ap-repeat-identity (fs .force) a

 ap-repeat-commute : ∀ (f : A → B) a {i} → i ⊢ ap (repeat f) (repeat a) ≈ repeat (f a)
 ap-repeat-commute f a = Eq.refl ∷ λ where .force → ap-repeat-commute f a

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 map-map-fusion : ∀ (f : A → B) (g : B → C) as {i} → i ⊢ map g (map f as) ≈ map (g ∘ f) as
 map-map-fusion f g (a ∷ as) = Eq.refl ∷ λ where .force → map-map-fusion f g (as .force)

