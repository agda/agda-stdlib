------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Stream type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Codata.Stream.Properties where

open import Size
open import Codata.Thunk using (Thunk; force)
open import Codata.Stream
open import Codata.Stream.Bisimilarity

open import Data.Nat.Base
open import Data.Nat.GeneralisedArithmetic using (fold; fold-pull)

import Data.Vec as Vec
import Data.Product as Prod

open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

------------------------------------------------------------------------
-- repeat

module _ {a} {A : Set a} where

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


------------------------------------------------------------------------
-- Functor laws

module _ {a} {A : Set a} where

 map-identity : ∀ (as : Stream A ∞) {i} → i ⊢ map id as ≈ as
 map-identity (a ∷ as) = Eq.refl ∷ λ where .force → map-identity (as .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 map-map-fusion : ∀ (f : A → B) (g : B → C) as {i} → i ⊢ map g (map f as) ≈ map (g ∘ f) as
 map-map-fusion f g (a ∷ as) = Eq.refl ∷ λ where .force → map-map-fusion f g (as .force)


------------------------------------------------------------------------
-- splitAt

module _ {a b} {A : Set a} {B : Set b} where

  splitAt-map : ∀ n (f : A → B) xs →
    splitAt n (map f xs) ≡ Prod.map (Vec.map f) (map f) (splitAt n xs)
  splitAt-map zero    f xs       = Eq.refl
  splitAt-map (suc n) f (x ∷ xs) =
    Eq.cong (Prod.map₁ (f x Vec.∷_)) (splitAt-map n f (xs .force))

------------------------------------------------------------------------
-- iterate

module _ {a} {A : Set a} where

  lookup-iterate-identity : ∀ n f (a : A) → lookup n (iterate f a) ≡ fold a f n
  lookup-iterate-identity zero     f a = Eq.refl
  lookup-iterate-identity (suc n)  f a = begin
    lookup (suc n) (iterate f a) ≡⟨⟩
    lookup n (iterate f (f a))   ≡⟨ lookup-iterate-identity n f (f a) ⟩
    fold (f a) f n               ≡⟨ fold-pull (const ∘′ f) (f a) Eq.refl (λ _ → Eq.refl) n ⟩
    f (fold a f n)               ≡⟨⟩
    fold a f (suc n)             ∎ where open Eq.≡-Reasoning
