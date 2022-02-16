------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of infinite streams defined as coinductive records
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream.Properties where

open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Relation.Binary.Pointwise
  as B using (_≈_; head; tail)

open import Data.Nat.Base using (zero; suc)
open import Data.Product as Prod using (_,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec; _∷_)
open import Function.Base using (const; flip; id; _∘′_; _$′_; _⟨_⟩_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Properties of repeat

lookup-repeat : ∀ n (a : A) → lookup n (repeat a) ≡ a
lookup-repeat zero    a = P.refl
lookup-repeat (suc n) a = lookup-repeat n a

splitAt-repeat : ∀ n (a : A) → splitAt n (repeat a) ≡ (Vec.replicate a , repeat a)
splitAt-repeat zero    a = P.refl
splitAt-repeat (suc n) a = cong (Prod.map₁ (a ∷_)) (splitAt-repeat n a)

take-repeat : ∀ n (a : A) → take n (repeat a) ≡ Vec.replicate a
take-repeat n a = cong proj₁ (splitAt-repeat n a)

drop-repeat : ∀ n (a : A) → drop n (repeat a) ≡ repeat a
drop-repeat n a = cong proj₂ (splitAt-repeat n a)

map-repeat : ∀ (f : A → B) a → map f (repeat a) ≈ repeat (f a)
map-repeat f a .head = P.refl
map-repeat f a .tail = map-repeat f a

ap-repeat : ∀ (f : A → B) a → ap (repeat f) (repeat a) ≈ repeat (f a)
ap-repeat f a .head = P.refl
ap-repeat f a .tail = ap-repeat f a

ap-repeatˡ : ∀ (f : A → B) as → ap (repeat f) as ≈ map f as
ap-repeatˡ f as .head = P.refl
ap-repeatˡ f as .tail = ap-repeatˡ f (as .tail)

ap-repeatʳ : ∀ (fs : Stream (A → B)) a → ap fs (repeat a) ≈ map (_$′ a) fs
ap-repeatʳ fs a .head = P.refl
ap-repeatʳ fs a .tail = ap-repeatʳ (fs .tail) a

interleave-repeat : (a : A) → interleave (repeat a) (repeat a) ≈ repeat a
interleave-repeat a .head = P.refl
interleave-repeat a .tail = interleave-repeat a

zipWith-repeat : ∀ (f : A → B → C) a b →
                 zipWith f (repeat a) (repeat b) ≈ repeat (f a b)
zipWith-repeat f a b .head = P.refl
zipWith-repeat f a b .tail = zipWith-repeat f a b

------------------------------------------------------------------------
-- Properties of map

map-const : (a : A) (bs : Stream B) → map (const a) bs ≈ repeat a
map-const a bs .head = P.refl
map-const a bs .tail = map-const a (bs .tail)

map-identity : (as : Stream A) → map id as ≈ as
map-identity as .head = P.refl
map-identity as .tail = map-identity (as .tail)

map-fusion : ∀ (g : B → C) (f : A → B) as → map g (map f as) ≈ map (g ∘′ f) as
map-fusion g f as .head = P.refl
map-fusion g f as .tail = map-fusion g f (as .tail)

------------------------------------------------------------------------
-- Properties of zipWith

zipWith-defn : ∀ (f : A → B → C) as bs →
               zipWith f as bs ≈ (repeat f ⟨ ap ⟩ as ⟨ ap ⟩ bs)
zipWith-defn f as bs .head = P.refl
zipWith-defn f as bs .tail = zipWith-defn f (as .tail) (bs .tail)

zipWith-const : (as : Stream A) (bs : Stream B) →
                zipWith const as bs ≈ as
zipWith-const as bs .head = P.refl
zipWith-const as bs .tail = zipWith-const (as .tail) (bs .tail)

zipWith-flip : ∀ (f : A → B → C) as bs →
               zipWith (flip f) as bs ≈ zipWith f bs as
zipWith-flip f as bs .head = P.refl
zipWith-flip f as bs .tail = zipWith-flip f (as .tail) (bs. tail)

------------------------------------------------------------------------
-- Properties of interleave

interleave-evens-odds : (as : Stream A) → interleave (evens as) (odds as) ≈ as
interleave-evens-odds as .head       = P.refl
interleave-evens-odds as .tail .head = P.refl
interleave-evens-odds as .tail .tail = interleave-evens-odds (as .tail .tail)
