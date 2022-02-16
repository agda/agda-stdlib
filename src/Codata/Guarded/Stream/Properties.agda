------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of infinite streams defined as coinductive records
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream.Properties where

open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Relation.Binary.Pointwise
  as B using (_≈_; head; tail; module ≈-Reasoning)

open import Data.Nat.Base using (zero; suc; _+_)
import Data.Nat.GeneralisedArithmetic as ℕ
open import Data.Product as Prod using (_,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec; _∷_)
open import Function.Base using (const; flip; id; _∘′_; _$′_; _⟨_⟩_; _∘₂′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Congruence

cong-take : ∀ n {as bs : Stream A} → as ≈ bs → take n as ≡ take n bs
cong-take zero    as≈bs = P.refl
cong-take (suc n) as≈bs = cong₂ _∷_ (as≈bs .head) (cong-take n (as≈bs .tail))

cong-drop : ∀ n {as bs : Stream A} → as ≈ bs → drop n as ≈ drop n bs
cong-drop zero    as≈bs = as≈bs
cong-drop (suc n) as≈bs = cong-drop n (as≈bs .tail)

cong-map : ∀ (f : A → B) {as bs} → as ≈ bs → map f as ≈ map f bs
cong-map f as≈bs .head = cong f (as≈bs .head)
cong-map f as≈bs .tail = cong-map f (as≈bs .tail)

cong-zipWith : ∀ (f : A → B → C) {as bs cs ds} → as ≈ bs → cs ≈ ds →
               zipWith f as cs ≈ zipWith f bs ds
cong-zipWith f as≈bs cs≈ds .head = cong₂ f (as≈bs .head) (cs≈ds .head)
cong-zipWith f as≈bs cs≈ds .tail = cong-zipWith f (as≈bs .tail) (cs≈ds .tail)

cong-interleave : {as bs cs ds : Stream A} → as ≈ bs → cs ≈ ds →
                  interleave as cs ≈ interleave bs ds
cong-interleave as≈bs cs≈ds .head = as≈bs .head
cong-interleave as≈bs cs≈ds .tail = cong-interleave cs≈ds (as≈bs .tail)

cong-chunksOf : ∀ n {as bs : Stream A} → as ≈ bs → chunksOf n as ≈ chunksOf n bs
cong-chunksOf n as≈bs .head = cong-take n as≈bs
cong-chunksOf n as≈bs .tail = cong-chunksOf n (cong-drop n as≈bs)

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

{-

-- Oops the productivity checker doesn't like this .tail case!
chunksOf-repeat : ∀ n (a : A) → chunksOf n (repeat a) ≈ repeat (Vec.replicate a)
chunksOf-repeat n a .head = take-repeat n a
chunksOf-repeat n a .tail = begin
  chunksOf n (drop n (repeat a)) ≡⟨ cong (chunksOf n) (drop-repeat n a) ⟩
  chunksOf n (repeat a)          ≈⟨ chunksOf-repeat n a ⟩
  repeat (Vec.replicate a)       ∎ where open ≈-Reasoning

-}

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

map-drop : ∀ (f : A → B) n as → map f (drop n as) ≡ drop n (map f as)
map-drop f zero    as = P.refl
map-drop f (suc n) as = map-drop f n (as .tail)

map-zipWith : ∀ (g : C → D) (f : A → B → C) as bs →
              map g (zipWith f as bs) ≈ zipWith (g ∘₂′ f) as bs
map-zipWith g f as bs .head = P.refl
map-zipWith g f as bs .tail = map-zipWith g f (as .tail) (bs .tail)

map-interleave : ∀ (f : A → B) as bs →
                 map f (interleave as bs) ≈ interleave (map f as) (map f bs)
map-interleave f as bs .head = P.refl
map-interleave f as bs .tail = map-interleave f bs (as .tail)

------------------------------------------------------------------------
-- Properties of take

take-iterate : ∀ n f (x : A) → take n (iterate f x) ≡ Vec.iterate f x
take-iterate zero    f x = P.refl
take-iterate (suc n) f x = cong (x ∷_) (take-iterate n f (f x))

take-zipWith : ∀ n (f : A → B → C) as bs →
               take n (zipWith f as bs) ≡ Vec.zipWith f (take n as) (take n bs)
take-zipWith zero    f as bs = P.refl
take-zipWith (suc n) f as bs =
  cong (f (as .head) (bs .head) ∷_) (take-zipWith n f (as .tail) (bs . tail))

------------------------------------------------------------------------
-- Properties of drop

drop-fusion : ∀ m n (as : Stream A) → drop n (drop m as) ≡ drop (m + n) as
drop-fusion zero    n as = P.refl
drop-fusion (suc m) n as = drop-fusion m n (as .tail)

drop-zipWith : ∀ n (f : A → B → C) as bs →
               drop n (zipWith f as bs) ≡ zipWith f (drop n as) (drop n bs)
drop-zipWith zero    f as bs = P.refl
drop-zipWith (suc n) f as bs = drop-zipWith n f (as .tail) (bs .tail)

drop-ap : ∀ n (fs : Stream (A → B)) as →
          drop n (ap fs as) ≡ ap (drop n fs) (drop n as)
drop-ap zero    fs as = P.refl
drop-ap (suc n) fs as = drop-ap n (fs .tail) (as .tail)

drop-iterate : ∀ n f (x : A) → drop n (iterate f x) ≡ iterate f (ℕ.iterate f x n)
drop-iterate zero    f x = P.refl
drop-iterate (suc n) f x = drop-iterate n f (f x)

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
