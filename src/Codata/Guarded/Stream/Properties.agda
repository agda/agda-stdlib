------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of infinite streams defined as coinductive records
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Codata.Guarded.Stream.Properties where

open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Relation.Binary.Pointwise
  as B using (_≈_; head; tail; module ≈-Reasoning)

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
import Data.Nat.GeneralisedArithmetic as ℕ
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec; _∷_)
open import Function.Base using (const; flip; id; _∘′_; _$′_; _⟨_⟩_; _∘₂′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_; cong; cong₂)

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Congruence

cong-lookup : ∀ {as bs : Stream A} → as ≈ bs → ∀ n → lookup as n ≡ lookup bs n
cong-lookup = B.lookup⁺

cong-take : ∀ n {as bs : Stream A} → as ≈ bs → take n as ≡ take n bs
cong-take zero    as≈bs = P.refl
cong-take (suc n) as≈bs = cong₂ _∷_ (as≈bs .head) (cong-take n (as≈bs .tail))

cong-drop : ∀ n {as bs : Stream A} → as ≈ bs → drop n as ≈ drop n bs
cong-drop = B.drop⁺

-- This is not map⁺ because the propositional equality relation is
-- not the same on the input and output
cong-map : ∀ (f : A → B) {as bs} → as ≈ bs → map f as ≈ map f bs
cong-map f as≈bs .head = cong f (as≈bs .head)
cong-map f as≈bs .tail = cong-map f (as≈bs .tail)

cong-zipWith : ∀ (f : A → B → C) {as bs cs ds} → as ≈ bs → cs ≈ ds →
               zipWith f as cs ≈ zipWith f bs ds
cong-zipWith f as≈bs cs≈ds .head = cong₂ f (as≈bs .head) (cs≈ds .head)
cong-zipWith f as≈bs cs≈ds .tail = cong-zipWith f (as≈bs .tail) (cs≈ds .tail)

cong-concat : {ass bss : Stream (List⁺ A)} → ass ≈ bss → concat ass ≈ concat bss
cong-concat ass≈bss = cong-++-concat [] ass≈bss
  where
    open Concat
    cong-++-concat : ∀ (as : List A) {ass bss} → ass ≈ bss → ++-concat as ass ≈ ++-concat as bss
    cong-++-concat [] ass≈bss .head = cong List⁺.head (ass≈bss .head)
    cong-++-concat [] ass≈bss .tail rewrite ass≈bss .head = cong-++-concat _ (ass≈bss .tail)
    cong-++-concat (a ∷ as) ass≈bss .head = P.refl
    cong-++-concat (a ∷ as) ass≈bss .tail = cong-++-concat as ass≈bss

cong-interleave : {as bs cs ds : Stream A} → as ≈ bs → cs ≈ ds →
                  interleave as cs ≈ interleave bs ds
cong-interleave as≈bs cs≈ds .head = as≈bs .head
cong-interleave as≈bs cs≈ds .tail = cong-interleave cs≈ds (as≈bs .tail)

cong-chunksOf : ∀ n {as bs : Stream A} → as ≈ bs → chunksOf n as ≈ chunksOf n bs
cong-chunksOf n as≈bs .head = cong-take n as≈bs
cong-chunksOf n as≈bs .tail = cong-chunksOf n (cong-drop n as≈bs)

------------------------------------------------------------------------
-- Properties of repeat

lookup-repeat : ∀ n (a : A) → lookup (repeat a) n ≡ a
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

chunksOf-repeat : ∀ n (a : A) → chunksOf n (repeat a) ≈ repeat (Vec.replicate a)
chunksOf-repeat n a = begin go where

  open ≈-Reasoning

  go : chunksOf n (repeat a) ≈∞ repeat (Vec.replicate a)
  go .head = take-repeat n a
  go .tail =
    chunksOf n (drop n (repeat a)) ≡⟨ P.cong (chunksOf n) (drop-repeat n a) ⟩
    chunksOf n (repeat a)          ↺⟨ go ⟩
    repeat (Vec.replicate a)       ∎

------------------------------------------------------------------------
-- Properties of map

map-const : (a : A) (bs : Stream B) → map (const a) bs ≈ repeat a
map-const a bs .head = P.refl
map-const a bs .tail = map-const a (bs .tail)

map-id : (as : Stream A) → map id as ≈ as
map-id as .head = P.refl
map-id as .tail = map-id (as .tail)

map-∘ : ∀ (g : B → C) (f : A → B) as → map g (map f as) ≈ map (g ∘′ f) as
map-∘ g f as .head = P.refl
map-∘ g f as .tail = map-∘ g f (as .tail)

map-unfold : ∀ (g : B → C) (f : A → A × B) a →
             map g (unfold f a) ≈ unfold (Prod.map₂ g ∘′ f) a
map-unfold g f a .head = P.refl
map-unfold g f a .tail = map-unfold g f (proj₁ (f a))

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

map-concat : ∀ (f : A → B) ass → map f (concat ass) ≈ concat (map (List⁺.map f) ass)
map-concat f ass = map-++-concat [] ass
  where
    open Concat
    map-++-concat : ∀ acc ass → map f (++-concat acc ass) ≈ ++-concat (List.map f acc) (map (List⁺.map f) ass)
    map-++-concat [] ass .head = P.refl
    map-++-concat [] ass .tail = map-++-concat (ass .head .List⁺.tail) (ass .tail)
    map-++-concat (a ∷ as) ass .head = P.refl
    map-++-concat (a ∷ as) ass .tail = map-++-concat as ass

map-cycle : ∀ (f : A → B) as → map f (cycle as) ≈ cycle (List⁺.map f as)
map-cycle f as = run
  (map f (cycle as)                      ≡⟨⟩
  map f (concat (repeat as))             ≈⟨ map-concat f (repeat as) ⟩
  concat (map (List⁺.map f) (repeat as)) ≈⟨ cong-concat (map-repeat (List⁺.map f) as) ⟩
  concat (repeat (List⁺.map f as))       ≡⟨⟩
  cycle (List⁺.map f as)                 ∎)
  where open ≈-Reasoning

------------------------------------------------------------------------
-- Properties of lookup

lookup-drop : ∀ m (as : Stream A) n → lookup (drop m as) n ≡ lookup as (m + n)
lookup-drop zero    as n = P.refl
lookup-drop (suc m) as n = lookup-drop m (as .tail) n

lookup-map : ∀ n (f : A → B) as → lookup (map f as) n ≡ f (lookup as n)
lookup-map zero    f as = P.refl
lookup-map (suc n) f as = lookup-map n f (as . tail)

lookup-iterate : ∀ n f (x : A) → lookup (iterate f x) n ≡ ℕ.iterate f x n
lookup-iterate zero    f x = P.refl
lookup-iterate (suc n) f x = lookup-iterate n f (f x)

lookup-zipWith : ∀ n (f : A → B → C) as bs →
                 lookup (zipWith f as bs) n ≡ f (lookup as n) (lookup bs n)
lookup-zipWith zero f as bs = P.refl
lookup-zipWith (suc n) f as bs = lookup-zipWith n f (as .tail) (bs .tail)

lookup-unfold : ∀ n (f : A → A × B) a →
                lookup (unfold f a) n ≡ proj₂ (f (ℕ.iterate (proj₁ ∘′ f) a n))
lookup-unfold zero    f a = P.refl
lookup-unfold (suc n) f a = lookup-unfold n f (proj₁ (f a))

lookup-tabulate : ∀ n (f : ℕ → A) → lookup (tabulate f) n ≡ f n
lookup-tabulate zero f = P.refl
lookup-tabulate (suc n) f = lookup-tabulate n (f ∘′ suc)

lookup-transpose : ∀ n (ass : List (Stream A)) →
                   lookup (transpose ass) n ≡ List.map (flip lookup n) ass
lookup-transpose n [] = lookup-repeat n []
lookup-transpose n (as ∷ ass) = begin
  lookup (transpose (as ∷ ass)) n            ≡⟨⟩
  lookup (zipWith _∷_ as (transpose ass)) n  ≡⟨ lookup-zipWith n _∷_ as (transpose ass) ⟩
  lookup as n ∷ lookup (transpose ass) n     ≡⟨ cong (lookup as n ∷_) (lookup-transpose n ass) ⟩
  lookup as n ∷ List.map (flip lookup n) ass ≡⟨⟩
  List.map (flip lookup n) (as ∷ ass)        ∎
  where open P.≡-Reasoning

lookup-transpose⁺ : ∀ n (ass : List⁺ (Stream A)) →
                    lookup (transpose⁺ ass) n ≡ List⁺.map (flip lookup n) ass
lookup-transpose⁺ n (as ∷ ass) = begin
  lookup (transpose⁺ (as ∷ ass))          n  ≡⟨⟩
  lookup (zipWith _∷_ as (transpose ass)) n  ≡⟨ lookup-zipWith n _∷_ as (transpose ass) ⟩
  lookup as n ∷ lookup (transpose ass) n     ≡⟨ cong (lookup as n ∷_) (lookup-transpose n ass) ⟩
  lookup as n ∷ List.map (flip lookup n) ass ≡⟨⟩
  List⁺.map (flip lookup n) (as ∷ ass)       ∎
  where open P.≡-Reasoning

lookup-tails : ∀ n (as : Stream A) → lookup (tails as) n ≈ ℕ.iterate tail as n
lookup-tails zero    as = B.refl
lookup-tails (suc n) as = lookup-tails n (as .tail)

lookup-evens : ∀ n (as : Stream A) → lookup (evens as) n ≡ lookup as (n * 2)
lookup-evens zero    as = P.refl
lookup-evens (suc n) as = lookup-evens n (as .tail .tail)

lookup-odds : ∀ n (as : Stream A) → lookup (odds as) n ≡ lookup as (suc (n * 2))
lookup-odds zero    as = P.refl
lookup-odds (suc n) as = lookup-odds n (as .tail .tail)

lookup-interleave-even : ∀ n (as bs : Stream A) →
                         lookup (interleave as bs) (n * 2) ≡ lookup as n
lookup-interleave-even zero    as bs = P.refl
lookup-interleave-even (suc n) as bs = lookup-interleave-even n (as .tail) (bs .tail)

lookup-interleave-odd : ∀ n (as bs : Stream A) →
                        lookup (interleave as bs) (suc (n * 2)) ≡ lookup bs n
lookup-interleave-odd zero    as bs = P.refl
lookup-interleave-odd (suc n) as bs = lookup-interleave-odd n (as .tail) (bs .tail)

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

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-identity = map-id
{-# WARNING_ON_USAGE map-identity
"Warning: map-identity was deprecated in v2.0.
Please use map-id instead."
#-}

map-fusion = map-∘
{-# WARNING_ON_USAGE map-fusion
"Warning: map-fusion was deprecated in v2.0.
Please use map-∘ instead."
#-}
