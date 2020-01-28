------------------------------------------------------------------------
-- The Agda standard library
--
-- The Colist type and some operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Colist where

open import Level using (Level)
open import Size
open import Data.Unit
open import Data.Nat.Base
open import Data.Product using (_×_ ; _,_)
open import Data.These.Base using (These; this; that; these)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Bounded as Vec≤ using (Vec≤)
open import Function

open import Codata.Thunk using (Thunk; force)
open import Codata.Conat as Conat using (Conat ; zero ; suc)
open import Codata.Cowriter as CW using (Cowriter; _∷_)
open import Codata.Delay as Delay using (Delay ; now ; later)
open import Codata.Stream using (Stream ; _∷_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    a b c w : Level
    i : Size
    A : Set a
    B : Set b
    C : Set c
    W : Set w

data Colist (A : Set a) (i : Size) : Set a where
  []  : Colist A i
  _∷_ : A → Thunk (Colist A) i → Colist A i

------------------------------------------------------------------------
-- Relationship to Cowriter.

fromCowriter : Cowriter W A i → Colist W i
fromCowriter CW.[ _ ] = []
fromCowriter (w ∷ ca) = w ∷ λ where .force → fromCowriter (ca .force)

toCowriter : Colist A i → Cowriter A ⊤ i
toCowriter []       = CW.[ _ ]
toCowriter (a ∷ as) = a ∷ λ where .force → toCowriter (as .force)

------------------------------------------------------------------------
-- Basic functions.

[_] : A → Colist A ∞
[ a ] = a ∷ λ where .force → []

length : Colist A i → Conat i
length []       = zero
length (x ∷ xs) = suc λ where .force → length (xs .force)

replicate : Conat i → A → Colist A i
replicate zero    a = []
replicate (suc n) a = a ∷ λ where .force → replicate (n .force) a

infixr 5 _++_ _⁺++_
_++_ : Colist A i → Colist A i → Colist A i
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ λ where .force → xs .force ++ ys

lookup : ℕ → Colist A ∞ → Maybe A
lookup n       []       = nothing
lookup zero    (a ∷ as) = just a
lookup (suc n) (a ∷ as) = lookup n (as .force)

colookup : Conat i → Colist A i → Delay (Maybe A) i
colookup n       []       = now nothing
colookup zero    (a ∷ as) = now (just a)
colookup (suc n) (a ∷ as) =
  later λ where .force → colookup (n .force) (as .force)

take : (n : ℕ) → Colist A ∞ → Vec≤ A n
take zero    xs       = Vec≤.[]
take n       []       = Vec≤.[]
take (suc n) (x ∷ xs) = x Vec≤.∷ take n (xs .force)

cotake : Conat i → Stream A i → Colist A i
cotake zero    xs       = []
cotake (suc n) (x ∷ xs) = x ∷ λ where .force → cotake (n .force) (xs .force)

drop : ℕ → Colist A ∞ → Colist A ∞
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n (xs .force)

fromList : List A → Colist A ∞
fromList []       = []
fromList (x ∷ xs) = x ∷ λ where .force → fromList xs

fromList⁺ : List⁺ A → Colist A ∞
fromList⁺ = fromList ∘′ List⁺.toList

_⁺++_ : List⁺ A → Thunk (Colist A) i → Colist A i
(x ∷ xs) ⁺++ ys = x ∷ λ where .force → fromList xs ++ ys .force

concat : Colist (List⁺ A) i → Colist A i
concat []         = []
concat (as ∷ ass) = as ⁺++ λ where .force → concat (ass .force)

fromStream : Stream A i → Colist A i
fromStream = cotake Conat.infinity

module ChunksOf (n : ℕ) where

  chunksOf : Colist A ∞ → Cowriter (Vec A n) (Vec≤ A n) i
  chunksOfAcc : ∀ m →
    -- We have two continuations but we are only ever going to use one.
    -- If we had linear types, we'd write the type using the & conjunction here.
    (k≤ : Vec≤ A m → Vec≤ A n) →
    (k≡ : Vec A m → Vec A n) →
    -- Finally we chop up the input stream.
    Colist A ∞ → Cowriter (Vec A n) (Vec≤ A n) i

  chunksOf = chunksOfAcc n id id

  chunksOfAcc zero    k≤ k≡ as       = k≡ [] ∷ λ where .force → chunksOf as
  chunksOfAcc (suc k) k≤ k≡ []       = CW.[ k≤ Vec≤.[] ]
  chunksOfAcc (suc k) k≤ k≡ (a ∷ as) =
    chunksOfAcc k (k≤ ∘ (a Vec≤.∷_)) (k≡ ∘ (a ∷_)) (as .force)

open ChunksOf using (chunksOf) public

-- Test to make sure that the values are kept in the same order
_ : chunksOf 3 (fromList (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
  ≡ (1 ∷ 2 ∷ 3 ∷ []) ∷ _
_ = refl

map : (A → B) → Colist A i → Colist B i
map f []       = []
map f (a ∷ as) = f a ∷ λ where .force → map f (as .force)

unfold : (A → Maybe (A × B)) → A → Colist B i
unfold next seed with next seed
... | nothing          = []
... | just (seed′ , b) = b ∷ λ where .force → unfold next seed′

scanl : (B → A → B) → B → Colist A i → Colist B i
scanl c n []       = n ∷ λ where .force → []
scanl c n (a ∷ as) = n ∷ λ where .force → scanl c (c n a) (as .force)

alignWith : (These A B → C) → Colist A i → Colist B i → Colist C i
alignWith f []         bs       = map (f ∘′ that) bs
alignWith f as@(_ ∷ _) []       = map (f ∘′ this) as
alignWith f (a ∷ as)   (b ∷ bs) =
  f (these a b) ∷ λ where .force → alignWith f (as .force) (bs .force)

zipWith : (A → B → C) → Colist A i → Colist B i → Colist C i
zipWith f []       bs       = []
zipWith f as       []       = []
zipWith f (a ∷ as) (b ∷ bs) =
  f a b ∷ λ where .force → zipWith f (as .force) (bs .force)

align : Colist A i → Colist B i → Colist (These A B) i
align = alignWith id

zip : Colist A i → Colist B i → Colist (A × B) i
zip = zipWith _,_

ap : Colist (A → B) i → Colist A i → Colist B i
ap = zipWith _$′_
