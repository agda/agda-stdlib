------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists: base type and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty.Base where

open import Level using (Level)
open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Nat.Base as ℕ
open import Data.Product as Prod using (∃; _×_; proj₁; proj₂; _,_; -,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function.Base
open import Relation.Binary.PropositionalEquality.Core using (_≢_)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Non-empty lists

infixr 5 _∷_

record List⁺ (A : Set a) : Set a where
  constructor _∷_
  field
    head : A
    tail : List A

open List⁺ public

-- Basic combinators

uncons : List⁺ A → A × List A
uncons (hd ∷ tl) = hd , tl

[_] : A → List⁺ A
[ x ] = x ∷ []

infixr 5 _∷⁺_

_∷⁺_ : A → List⁺ A → List⁺ A
x ∷⁺ y ∷ xs = x ∷ y ∷ xs

length : List⁺ A → ℕ
length (x ∷ xs) = suc (List.length xs)

------------------------------------------------------------------------
-- Conversion

toList : List⁺ A → List A
toList (x ∷ xs) = x ∷ xs

fromList : List A → Maybe (List⁺ A)
fromList []       = nothing
fromList (x ∷ xs) = just (x ∷ xs)

fromVec : ∀ {n} → Vec A (suc n) → List⁺ A
fromVec (x ∷ xs) = x ∷ Vec.toList xs

toVec : (xs : List⁺ A) → Vec A (length xs)
toVec (x ∷ xs) = x ∷ Vec.fromList xs

lift : (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

------------------------------------------------------------------------
-- Other operations

map : (A → B) → List⁺ A → List⁺ B
map f (x ∷ xs) = (f x ∷ List.map f xs)

replicate : ∀ n → n ≢ 0 → A → List⁺ A
replicate n n≢0 a = a ∷ List.replicate (pred n) a

-- Right fold. Note that s is only applied to the last element (see
-- the examples below).

foldr : (A → B → B) → (A → B) → List⁺ A → B
foldr {A = A} {B = B} c s (x ∷ xs) = foldr′ x xs
  where
  foldr′ : A → List A → B
  foldr′ x []       = s x
  foldr′ x (y ∷ xs) = c x (foldr′ y xs)

-- Right fold.

foldr₁ : (A → A → A) → List⁺ A → A
foldr₁ f = foldr f id

-- Left fold. Note that s is only applied to the first element (see
-- the examples below).

foldl : (B → A → B) → (A → B) → List⁺ A → B
foldl c s (x ∷ xs) = List.foldl c (s x) xs

-- Left fold.

foldl₁ : (A → A → A) → List⁺ A → A
foldl₁ f = foldl f id

-- Append (several variants).

infixr 5 _⁺++⁺_ _++⁺_ _⁺++_

_⁺++⁺_ : List⁺ A → List⁺ A → List⁺ A
(x ∷ xs) ⁺++⁺ (y ∷ ys) = x ∷ (xs List.++ y ∷ ys)

_⁺++_ : List⁺ A → List A → List⁺ A
(x ∷ xs) ⁺++ ys = x ∷ (xs List.++ ys)

_++⁺_ : List A → List⁺ A → List⁺ A
xs ++⁺ ys = List.foldr _∷⁺_ ys xs

concat : List⁺ (List⁺ A) → List⁺ A
concat (xs ∷ xss) = xs ⁺++ List.concat (List.map toList xss)

concatMap : (A → List⁺ B) → List⁺ A → List⁺ B
concatMap f = concat ∘′ map f

-- Reverse

reverse : List⁺ A → List⁺ A
reverse = lift (-,_ ∘′ Vec.reverse)

-- Align and Zip

alignWith : (These A B → C) → List⁺ A → List⁺ B → List⁺ C
alignWith f (a ∷ as) (b ∷ bs) = f (these a b) ∷ List.alignWith f as bs

zipWith : (A → B → C) → List⁺ A → List⁺ B → List⁺ C
zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ List.zipWith f as bs

unalignWith : (A → These B C) → List⁺ A → These (List⁺ B) (List⁺ C)
unalignWith f = foldr (These.alignWith mcons mcons ∘′ f)
                    (These.map [_] [_] ∘′ f)

  where mcons : ∀ {e} {E : Set e} → These E (List⁺ E) → List⁺ E
        mcons = These.fold [_] id _∷⁺_

unzipWith : (A → B × C) → List⁺ A → List⁺ B × List⁺ C
unzipWith f (a ∷ as) = Prod.zip _∷_ _∷_ (f a) (List.unzipWith f as)

align : List⁺ A → List⁺ B → List⁺ (These A B)
align = alignWith id

zip : List⁺ A → List⁺ B → List⁺ (A × B)
zip = zipWith _,_

unalign : List⁺ (These A B) → These (List⁺ A) (List⁺ B)
unalign = unalignWith id

unzip : List⁺ (A × B) → List⁺ A × List⁺ B
unzip = unzipWith id

-- Snoc.

infixl 5 _∷ʳ_ _⁺∷ʳ_

_∷ʳ_ : List A → A → List⁺ A
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs List.∷ʳ y)

_⁺∷ʳ_ : List⁺ A → A → List⁺ A
xs ⁺∷ʳ x = toList xs ∷ʳ x

-- A snoc-view of non-empty lists.

infixl 5 _∷ʳ′_

data SnocView {A : Set a} : List⁺ A → Set a where
  _∷ʳ′_ : (xs : List A) (x : A) → SnocView (xs ∷ʳ x)

snocView : (xs : List⁺ A) → SnocView xs
snocView (x ∷ xs)              with List.initLast xs
snocView (x ∷ .[])             | []            = []       ∷ʳ′ x
snocView (x ∷ .(xs List.∷ʳ y)) | xs List.∷ʳ′ y = (x ∷ xs) ∷ʳ′ y

-- The last element in the list.

last : List⁺ A → A
last xs with snocView xs
last .(ys ∷ʳ y) | ys ∷ʳ′ y = y
