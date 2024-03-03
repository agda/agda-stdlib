------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined as functions from a finite set to a type.
------------------------------------------------------------------------

-- This implementation is designed for reasoning about fixed-size
-- vectors where ease of retrieval of elements is prioritised.

-- See `Data.Vec` for an alternative implementation using inductive
-- data-types, which is more suitable for reasoning about vectors that
-- will grow or shrink in size.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional where

open import Data.Fin.Base
open import Data.List.Base as L using (List)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; NonZero; pred)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Base as V using (Vec)
open import Function.Base using (_∘_; const; flip; _ˢ_; id)
open import Level using (Level)

infixr 5 _∷_ _++_
infixl 4 _⊛_
infixl 1 _>>=_

private
  variable
    a b c : Level
    A B C : Set a
    m n : ℕ

------------------------------------------------------------------------
-- Definition

Vector : Set a → ℕ → Set a
Vector A n = Fin n → A

------------------------------------------------------------------------
-- Conversion

toVec : Vector A n → Vec A n
toVec = V.tabulate

fromVec : Vec A n → Vector A n
fromVec = V.lookup

toList : Vector A n → List A
toList = L.tabulate

fromList : ∀ (xs : List A) → Vector A (L.length xs)
fromList = L.lookup

------------------------------------------------------------------------
-- Basic operations

[] : Vector A zero
[] ()

_∷_ : A → Vector A n → Vector A (suc n)
(x ∷ xs) zero    = x
(x ∷ xs) (suc i) = xs i

length : Vector A n → ℕ
length {n = n} _ = n

head : Vector A (suc n) → A
head xs = xs zero

tail : Vector A (suc n) → Vector A n
tail xs = xs ∘ suc

uncons : Vector A (suc n) → A × Vector A n
uncons xs = head xs , tail xs

replicate : (n : ℕ) → A → Vector A n
replicate n = const

insertAt : Vector A n → Fin (suc n) → A → Vector A (suc n)
insertAt {n = n}     xs zero    v zero    = v
insertAt {n = n}     xs zero    v (suc j) = xs j
insertAt {n = suc n} xs (suc i) v zero    = head xs
insertAt {n = suc n} xs (suc i) v (suc j) = insertAt (tail xs) i v j

removeAt : Vector A (suc n) → Fin (suc n) → Vector A n
removeAt t i = t ∘ punchIn i

updateAt : Vector A n → Fin n → (A → A) → Vector A n
updateAt {n = suc n} xs zero    f zero    = f (head xs)
updateAt {n = suc n} xs zero    f (suc j) = xs (suc j)
updateAt {n = suc n} xs (suc i) f zero    = head xs
updateAt {n = suc n} xs (suc i) f (suc j) = updateAt (tail xs) i f j

------------------------------------------------------------------------
-- Transformations

map : (A → B) → ∀ {n} → Vector A n → Vector B n
map f xs = f ∘ xs

_++_ : Vector A m → Vector A n → Vector A (m ℕ.+ n)
_++_ {m = m} xs ys i = [ xs , ys ] (splitAt m i)

concat : Vector (Vector A m) n → Vector A (n ℕ.* m)
concat {m = m} xss i = uncurry (flip xss) (quotRem m i)

foldr : (A → B → B) → B → ∀ {n} → Vector A n → B
foldr f z {n = zero}  xs = z
foldr f z {n = suc n} xs = f (head xs) (foldr f z (tail xs))

foldl : (B → A → B) → B → ∀ {n} → Vector A n → B
foldl f z {n = zero}  xs = z
foldl f z {n = suc n} xs = foldl f (f z (head xs)) (tail xs)

rearrange : (Fin m → Fin n) → Vector A n → Vector A m
rearrange r xs = xs ∘ r

_⊛_ : Vector (A → B) n → Vector A n → Vector B n
_⊛_ = _ˢ_

_>>=_ : Vector A m → (A → Vector B n) → Vector B (m ℕ.* n)
xs >>= f = concat (map f xs)

zipWith : (A → B → C) → ∀ {n} → Vector A n → Vector B n → Vector C n
zipWith f xs ys i = f (xs i) (ys i)

unzipWith : (A → B × C) → Vector A n → Vector B n × Vector C n
unzipWith f xs = proj₁ ∘ f ∘ xs , proj₂ ∘ f ∘ xs

zip : Vector A n → Vector B n → Vector (A × B) n
zip = zipWith _,_

unzip : Vector (A × B) n → Vector A n × Vector B n
unzip = unzipWith id

take : ∀ m {n} → Vector A (m ℕ.+ n) → Vector A m
take _ {n = n} xs = xs ∘ (_↑ˡ n)

drop : ∀ m {n} → Vector A (m ℕ.+ n) → Vector A n
drop m xs = xs ∘ (m ↑ʳ_)

reverse : Vector A n → Vector A n
reverse xs = xs ∘ opposite

init : Vector A (suc n) → Vector A n
init xs = xs ∘ inject₁

last : Vector A (suc n) → A
last {n = n} xs = xs (fromℕ n)

transpose : Vector (Vector A n) m → Vector (Vector A m) n
transpose = flip

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

remove : Fin (suc n) → Vector A (suc n) → Vector A n
remove = flip removeAt
{-# WARNING_ON_USAGE remove
"Warning: remove was deprecated in v2.0.
Please use removeAt instead.
NOTE: argument order has been flipped."
#-}
insert = insertAt
{-# WARNING_ON_USAGE insert
"Warning: insert was deprecated in v2.0.
Please use insertAt instead."
#-}
