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

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional where

open import Data.Fin.Base
open import Data.List.Base as L using (List)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Base as V using (Vec)
open import Function.Base
open import Level using (Level)

infixr 5 _∷_ _++_
infixl 4 _⊛_
infixl 1 _>>=_

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definition

Vector : Set a → ℕ → Set a
Vector A n = Fin n → A

------------------------------------------------------------------------
-- Conversion

toVec : ∀ {n} → Vector A n → Vec A n
toVec = V.tabulate

fromVec : ∀ {n} → Vec A n → Vector A n
fromVec = V.lookup

toList : ∀ {n} → Vector A n → List A
toList = L.tabulate

fromList : ∀ (xs : List A) → Vector A (L.length xs)
fromList = L.lookup

------------------------------------------------------------------------
-- Basic operations

[] : Vector A zero
[] ()

_∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)
(x ∷ xs) zero    = x
(x ∷ xs) (suc i) = xs i

length : ∀ {n} → Vector A n → ℕ
length {n = n} _ = n

head : ∀ {n} → Vector A (suc n) → A
head xs = xs zero

tail : ∀ {n} → Vector A (suc n) → Vector A n
tail xs = xs ∘ suc

uncons : ∀ {n} → Vector A (suc n) → A × Vector A n
uncons xs = head xs , tail xs

replicate : ∀ {n} → A → Vector A n
replicate = const

insert : ∀ {n} → Vector A n → Fin (suc n) → A → Vector A (suc n)
insert {n = n}     xs zero    v zero    = v
insert {n = n}     xs zero    v (suc j) = xs j
insert {n = suc n} xs (suc i) v zero    = head xs
insert {n = suc n} xs (suc i) v (suc j) = insert (tail xs) i v j

remove : ∀ {n} → Fin (suc n) → Vector A (suc n) → Vector A n
remove i t = t ∘ punchIn i

updateAt : ∀ {n} → Fin n → (A → A) → Vector A n → Vector A n
updateAt {n = suc n} zero    f xs zero    = f (head xs)
updateAt {n = suc n} zero    f xs (suc j) = xs (suc j)
updateAt {n = suc n} (suc i) f xs zero    = head xs
updateAt {n = suc n} (suc i) f xs (suc j) = updateAt i f (tail xs) j

------------------------------------------------------------------------
-- Transformations

map : (A → B) → ∀ {n} → Vector A n → Vector B n
map f xs = f ∘ xs

_++_ : ∀ {m n} → Vector A m → Vector A n → Vector A (m ℕ.+ n)
_++_ {m = m} xs ys i = [ xs , ys ] (splitAt m i)

concat : ∀ {m n} → Vector (Vector A m) n → Vector A (n ℕ.* m)
concat {m = m} xss i = uncurry (flip xss) (quotRem m i)

foldr : (A → B → B) → B → ∀ {n} → Vector A n → B
foldr f z {n = zero}  xs = z
foldr f z {n = suc n} xs = f (head xs) (foldr f z (tail xs))

foldl : (B → A → B) → B → ∀ {n} → Vector A n → B
foldl f z {n = zero}  xs = z
foldl f z {n = suc n} xs = foldl f (f z (head xs)) (tail xs)

rearrange : ∀ {m n} → (Fin m → Fin n) → Vector A n → Vector A m
rearrange r xs = xs ∘ r

_⊛_ : ∀ {n} → Vector (A → B) n → Vector A n → Vector B n
_⊛_ = _ˢ_

_>>=_ : ∀ {m n} → Vector A m → (A → Vector B n) → Vector B (m ℕ.* n)
xs >>= f = concat (map f xs)

zipWith : (A → B → C) → ∀ {n} → Vector A n → Vector B n → Vector C n
zipWith f xs ys i = f (xs i) (ys i)

unzipWith : ∀ {n} → (A → B × C) → Vector A n → Vector B n × Vector C n
unzipWith f xs = proj₁ ∘ f ∘ xs , proj₂ ∘ f ∘ xs

zip : ∀ {n} → Vector A n → Vector B n → Vector (A × B) n
zip = zipWith _,_

unzip : ∀ {n} → Vector (A × B) n → Vector A n × Vector B n
unzip = unzipWith id

take : ∀ m {n} → Vector A (m ℕ.+ n) → Vector A m
take _ {n = n} xs = xs ∘ inject+ n

drop : ∀ m {n} → Vector A (m ℕ.+ n) → Vector A n
drop m xs = xs ∘ raise m

reverse : ∀ {n} → Vector A n → Vector A n
reverse xs = xs ∘ opposite

init : ∀ {n} → Vector A (suc n) → Vector A n
init xs = xs ∘ inject₁

last : ∀ {n} → Vector A (suc n) → A
last {n = n} xs = xs (fromℕ n)

transpose : ∀ {m n} → Vector (Vector A n) m → Vector (Vector A m) n
transpose = flip
