------------------------------------------------------------------------
-- The Agda standard library
--
-- N-ary products
------------------------------------------------------------------------

-- Vectors (as in Data.Vec) also represent n-ary products, so what is
-- the point of this module? The n-ary products below are intended to
-- be used with a fixed n, in which case the nil constructor can be
-- avoided: pairs are represented as pairs (x , y), not as triples
-- (x , y , unit).

module Data.Product.N-ary where

open import Data.Nat as Nat hiding (_^_)
open import Data.Fin hiding (lift)
open import Data.Product as P using (_×_ ; _,_ ; ∃₂ ; uncurry)
open import Data.Sum using (_⊎_)
open import Data.Unit
open import Data.Empty
open import Function
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Types and patterns
------------------------------------------------------------------------

pattern 2+_ n = suc (suc n)

infix 8 _^_
_^_ : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
A ^ 0    = Lift ⊤
A ^ 1    = A
A ^ 2+ n = A × A ^ suc n

pattern [] = lift tt

module _  {a} {A : Set a} where

  infix 3 _∈[_]_
  _∈[_]_ : A → ∀ n → A ^ n → Set a
  a ∈[ 0    ] as      = Lift ⊥
  a ∈[ 1    ] a′      = a ≡ a′
  a ∈[ 2+ n ] a′ , as = a ≡ a′ ⊎ a ∈[ suc n ] as

-- Basic operations
------------------------------------------------------------------------

module _  {a} {A : Set a} where

  cons : ∀ n → A → A ^ n → A ^ suc n
  cons 0       a _  = a
  cons (suc n) a as = a , as

  uncons : ∀ n → A ^ suc n → A × A ^ n
  uncons 0        a        = a , lift tt
  uncons (suc n)  (a , as) = a , as

  head : ∀ n → A ^ suc n → A
  head n as = P.proj₁ (uncons n as)

  tail : ∀ n → A ^ suc n → A ^ n
  tail n as = P.proj₂ (uncons n as)

  lookup : ∀ {n} (k : Fin n) → A ^ n → A
  lookup {suc n} zero    = head n
  lookup {suc n} (suc k) = lookup k ∘′ tail n

  replicate : ∀ n → A → A ^ n
  replicate 0      a = []
  replicate 1      a = a
  replicate (2+ n) a = a , replicate (suc n) a

  tabulate : ∀ n → (Fin n → A) → A ^ n
  tabulate 0      f = []
  tabulate 1      f = f zero
  tabulate (2+ n) f = f zero , tabulate (suc n) (f ∘′ suc)

  append : ∀ m n → A ^ m → A ^ n → A ^ (m Nat.+ n)
  append 0      n xs       ys = ys
  append 1      n x        ys = cons n x ys
  append (2+ m) n (x , xs) ys = x , append (suc m) n xs ys

  splitAt : ∀ m n → A ^ (m Nat.+ n) → A ^ m × A ^ n
  splitAt 0       n xs = [] , xs
  splitAt (suc m) n xs =
    let (ys , zs) = splitAt m n (tail (m Nat.+ n) xs) in
    cons m (head (m Nat.+ n) xs) ys , zs


-- Manipulating N-ary products
------------------------------------------------------------------------

module _ {a b} {A : Set a} {B : Set b} where

  map : (A → B) → ∀ n → A ^ n → B ^ n
  map f 0      as       = lift tt
  map f 1      a        = f a
  map f (2+ n) (a , as) = f a , map f (suc n) as

  ap : ∀ n → (A → B) ^ n → A ^ n → B ^ n
  ap 0      fs       ts       = []
  ap 1      f        t        = f t
  ap (2+ n) (f , fs) (t , ts) = f t , ap (suc n) fs ts

module _ {a p} {A : Set a} {P : ℕ → Set p} where

  foldr : P 0 → (A → P 1) → (∀ n → A → P (suc n) → P (2+ n)) →
          ∀ n → A ^ n → P n
  foldr p0 p1 p2+ 0      as       = p0
  foldr p0 p1 p2+ 1      a        = p1 a
  foldr p0 p1 p2+ (2+ n) (a , as) = p2+ n a (foldr p0 p1 p2+ (suc n) as)

foldl : ∀ {a p} {A : Set a} (P : ℕ → Set p) →
        P 0 → (A → P 1) → (∀ n → A → P (suc n) → P (2+ n)) →
        ∀ n → A ^ n → P n
foldl P p0 p1 p2+ 0      as       = p0
foldl P p0 p1 p2+ 1      a        = p1 a
foldl P p0 p1 p2+ (2+ n) (a , as) = let p1′ = p1 a in
  foldl (P ∘′ suc) p1′ (λ a → p2+ 0 a p1′) (p2+ ∘ suc) (suc n) as

module _ {a} {A : Set a} where

  reverse : ∀ n → A ^ n → A ^ n
  reverse = foldl (A ^_) [] id (λ n → _,_)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  zipWith : (A → B → C) → ∀ n → A ^ n → B ^ n → C ^ n
  zipWith f 0      as       bs       = []
  zipWith f 1      a        b        = f a b
  zipWith f (2+ n) (a , as) (b , bs) = f a b , zipWith f (suc n) as bs

  unzipWith : (A → B × C) → ∀ n → A ^ n → B ^ n × C ^ n
  unzipWith f 0      as       = [] , []
  unzipWith f 1      a        = f a
  unzipWith f (2+ n) (a , as) =
    let (b , c) = f a; (bs , cs) = unzipWith f (suc n) as in
    (b , bs) , (c , cs)

module _ {a b} {A : Set a} {B : Set b} where

  zip : ∀ n → A ^ n → B ^ n → (A × B) ^ n
  zip = zipWith _,_

  unzip : ∀ n → (A × B) ^ n → A ^ n × B ^ n
  unzip = unzipWith id
