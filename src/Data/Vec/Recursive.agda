------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined by recursion
------------------------------------------------------------------------

-- What is the point of this module? The n-ary products below are intended
-- to be used with a fixed n, in which case the nil constructor can be
-- avoided: pairs are represented as pairs (x , y), not as triples
-- (x , y , unit).
-- Additionally, vectors defined by recursion enjoy η-rules. That is to say
-- that two vectors of known length are definitionally equal whenever their
-- elements are.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Recursive where

open import Data.Nat.Base as Nat using (ℕ; zero; suc; NonZero; pred)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Data.Empty.Polymorphic
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (1↔⊤; *↔×)
open import Data.Product.Base as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Algebra using (×-cong)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Unit.Polymorphic.Properties using (⊤↔⊤*)
open import Data.Vec.Base as Vec using (Vec; _∷_)
open import Data.Vec.N-ary using (N-ary)
open import Function.Base using (_∘′_; _∘_; id)
open import Function.Bundles using (_↔_; mk↔′; mk↔)
open import Function.Properties.Inverse using (↔-isEquivalence; ↔-refl; ↔-sym; ↔-trans)
open import Level using (Level; lift)
open import Relation.Unary using (IUniversal; Universal; _⇒_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Binary.Structures using (IsEquivalence)

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c

-- Types and patterns
------------------------------------------------------------------------

infix 8 _^_
_^_ : Set a → ℕ → Set a
A ^ 0    = ⊤
A ^ 1    = A
A ^ (suc n@(suc _)) = A × A ^ n

pattern [] = lift tt

infix 3 _∈[_]_
_∈[_]_ : {A : Set a} → A → ∀ n → A ^ n → Set a
a ∈[ 0    ] as               = ⊥
a ∈[ 1    ] a′               = a ≡ a′
a ∈[ suc n@(suc _) ] a′ , as = a ≡ a′ ⊎ a ∈[ n ] as

-- Basic operations
------------------------------------------------------------------------

cons : ∀ n → A → A ^ n → A ^ suc n
cons 0       a _  = a
cons (suc n) a as = a , as

uncons : ∀ n → A ^ suc n → A × A ^ n
uncons 0        a        = a , lift tt
uncons (suc n)  (a , as) = a , as

head : ∀ n → A ^ suc n → A
head n as = proj₁ (uncons n as)

tail : ∀ n → A ^ suc n → A ^ n
tail n as = proj₂ (uncons n as)

fromVec : ∀[ Vec A ⇒ (A ^_) ]
fromVec = Vec.foldr (_ ^_) (cons _) _

toVec : Π[ (A ^_) ⇒ Vec A ]
toVec 0       as = Vec.[]
toVec (suc n) as = head n as ∷ toVec n (tail n as)

lookup : ∀ {n} → A ^ n → Fin n → A
lookup as (zero {n})  = head n as
lookup as (suc {n} k) = lookup (tail n as) k

replicate : ∀ n → A → A ^ n
replicate n a = fromVec (Vec.replicate a)

tabulate : ∀ n → (Fin n → A) → A ^ n
tabulate n f = fromVec (Vec.tabulate f)

append : ∀ m n → A ^ m → A ^ n → A ^ (m Nat.+ n)
append 0               n xs       ys = ys
append 1               n x        ys = cons n x ys
append (suc m@(suc _)) n (x , xs) ys = x , append m n xs ys

splitAt : ∀ m n → A ^ (m Nat.+ n) → A ^ m × A ^ n
splitAt 0       n xs = [] , xs
splitAt (suc m) n xs =
  let (ys , zs) = splitAt m n (tail (m Nat.+ n) xs) in
  cons m (head (m Nat.+ n) xs) ys , zs


-- Manipulating N-ary products
------------------------------------------------------------------------

map : (A → B) → ∀ n → A ^ n → B ^ n
map f 0      as       = lift tt
map f 1      a        = f a
map f (suc n@(suc _)) (a , as) = f a , map f n as

ap : ∀ n → (A → B) ^ n → A ^ n → B ^ n
ap 0      fs       ts       = []
ap 1      f        t        = f t
ap (suc n@(suc _)) (f , fs) (t , ts) = f t , ap n fs ts

module _ {P : ℕ → Set p} where

  foldr : P 0 → (A → P 1) → (∀ n → A → P (suc n) → P (suc (suc n))) →
          ∀ n → A ^ n → P n
  foldr p0 p1 p2+ 0      as       = p0
  foldr p0 p1 p2+ 1      a        = p1 a
  foldr p0 p1 p2+ (suc n′@(suc n)) (a , as) = p2+ n a (foldr p0 p1 p2+ n′ as)

foldl : (P : ℕ → Set p) →
        P 0 → (A → P 1) → (∀ n → A → P (suc n) → P (suc (suc n))) →
        ∀ n → A ^ n → P n
foldl P p0 p1 p2+ 0      as       = p0
foldl P p0 p1 p2+ 1      a        = p1 a
foldl P p0 p1 p2+ (suc n@(suc _)) (a , as) = let p1′ = p1 a in
  foldl (P ∘′ suc) p1′ (λ a → p2+ 0 a p1′) (p2+ ∘ suc) n as

reverse : ∀ n → A ^ n → A ^ n
reverse = foldl (_ ^_) [] id (λ n → _,_)

zipWith : (A → B → C) → ∀ n → A ^ n → B ^ n → C ^ n
zipWith f 0      as       bs       = []
zipWith f 1      a        b        = f a b
zipWith f ((suc n@(suc _))) (a , as) (b , bs) = f a b , zipWith f n as bs

unzipWith : (A → B × C) → ∀ n → A ^ n → B ^ n × C ^ n
unzipWith f 0               as       = [] , []
unzipWith f 1               a        = f a
unzipWith f (suc n@(suc _)) (a , as) = Prod.zip _,_ _,_ (f a) (unzipWith f n as)

zip : ∀ n → A ^ n → B ^ n → (A × B) ^ n
zip = zipWith _,_

unzip : ∀ n → (A × B) ^ n → A ^ n × B ^ n
unzip = unzipWith id

lift↔ : ∀ n → A ↔ B → A ^ n ↔ B ^ n
lift↔ 0               A↔B = mk↔ ((λ { [] → refl }) , (λ{ [] → refl }))
lift↔ 1               A↔B = A↔B
lift↔ (suc n@(suc _)) A↔B = ×-cong A↔B (lift↔ n A↔B)

Fin[m^n]↔Fin[m]^n : ∀ m n → Fin (m Nat.^ n) ↔ Fin m ^ n
Fin[m^n]↔Fin[m]^n m 0 = ↔-trans 1↔⊤ (↔-sym ⊤↔⊤*)
Fin[m^n]↔Fin[m]^n m 1 = subst (λ x → Fin x ↔ Fin m)
  (trans (sym (+-comm m zero)) (*-comm 1 m)) ↔-refl
Fin[m^n]↔Fin[m]^n m (suc (suc n)) = ↔-trans (*↔× {m = m}) (×-cong ↔-refl (Fin[m^n]↔Fin[m]^n _ _))
