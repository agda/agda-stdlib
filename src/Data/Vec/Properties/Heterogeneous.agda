------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Properties.Heterogeneous where

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ; fromℕ; _↑ˡ_; _↑ʳ_)
open import Data.List.Base as List using (List)
open import Data.Nat.Base
open import Data.Nat.Properties using (+-assoc; +-suc)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; <_,_>; uncurry)
open import Data.Sum.Base using ([_,_]′)
open import Data.Sum.Properties using ([,]-map-commute)
open import Data.Vec.Base
open import Data.Vec.Properties
open import Function.Base
open import Function.Inverse using (_↔_; inverse)
open import Level using (Level)
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_; cong₂)
open P.≡-Reasoning
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (Dec; does; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Product using (_×-dec_)

private
  variable
    a b c d p : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Heterogeneous propositional equality over vectors

data Vec≡-syntax {a : Level} {A : Set a} : {m : ℕ} (xs : Vec A m) {n : ℕ} (ys : Vec A n) → Set (Level.suc a) where

  []  : Vec≡-syntax [] []
  _∷_ : ∀ {m n} {xs} {ys} {z} → Vec≡-syntax {m = m} xs {n} ys →
        Vec≡-syntax (z ∷ xs) (z ∷ ys)

syntax Vec≡-syntax {m = m} xs {n} ys = xs [ m ]≡[ n ] ys

Vec≡-refl : ∀ {n} {xs : Vec A n} → xs [ n ]≡[ n ] xs
Vec≡-refl {xs = []}       = []
Vec≡-refl {xs = (x ∷ xs)} = _∷_ Vec≡-refl

Vec≡-sym : ∀ {m n} {xs : Vec A m} {ys} → xs [ m ]≡[ n ] ys → ys [ n ]≡[ m ] xs
Vec≡-sym []       = []
Vec≡-sym (_∷_ eq) = _∷_ (Vec≡-sym eq)

Vec≡-trans : ∀ {m n p} {xs : Vec A m} {ys} {zs} →
  xs [ m ]≡[ n ] ys → ys [ n ]≡[ p ] zs → xs [ m ]≡[ p ] zs
Vec≡-trans []       t = t
Vec≡-trans (_∷_ eq) (_∷_ t) = _∷_ (Vec≡-trans eq t)

Vec≡-≡ : ∀ {n} {xs ys : Vec A n} → xs [ n ]≡[ n ] ys → xs ≡ ys
Vec≡-≡ []       = refl
Vec≡-≡ (_∷_ eq) = P.cong (_ ∷_) (Vec≡-≡ eq)

Vec≡-transport : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → xs [ m ]≡[ n ] ys →
  Prod.∃ λ (eq : m ≡ n) → (P.subst (Vec A) eq xs ≡ ys)
Vec≡-transport []       = refl , refl
Vec≡-transport (_∷_ eq) with Vec≡-transport eq
... | refl , refl = refl , refl

transport-Vec≡ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
                 (Prod.∃ λ (eq : m ≡ n) → (P.subst (Vec A) eq xs ≡ ys)) →
                 xs [ m ]≡[ n ] ys

transport-Vec≡ (refl , refl) = Vec≡-refl


------------------------------------------------------------------------
-- none of these are type correct without extra work

++-[] : ∀ {m} {xs : Vec A m} → (xs ++ []) [ m + 0 ]≡[ m ] xs
++-[] {xs = []}     = []
++-[] {xs = x ∷ xs} = _∷_ (++-[] {xs = xs})

++-assoc : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
  (xs ++ (ys ++ zs)) [ m + (n + p) ]≡[ (m + n) + p ] ((xs ++ ys) ++ zs)
++-assoc [] = Vec≡-refl
++-assoc (x ∷ xs) = _∷_ (++-assoc xs)

ʳ++-[] : ∀ {m} {xs : Vec A m} → (xs ʳ++ []) [ m + 0 ]≡[ m ] (reverse xs)
ʳ++-[] {xs = xs} = P.subst (λ v → Vec≡-syntax v (reverse xs))
                     (P.sym (unfold-ʳ++ {xs = xs} {ys = []})) (++-[] {xs = reverse xs})

-- reverse is an involution with respect to append.

ʳ++-∷ : ∀ {m n} y (xs : Vec A m) {ys : Vec A n} →
        (xs ʳ++ (y ∷ ys)) [ m + (suc n) ]≡[ suc m + n ] ((y ∷ xs) ʳ++ ys)
ʳ++-∷ {A = A} {m} {n} y xs {ys} = transport-Vec≡ (_,_ (+-suc m n)
  (foldl-fusion (λ {m} → P.subst (Vec A) (+-suc m n)) (y ∷ ys) (y ∷ ys) refl (λ {m} b x → eq b x (+-suc m n)) xs))
  where
    eq : ∀ {m} b (x : A) (p : m + (suc n) ≡ suc (m + n))  →
         (P.subst (Vec A) (P.cong suc p) (x ∷ b)) ≡ x ∷ P.subst (Vec A) p b
    eq b x p rewrite p = refl

ʳ++-Vec≡-cong : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
  ys [ n ]≡[ p ] zs → (xs ʳ++ ys) [ m + n ]≡[ m + p ] (xs ʳ++ zs)
ʳ++-Vec≡-cong [] eq = eq
ʳ++-Vec≡-cong (x ∷ xs) {ys} eq = Vec≡-trans (Vec≡-sym (ʳ++-∷ x xs)) (Vec≡-trans (ʳ++-Vec≡-cong xs (_∷_ eq)) (ʳ++-∷ x xs))

Vec≡-ʳ++-cong : ∀ {m n p} {xs : Vec A m} {ys : Vec A n} (zs : Vec A p) →
  xs [ m ]≡[ n ] ys → (xs ʳ++ zs) [ m + p ]≡[ n + p ] (ys ʳ++ zs)
Vec≡-ʳ++-cong zs []       = Vec≡-refl
Vec≡-ʳ++-cong {xs = z ∷ xs} {ys = z ∷ ys} zs (_∷_ {z = z} eq) = Vec≡-trans (Vec≡-sym (ʳ++-∷ z xs)) (Vec≡-trans (Vec≡-ʳ++-cong (z ∷ zs) eq) (ʳ++-∷ z ys))

-- Reverse-append of append is reverse-append after reverse-append.

ʳ++-++ : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
        ((xs ++ ys) ʳ++ zs) [ (m + n) + p ]≡[ n + (m + p) ] (ys ʳ++ (xs ʳ++ zs))
ʳ++-++ []       {ys} {zs} = Vec≡-refl
ʳ++-++ (x ∷ xs) {ys} {zs} = Vec≡-trans (Vec≡-sym (ʳ++-∷ x (xs ++ ys))) (Vec≡-trans (ʳ++-++ xs {ys} {x ∷ zs}) (ʳ++-Vec≡-cong ys (ʳ++-∷ x xs)))


-- reverse is an involution with respect to append.

reverse-++-commute′ : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} (zs : Vec A p) →
                     (reverse (xs ++ ys) ++ zs) [ m + n + p ]≡[ n + (m + p) ] (reverse ys ++ (reverse xs ++ zs))
reverse-++-commute′ xs {ys} zs
  rewrite P.sym (unfold-ʳ++ {xs = xs ++ ys} {ys = zs})
    | P.sym (unfold-ʳ++ {xs = xs} {ys = zs})
    | P.sym (unfold-ʳ++ {xs = ys} {ys = xs ʳ++ zs})
  = ʳ++-++ xs

reverse-++-commute : ∀ {m n} (xs : Vec A m) (ys : Vec A n) →
                     reverse (xs ++ ys) [ m + n ]≡[ n + m ] (reverse ys ++ reverse xs)
reverse-++-commute xs ys
  with ++-[] {xs = reverse (xs ++ ys)} | ++-[] {xs = reverse ys ++ reverse xs}  | ++-assoc (reverse ys)
... | p | q | r = Vec≡-trans (Vec≡-sym p) (Vec≡-trans (reverse-++-commute′ xs []) (Vec≡-trans r q))


-- Reverse-append of reverse-append is commuted reverse-append after append.

ʳ++-ʳ++ : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
  ((xs ʳ++ ys) ʳ++ zs) [ (m + n) + p ]≡[ n + (m + p) ] (ys ʳ++ (xs ++ zs))
ʳ++-ʳ++ []       {ys} {zs} = Vec≡-refl
ʳ++-ʳ++ (x ∷ xs) {ys} {zs} = Vec≡-trans (Vec≡-sym (Vec≡-ʳ++-cong zs (ʳ++-∷ x xs)) ) (Vec≡-trans (ʳ++-ʳ++ xs {x ∷ ys} {zs}) (Vec≡-sym (ʳ++-∷ x ys)))

