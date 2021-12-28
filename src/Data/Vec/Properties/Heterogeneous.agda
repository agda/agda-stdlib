------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Properties.Heterogeneous where

open import Data.Nat.Base
open import Data.Nat.Properties using (+-assoc; +-suc)
open import Data.Product as Prod
  using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Vec.Base
open import Data.Vec.Properties
-- open import Function.Base
-- open import Function.Inverse using (_↔_; inverse)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_; cong₂)
open P.≡-Reasoning

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Heterogeneous propositional equality over vectors

data ≡ᵥ {a} {A : Set a} : {m : ℕ} (xs : Vec A m) {n : ℕ} (ys : Vec A n) → Set (Level.suc a) where

  []  : ≡ᵥ [] []
  _∷_ : ∀ {m n} z {xs} {ys} → ≡ᵥ {m = m} xs {n} ys →
        ≡ᵥ (z ∷ xs) (z ∷ ys)

syntax ≡ᵥ {m = m} xs {n} ys = xs [ m ]≡[ n ] ys

≡ᵥ-refl : ∀ {n} {xs : Vec A n} → xs [ n ]≡[ n ] xs
≡ᵥ-refl {xs = []}       = []
≡ᵥ-refl {xs = (x ∷ xs)} = x ∷ ≡ᵥ-refl

≡ᵥ-sym : ∀ {m n} {xs : Vec A m} {ys} → xs [ m ]≡[ n ] ys → ys [ n ]≡[ m ] xs
≡ᵥ-sym []       = []
≡ᵥ-sym (z ∷ eq) = z ∷ (≡ᵥ-sym eq)

≡ᵥ-trans : ∀ {m n p} {xs : Vec A m} {ys} {zs} →
  xs [ m ]≡[ n ] ys → ys [ n ]≡[ p ] zs → xs [ m ]≡[ p ] zs
≡ᵥ-trans []       t = t
≡ᵥ-trans (z ∷ eq) (z ∷ t) = z ∷ (≡ᵥ-trans eq t)

≡ᵥ-≡ : ∀ {n} {xs ys : Vec A n} → xs [ n ]≡[ n ] ys → xs ≡ ys
≡ᵥ-≡ []       = refl
≡ᵥ-≡ (z ∷ eq) = P.cong (z ∷_) (≡ᵥ-≡ eq)

≡ᵥ-transport : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → xs [ m ]≡[ n ] ys →
  Σ[ eq ∈ m ≡ n ] P.subst (Vec A) eq xs ≡ ys
≡ᵥ-transport []       = refl , refl
≡ᵥ-transport (z ∷ eq) with ≡ᵥ-transport eq
... | refl , refl = refl , refl

transport-≡ᵥ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
               Σ[ eq ∈ m ≡ n ] P.subst (Vec A) eq xs ≡ ys →
               xs [ m ]≡[ n ] ys

transport-≡ᵥ (refl , refl) = ≡ᵥ-refl

------------------------------------------------------------------------

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

-- This is an adaptation of `≡-Reasoning` from
-- `Relation.Binary.Reasoning.PropositionalEquality.Core`
-- to account for heterogeneous `Vec` equality

module ≡ᵥ-Reasoning {A : Set a} where

  infix  3 _∎ᵥ
  infixr 2 _≡ᵥ⟨⟩_ step-≡ᵥ step-≡ᵥ˘
  infix  1 beginᵥ_

  beginᵥ_ : ∀ {m n} {x : Vec A m} {y : Vec A n} → x [ m ]≡[ n ] y → x [ m ]≡[ n ] y
  beginᵥ_ x≡ᵥy = x≡ᵥy

  _≡ᵥ⟨⟩_ : ∀ {m n} (x : Vec A m) {y : Vec A n} → x [ m ]≡[ n ] y → x [ m ]≡[ n ] y
  _ ≡ᵥ⟨⟩ x≡ᵥy = x≡ᵥy

  step-≡ᵥ : ∀ {m n p} (x : Vec A m) {y : Vec A n} {z : Vec A p} →
            y [ n ]≡[ p ] z → x [ m ]≡[ n ] y → x [ m ]≡[ p ] z
  step-≡ᵥ _ y≡ᵥz x≡ᵥy = ≡ᵥ-trans x≡ᵥy y≡ᵥz

  step-≡ᵥ˘ : ∀ {m n p} (x : Vec A m) {y : Vec A n} {z : Vec A p} →
             y [ n ]≡[ p ] z → y [ n ]≡[ m ] x → x [ m ]≡[ p ] z
  step-≡ᵥ˘ _ y≡ᵥz y≡ᵥx = ≡ᵥ-trans (≡ᵥ-sym y≡ᵥx) y≡ᵥz

  _∎ᵥ : ∀ {n} (x : Vec A n) → x [ n ]≡[ n ] x
  _∎ᵥ _ = ≡ᵥ-refl

  syntax step-≡ᵥ  x y≡ᵥz x≡ᵥy = x ≡ᵥ⟨  x≡ᵥy ⟩ y≡ᵥz
  syntax step-≡ᵥ˘ x y≡ᵥz y≡ᵥx = x ≡ᵥ˘⟨ y≡ᵥx ⟩ y≡ᵥz

------------------------------------------------------------------------
-- none of these are type correct without the above extra work

-- [] is a right identity for ++

++-[] : ∀ {m} {xs : Vec A m} → (xs ++ []) [ m + 0 ]≡[ m ] xs
++-[] {xs = []}     = []
++-[] {xs = x ∷ xs} = x ∷ (++-[] {xs = xs})

-- ++ is associative

++-assoc : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
  (xs ++ (ys ++ zs)) [ m + (n + p) ]≡[ (m + n) + p ] ((xs ++ ys) ++ zs)
++-assoc [] = ≡ᵥ-refl
++-assoc (x ∷ xs) = x ∷ (++-assoc xs)

-- _ʳ++ [] is reverse

ʳ++-[] : ∀ {m} {xs : Vec A m} → (xs ʳ++ []) [ m + 0 ]≡[ m ] (reverse xs)
ʳ++-[] {xs = xs} = P.subst (λ v → ≡ᵥ v (reverse xs))
                     (P.sym (unfold-ʳ++ {xs = xs} {ys = []})) (++-[] {xs = reverse xs})

-- unfolding reverse-append on cons

ʳ++-∷ : ∀ {m n} y (xs : Vec A m) {ys : Vec A n} →
        (xs ʳ++ (y ∷ ys)) [ m + suc n ]≡[ suc m + n ] ((y ∷ xs) ʳ++ ys)
ʳ++-∷ {A = A} {m} {n} y xs {ys} = transport-≡ᵥ
  (+-suc m n , foldl-fusion h e e refl (λ {m} b x → eq b x (+-suc m n)) xs)
  where
    h : ∀ {m} → Vec A (m + suc n) → Vec A (suc m + n)
    h {m} = P.subst (Vec A) (+-suc m n)
    e : Vec A (suc n)
    e = y ∷ ys
    eq : ∀ {m} b (x : A) (p : m + suc n ≡ suc m + n) →
         (P.subst (Vec A) (P.cong suc p) (x ∷ b)) ≡ x ∷ P.subst (Vec A) p b
    eq b x p rewrite p = refl

-- reverse-append is a left congruence

ʳ++-≡ᵥ-cong : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
  ys [ n ]≡[ p ] zs → (xs ʳ++ ys) [ m + n ]≡[ m + p ] (xs ʳ++ zs)
ʳ++-≡ᵥ-cong []                 eq = eq
ʳ++-≡ᵥ-cong (x ∷ xs) {ys} {zs} eq = beginᵥ
  (x ∷ xs) ʳ++ ys ≡ᵥ⟨ ≡ᵥ-sym (ʳ++-∷ x xs) ⟩
  xs ʳ++ (x ∷ ys) ≡ᵥ⟨ ʳ++-≡ᵥ-cong xs (x ∷ eq) ⟩
  xs ʳ++ (x ∷ zs) ≡ᵥ⟨ ʳ++-∷ x xs ⟩
  (x ∷ xs) ʳ++ zs ∎ᵥ
  where open ≡ᵥ-Reasoning

-- reverse-append is a right congruence

≡ᵥ-ʳ++-cong : ∀ {m n p} {xs : Vec A m} {ys : Vec A n} (zs : Vec A p) →
  xs [ m ]≡[ n ] ys → (xs ʳ++ zs) [ m + p ]≡[ n + p ] (ys ʳ++ zs)
≡ᵥ-ʳ++-cong zs []       = ≡ᵥ-refl
≡ᵥ-ʳ++-cong {xs = z ∷ xs} {ys = z ∷ ys} zs (z ∷ eq) = beginᵥ
  (z ∷ xs) ʳ++ zs ≡ᵥ⟨ ≡ᵥ-sym (ʳ++-∷ z xs) ⟩
  xs ʳ++ (z ∷ zs) ≡ᵥ⟨ ≡ᵥ-ʳ++-cong (z ∷ zs) eq ⟩
  ys ʳ++ (z ∷ zs) ≡ᵥ⟨ ʳ++-∷ z ys ⟩
  (z ∷ ys) ʳ++ zs ∎ᵥ
  where open ≡ᵥ-Reasoning

-- reverse-append of append is reverse-append after reverse-append.

ʳ++-++ : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
        ((xs ++ ys) ʳ++ zs) [ (m + n) + p ]≡[ n + (m + p) ] (ys ʳ++ (xs ʳ++ zs))
ʳ++-++ []       {ys} {zs} = ≡ᵥ-refl
ʳ++-++ (x ∷ xs) {ys} {zs} = beginᵥ
  (x ∷ xs ++ ys) ʳ++ zs    ≡ᵥ⟨ ≡ᵥ-sym (ʳ++-∷ x (xs ++ ys)) ⟩
  (xs ++ ys) ʳ++ (x ∷ zs)  ≡ᵥ⟨ ʳ++-++ xs {ys} {x ∷ zs} ⟩
  ys ʳ++ (xs ʳ++ (x ∷ zs)) ≡ᵥ⟨ ʳ++-≡ᵥ-cong ys (ʳ++-∷ x xs) ⟩
  ys ʳ++ ((x ∷ xs) ʳ++ zs) ∎ᵥ
  where open ≡ᵥ-Reasoning

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
reverse-++-commute xs ys = beginᵥ
  reverse (xs ++ ys)               ≡ᵥ⟨ ≡ᵥ-sym (++-[] {xs = reverse (xs ++ ys)}) ⟩
  reverse (xs ++ ys) ++ []         ≡ᵥ⟨ reverse-++-commute′ xs [] ⟩
  reverse ys ++ (reverse xs ++ []) ≡ᵥ⟨ ++-assoc (reverse ys) ⟩
  (reverse ys ++ reverse xs) ++ [] ≡ᵥ⟨ ++-[] {xs = reverse ys ++ reverse xs} ⟩
  reverse ys ++ reverse xs         ∎ᵥ
  where open ≡ᵥ-Reasoning

-- reverse-append of reverse-append is commuted reverse-append after append.

ʳ++-ʳ++ : ∀ {m n p} (xs : Vec A m) {ys : Vec A n} {zs : Vec A p} →
  ((xs ʳ++ ys) ʳ++ zs) [ (m + n) + p ]≡[ n + (m + p) ] (ys ʳ++ (xs ++ zs))
ʳ++-ʳ++ []       {ys} {zs} = ≡ᵥ-refl
ʳ++-ʳ++ (x ∷ xs) {ys} {zs} = beginᵥ
  ((x ∷ xs) ʳ++ ys) ʳ++ zs ≡ᵥ⟨ ≡ᵥ-sym (≡ᵥ-ʳ++-cong zs (ʳ++-∷ x xs)) ⟩
  (xs ʳ++ (x ∷ ys)) ʳ++ zs ≡ᵥ⟨ ʳ++-ʳ++ xs {x ∷ ys} {zs} ⟩
  (x ∷ ys) ʳ++ (xs ++ zs)  ≡ᵥ⟨ ≡ᵥ-sym (ʳ++-∷ x ys) ⟩
  ys ʳ++ ((x ∷ xs) ++ zs)  ∎ᵥ
  where open ≡ᵥ-Reasoning
