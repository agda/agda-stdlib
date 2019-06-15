------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded vectors, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Bounded.Base where

open import Level using (Level)
open import Data.Nat.Base
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base as Vec using (Vec)
open import Data.These.Base as These using (These)
open import Function
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Types

infix 4 _,_
record Vec≤ (A : Set a) (n : ℕ) : Set a where
  constructor _,_
  field {length} : ℕ
        vec      : Vec A length
        .bound   : length ≤ n

------------------------------------------------------------------------
-- Creating new Vec≤ vectors

fromVec : ∀ {n} → Vec A n → Vec≤ A n
fromVec v = v , ℕₚ.≤-refl

replicate : ∀ {m n} .(m≤n : m ≤ n) → A → Vec≤ A n
replicate m≤n a = Vec.replicate a , m≤n

[] : ∀ {n} → Vec≤ A n
[] = Vec.[] , z≤n

infixr 5 _∷_
_∷_ : ∀ {n} → A → Vec≤ A n → Vec≤ A (suc n)
a ∷ (as , p) = a Vec.∷ as , s≤s p

------------------------------------------------------------------------
-- Modifying Vec≤ vectors

≤-cast : ∀ {m n} → .(m≤n : m ≤ n) → Vec≤ A m → Vec≤ A n
≤-cast m≤n (v , p) = v , ℕₚ.≤-trans p m≤n

≡-cast : ∀ {m n} → .(eq : m ≡ n) → Vec≤ A m → Vec≤ A n
≡-cast m≡n = ≤-cast (ℕₚ.≤-reflexive m≡n)

map : (A → B) → ∀ {n} → Vec≤ A n → Vec≤ B n
map f (v , p) = Vec.map f v , p

reverse : ∀ {n} → Vec≤ A n → Vec≤ A n
reverse (v , p) = Vec.reverse v , p

-- Align and Zip.

alignWith : (These A B → C) → ∀ {n} → Vec≤ A n → Vec≤ B n → Vec≤ C n
alignWith f (as , p) (bs , q) = Vec.alignWith f as bs , ℕₚ.⊔-least p q

zipWith : (A → B → C) → ∀ {n} → Vec≤ A n → Vec≤ B n → Vec≤ C n
zipWith f (as , p) (bs , q) = Vec.restrictWith f as bs , ℕₚ.m≤n⇒m⊓o≤n _ p

zip : ∀ {n} → Vec≤ A n → Vec≤ B n → Vec≤ (A × B) n
zip = zipWith _,_

align : ∀ {n} → Vec≤ A n → Vec≤ B n → Vec≤ (These A B) n
align = alignWith id
