------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded vectors, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Bounded.Base where

open import Data.Nat.Base
import Data.Nat.Properties as ℕ
open import Data.List.Base as List using (List)
open import Data.List.Extrema ℕ.≤-totalOrder
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Membership.Propositional using (mapWith∈)
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Data.These.Base as These using (These)
open import Function.Base using (_∘_; id; _$_)
open import Level using (Level)
open import Relation.Nullary.Decidable.Core using (recompute)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c
    m n : ℕ

------------------------------------------------------------------------
-- Types

infix 4 _,_
record Vec≤ (A : Set a) (n : ℕ) : Set a where
  constructor _,_
  field {length} : ℕ
        vec      : Vec A length
        .bound   : length ≤ n

-- projection to recompute irrelevant field
isBounded : (as : Vec≤ A n) → Vec≤.length as ≤ n
isBounded as@(_ , m≤n) = recompute (_ ℕ.≤? _) m≤n

------------------------------------------------------------------------
-- Conversion functions

toVec : (as : Vec≤ A n) → Vec A (Vec≤.length as)
toVec as@(vs , _) = vs

fromVec : Vec A n → Vec≤ A n
fromVec v = v , ℕ.≤-refl

padRight : A → Vec≤ A n → Vec A n
padRight a as@(vs , m≤n)
  with k , refl ← ℕ.m≤n⇒∃[o]m+o≡n m≤n
  = vs Vec.++ Vec.replicate k a

padLeft : A → Vec≤ A n → Vec A n
padLeft a record { length = m ; vec = vs ; bound = m≤n }
  with k , refl ← ℕ.m≤n⇒∃[o]m+o≡n m≤n
  rewrite ℕ.+-comm m k
  = Vec.replicate k a Vec.++ vs

private
  split : ∀ m k → m + k ≡ ⌊ k /2⌋ + (m + ⌈ k /2⌉)
  split m k = begin
    m + k                   ≡⟨ ≡.cong (m +_) (ℕ.⌊n/2⌋+⌈n/2⌉≡n k) ⟨
    m + (⌊ k /2⌋ + ⌈ k /2⌉) ≡⟨ ≡.cong (m +_) (ℕ.+-comm ⌊ k /2⌋ ⌈ k /2⌉) ⟩
    m + (⌈ k /2⌉ + ⌊ k /2⌋) ≡⟨ ℕ.+-assoc m ⌈ k /2⌉ ⌊ k /2⌋ ⟨
    m + ⌈ k /2⌉ + ⌊ k /2⌋   ≡⟨ ℕ.+-comm _ ⌊ k /2⌋ ⟩
    ⌊ k /2⌋ + (m + ⌈ k /2⌉) ∎
    where open ≡-Reasoning

padBoth : A → A → Vec≤ A n → Vec A n
padBoth aₗ aᵣ record { length = m ; vec = vs ; bound = m≤n }
  with k , refl ← ℕ.m≤n⇒∃[o]m+o≡n m≤n
  rewrite split m k
  = Vec.replicate ⌊ k /2⌋ aₗ
      Vec.++ vs
      Vec.++ Vec.replicate ⌈ k /2⌉ aᵣ


fromList : (as : List A) → Vec≤ A (List.length as)
fromList = fromVec ∘ Vec.fromList

toList : Vec≤ A n → List A
toList = Vec.toList ∘ toVec

------------------------------------------------------------------------
-- Creating new Vec≤ vectors

replicate : .(m≤n : m ≤ n) → A → Vec≤ A n
replicate m≤n a = Vec.replicate _ a , m≤n

[] : Vec≤ A n
[] = Vec.[] , z≤n

infixr 5 _∷_
_∷_ : A → Vec≤ A n → Vec≤ A (suc n)
a ∷ (as , p) = a Vec.∷ as , s≤s p

------------------------------------------------------------------------
-- Modifying Vec≤ vectors

≤-cast : .(m≤n : m ≤ n) → Vec≤ A m → Vec≤ A n
≤-cast m≤n (v , p) = v , ℕ.≤-trans p m≤n

≡-cast : .(eq : m ≡ n) → Vec≤ A m → Vec≤ A n
≡-cast m≡n = ≤-cast (ℕ.≤-reflexive m≡n)

map : (A → B) → Vec≤ A n → Vec≤ B n
map f (v , p) = Vec.map f v , p

reverse : Vec≤ A n → Vec≤ A n
reverse (v , p) = Vec.reverse v , p

-- Align and Zip.

alignWith : (These A B → C) → Vec≤ A n → Vec≤ B n → Vec≤ C n
alignWith f (as , p) (bs , q) = Vec.alignWith f as bs , ℕ.⊔-lub p q

zipWith : (A → B → C) → Vec≤ A n → Vec≤ B n → Vec≤ C n
zipWith f (as , p) (bs , q) = Vec.restrictWith f as bs , ℕ.m≤n⇒m⊓o≤n _ p

zip : Vec≤ A n → Vec≤ B n → Vec≤ (A × B) n
zip = zipWith _,_

align : Vec≤ A n → Vec≤ B n → Vec≤ (These A B) n
align = alignWith id

-- take and drop

take : ∀ n → Vec≤ A m → Vec≤ A (n ⊓ m)
take             zero    _                = []
take             (suc n) (Vec.[] , p)     = []
take {m = suc m} (suc n) (a Vec.∷ as , p) = a ∷ take n (as , s≤s⁻¹ p)

drop : ∀ n → Vec≤ A m → Vec≤ A (m ∸ n)
drop             zero    v                = v
drop             (suc n) (Vec.[] , p)     = []
drop {m = suc m} (suc n) (a Vec.∷ as , p) = drop n (as , s≤s⁻¹ p)

------------------------------------------------------------------------
-- Lifting a collection of bounded vectors to the same size

rectangle : List (∃ (Vec≤ A)) → ∃ (List ∘ Vec≤ A)
rectangle {A = A} rows = width , padded where

  sizes = List.map proj₁ rows
  width = max 0 sizes

  all≤ : All (λ v → proj₁ v ≤ width) rows
  all≤ = All.map⁻ (xs≤max 0 sizes)

  padded : List (Vec≤ A width)
  padded = mapWith∈ rows $ λ {x} x∈rows →
    ≤-cast (All.lookup all≤ x∈rows) (proj₂ x)
