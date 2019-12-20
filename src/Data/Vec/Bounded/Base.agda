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
open import Data.List.Base as List using (List)
open import Data.List.Extrema ℕₚ.≤-totalOrder
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Membership.Propositional using (mapWith∈)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Data.These.Base as These using (These)
open import Function
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

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
-- Conversion functions

fromVec : ∀ {n} → Vec A n → Vec≤ A n
fromVec v = v , ℕₚ.≤-refl

padRight : ∀ {n} → A → Vec≤ A n → Vec A n
padRight a (vs , m≤n)
  with recompute (_ ℕₚ.≤″? _) (ℕₚ.≤⇒≤″ m≤n)
... | less-than-or-equal refl = vs Vec.++ Vec.replicate a

padLeft : ∀ {n} → A → Vec≤ A n → Vec A n
padLeft a as@(vs , m≤n)
  with recompute (_ ℕₚ.≤″? _) (ℕₚ.≤⇒≤″ m≤n)
... | less-than-or-equal {k} ∣as∣+k≡n
  with P.trans (ℕₚ.+-comm k (Vec≤.length as)) ∣as∣+k≡n
... | refl = Vec.replicate a Vec.++ vs

private
  split : ∀ {m n} k → m + k ≡ n → ⌊ k /2⌋ + (m + ⌈ k /2⌉) ≡ n
  split {m} {n} k eq = begin
    ⌊ k /2⌋ + (m + ⌈ k /2⌉) ≡⟨ ℕₚ.+-comm ⌊ k /2⌋ _ ⟩
    m + ⌈ k /2⌉ + ⌊ k /2⌋   ≡⟨ ℕₚ.+-assoc m ⌈ k /2⌉ ⌊ k /2⌋ ⟩
    m + (⌈ k /2⌉ + ⌊ k /2⌋) ≡⟨ P.cong (m +_) (ℕₚ.+-comm ⌈ k /2⌉ ⌊ k /2⌋) ⟩
    m + (⌊ k /2⌋ + ⌈ k /2⌉) ≡⟨ P.cong (m +_) (ℕₚ.⌊n/2⌋+⌈n/2⌉≡n k) ⟩
    m + k                   ≡⟨ eq ⟩
    n                       ∎ where open P.≡-Reasoning

padBoth : ∀ {n} → A → A → Vec≤ A n → Vec A n
padBoth aₗ aᵣ as@(vs , m≤n)
  with recompute (_ ℕₚ.≤″? _) (ℕₚ.≤⇒≤″ m≤n)
... | less-than-or-equal {k} ∣as∣+k≡n
  with split k ∣as∣+k≡n
... | refl = Vec.replicate {n = ⌊ k /2⌋} aₗ
      Vec.++ vs
      Vec.++ Vec.replicate {n = ⌈ k /2⌉} aᵣ


fromList : (as : List A) → Vec≤ A (List.length as)
fromList = fromVec ∘ Vec.fromList

toList : ∀ {n} → Vec≤ A n → List A
toList = Vec.toList ∘ Vec≤.vec

------------------------------------------------------------------------
-- Creating new Vec≤ vectors

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

-- take and drop

take : ∀ {m} n → Vec≤ A m → Vec≤ A (n ⊓ m)
take             zero    _                = []
take             (suc n) (Vec.[] , p)     = []
take {m = suc m} (suc n) (a Vec.∷ as , p) = a ∷ take n (as , ℕₚ.≤-pred p)

drop : ∀ {m} n → Vec≤ A m → Vec≤ A (m ∸ n)
drop             zero    v                = v
drop             (suc n) (Vec.[] , p)     = []
drop {m = suc m} (suc n) (a Vec.∷ as , p) = drop n (as , ℕₚ.≤-pred p)

------------------------------------------------------------------------
-- Lifting a collection of bounded vectors to the same size

rectangle : List (∃ (Vec≤ A)) → ∃ (List ∘ Vec≤ A)
rectangle {A = A} rows = width , padded where

  sizes = List.map proj₁ rows
  width = max 0 sizes

  all≤ : All (λ v → proj₁ v ≤ width) rows
  all≤ = Allₚ.map⁻ (xs≤max 0 sizes)

  padded : List (Vec≤ A width)
  padded = mapWith∈ rows $ λ {x} x∈rows →
    ≤-cast (All.lookup all≤ x∈rows) (proj₂ x)
