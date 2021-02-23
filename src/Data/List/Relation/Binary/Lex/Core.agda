------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Lex.Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; flip; id)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Data.List.Relation.Binary.Pointwise.Core
   using (Pointwise; []; _∷_; head; tail)

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {a ℓ₁ ℓ₂} {A : Set a} (P : Set)
         (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) :
         Rel (List A) (a ⊔ ℓ₁ ⊔ ℓ₂) where
  base : P                             → Lex P _≈_ _≺_ []       []
  halt : ∀ {y ys}                      → Lex P _≈_ _≺_ []       (y ∷ ys)
  this : ∀ {x xs y ys} (x≺y : x ≺ y)   → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x xs y ys} (x≈y : x ≈ y)
         (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

-- Properties

module _ {a ℓ₁ ℓ₂} {A : Set a} {P : Set}
         {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<_ = Lex P _≈_ _≺_

  ¬≤-this : ∀ {x y xs ys} → ¬ (x ≈ y) → ¬ (x ≺ y) →
            ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-this x≉y x≮y (this x≺y)       = x≮y x≺y
  ¬≤-this x≉y x≮y (next x≈y xs<ys) = x≉y x≈y

  ¬≤-next : ∀ {x y xs ys} → ¬ x ≺ y → ¬ xs < ys →
            ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-next x≮y xs≮ys (this x≺y)     = x≮y x≺y
  ¬≤-next x≮y xs≮ys (next _ xs<ys) = xs≮ys xs<ys

  antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                  Asymmetric _≺_ → Antisymmetric _≋_ _<_
  antisymmetric sym ir asym = as
    where
    as : Antisymmetric _≋_ _<_
    as (base _)         (base _)         = []
    as (this x≺y)       (this y≺x)       = ⊥-elim (asym x≺y y≺x)
    as (this x≺y)       (next y≈x ys<xs) = ⊥-elim (ir (sym y≈x) x≺y)
    as (next x≈y xs<ys) (this y≺x)       = ⊥-elim (ir (sym x≈y) y≺x)
    as (next x≈y xs<ys) (next y≈x ys<xs) = x≈y ∷ as xs<ys ys<xs

  toSum : ∀ {x y xs ys} → (x ∷ xs) < (y ∷ ys) → (x ≺ y ⊎ (x ≈ y × xs < ys))
  toSum (this x≺y) = inj₁ x≺y
  toSum (next x≈y xs<ys) = inj₂ (x≈y , xs<ys)
