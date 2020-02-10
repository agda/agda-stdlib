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
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Equivalence using (_⇔_; equivalence)
open import Function using (_∘_; flip; id)
open import Level using (_⊔_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Binary
open import Data.List.Relation.Binary.Pointwise
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

  transitive : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ →
               Transitive _<_
  transitive eq resp tr = trans
    where
    trans : Transitive (Lex P _≈_ _≺_)
    trans (base p)         (base _)         = base p
    trans (base y)         halt             = halt
    trans halt             (this y≺z)       = halt
    trans halt             (next y≈z ys<zs) = halt
    trans (this x≺y)       (this y≺z)       = this (tr x≺y y≺z)
    trans (this x≺y)       (next y≈z ys<zs) = this (proj₁ resp y≈z x≺y)
    trans (next x≈y xs<ys) (this y≺z)       =
      this (proj₂ resp (IsEquivalence.sym eq x≈y) y≺z)
    trans (next x≈y xs<ys) (next y≈z ys<zs) =
      next (IsEquivalence.trans eq x≈y y≈z) (trans xs<ys ys<zs)

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

  respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _<_ Respects₂ _≋_
  respects₂ eq (resp₁ , resp₂) = resp¹ , resp²
    where
    open IsEquivalence eq using (sym; trans)
    resp¹ : ∀ {xs} → Lex P _≈_ _≺_ xs Respects _≋_
    resp¹ []            xs<[]            = xs<[]
    resp¹ (_   ∷ _)     halt             = halt
    resp¹ (x≈y ∷ _)     (this z≺x)       = this (resp₁ x≈y z≺x)
    resp¹ (x≈y ∷ xs≋ys) (next z≈x zs<xs) =
      next (trans z≈x x≈y) (resp¹ xs≋ys zs<xs)

    resp² : ∀ {ys} → flip (Lex P _≈_ _≺_) ys Respects _≋_
    resp² []            []<ys            = []<ys
    resp² (x≈z ∷ _)     (this x≺y)       = this (resp₂ x≈z x≺y)
    resp² (x≈z ∷ xs≋zs) (next x≈y xs<ys) =
      next (trans (sym x≈z) x≈y) (resp² xs≋zs xs<ys)

  []<[]-⇔ : P ⇔ [] < []
  []<[]-⇔ = equivalence base (λ { (base p) → p })

  toSum : ∀ {x y xs ys} → (x ∷ xs) < (y ∷ ys) → (x ≺ y ⊎ (x ≈ y × xs < ys))
  toSum (this x≺y) = inj₁ x≺y
  toSum (next x≈y xs<ys) = inj₂ (x≈y , xs<ys)

  ∷<∷-⇔ : ∀ {x y xs ys} → (x ≺ y ⊎ (x ≈ y × xs < ys)) ⇔ (x ∷ xs) < (y ∷ ys)
  ∷<∷-⇔ = equivalence [ this , uncurry next ] toSum

  module _ (dec-P : Dec P) (dec-≈ : Decidable _≈_) (dec-≺ : Decidable _≺_)
    where

    decidable : Decidable _<_
    decidable []       []       = Dec.map []<[]-⇔ dec-P
    decidable []       (y ∷ ys) = yes halt
    decidable (x ∷ xs) []       = no λ()
    decidable (x ∷ xs) (y ∷ ys) =
      Dec.map ∷<∷-⇔ (dec-≺ x y ⊎-dec (dec-≈ x y ×-dec decidable xs ys))
