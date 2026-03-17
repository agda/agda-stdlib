------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Lex where

open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base
   using (Pointwise; []; _∷_; head; tail)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Base using (_∘_; flip; id)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Decidable as Dec
  using (Dec; yes; no; _×?_; _⊎?_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Irreflexive; Asymmetric; Antisymmetric
        ; Decidable; _Respects₂_; _Respects_)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a
    x y : A
    xs ys : List A



------------------------------------------------------------------------
-- Re-exporting the core definitions and properties

open import Data.List.Relation.Binary.Lex.Core public

------------------------------------------------------------------------
-- Properties

module _ {A : Set a} {P : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<_ = Lex P _≈_ _≺_

  ¬≤-this : ¬ (x ≈ y) → ¬ (x ≺ y) → ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-this x≉y x≮y (this x≺y)       = x≮y x≺y
  ¬≤-this x≉y x≮y (next x≈y xs<ys) = x≉y x≈y

  ¬≤-next : ¬ x ≺ y → ¬ xs < ys → ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-next x≮y xs≮ys (this x≺y)     = x≮y x≺y
  ¬≤-next x≮y xs≮ys (next _ xs<ys) = xs≮ys xs<ys

  antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                  Asymmetric _≺_ → Antisymmetric _≋_ _<_
  antisymmetric sym ir asym = as
    where
    as : Antisymmetric _≋_ _<_
    as (base _)         (base _)         = []
    as (this x≺y)       (this y≺x)       = contradiction y≺x (asym x≺y)
    as (this x≺y)       (next y≈x ys<xs) = contradiction x≺y (ir (sym y≈x))
    as (next x≈y xs<ys) (this y≺x)       = contradiction y≺x (ir (sym x≈y))
    as (next x≈y xs<ys) (next y≈x ys<xs) = x≈y ∷ as xs<ys ys<xs

  toSum : (x ∷ xs) < (y ∷ ys) → x ≺ y ⊎ (x ≈ y × xs < ys)
  toSum (this x≺y) = inj₁ x≺y
  toSum (next x≈y xs<ys) = inj₂ (x≈y , xs<ys)

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

  respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _<_ Respects₂ _≋_
  respects₂ eq (resp₁ , resp₂) = resp¹ , resp²
    where
    open IsEquivalence eq using (sym; trans)
    resp¹ : Lex P _≈_ _≺_ xs Respects _≋_
    resp¹ []            xs<[]            = xs<[]
    resp¹ (_   ∷ _)     halt             = halt
    resp¹ (x≈y ∷ _)     (this z≺x)       = this (resp₁ x≈y z≺x)
    resp¹ (x≈y ∷ xs≋ys) (next z≈x zs<xs) =
      next (trans z≈x x≈y) (resp¹ xs≋ys zs<xs)

    resp² : flip (Lex P _≈_ _≺_) ys Respects _≋_
    resp² []            []<ys            = []<ys
    resp² (x≈z ∷ _)     (this x≺y)       = this (resp₂ x≈z x≺y)
    resp² (x≈z ∷ xs≋zs) (next x≈y xs<ys) =
      next (trans (sym x≈z) x≈y) (resp² xs≋zs xs<ys)


  []<[]-⇔ : P ⇔ [] < []
  []<[]-⇔ = mk⇔ base λ { (base p) → p }


  ∷<∷-⇔ : (x ≺ y ⊎ (x ≈ y × xs < ys)) ⇔ (x ∷ xs) < (y ∷ ys)
  ∷<∷-⇔ = mk⇔ [ this , uncurry next ] toSum

  module _ (dec-P : Dec P) (dec-≈ : Decidable _≈_) (dec-≺ : Decidable _≺_)
    where

    decidable : Decidable _<_
    decidable []       []       = Dec.map []<[]-⇔ dec-P
    decidable []       (y ∷ ys) = yes halt
    decidable (x ∷ xs) []       = no λ()
    decidable (x ∷ xs) (y ∷ ys) =
      Dec.map ∷<∷-⇔ (dec-≺ x y ⊎? (dec-≈ x y ×? decidable xs ys))
