------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Relation.Binary.LeftOrder where

open import Data.Sum.Base as Sum
open import Data.Sum.Relation.Binary.Pointwise as PW
  using (Pointwise; inj₁; inj₂)
open import Data.Product
open import Data.Empty
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

----------------------------------------------------------------------
-- Definition

infixr 1 _⊎-<_

data _⊎-<_ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
           {ℓ₁ ℓ₂} (_∼₁_ : Rel A₁ ℓ₁) (_∼₂_ : Rel A₂ ℓ₂) :
           Rel (A₁ ⊎ A₂) (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  ₁∼₂ : ∀ {x y}                 → (_∼₁_ ⊎-< _∼₂_) (inj₁ x) (inj₂ y)
  ₁∼₁ : ∀ {x y} (x∼₁y : x ∼₁ y) → (_∼₁_ ⊎-< _∼₂_) (inj₁ x) (inj₁ y)
  ₂∼₂ : ∀ {x y} (x∼₂y : x ∼₂ y) → (_∼₁_ ⊎-< _∼₂_) (inj₂ x) (inj₂ y)

----------------------------------------------------------------------
-- Some properties which are preserved by _⊎-<_

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂}
         where

  drop-inj₁ : ∀ {x y} → (∼₁ ⊎-< ∼₂) (inj₁ x) (inj₁ y) → ∼₁ x y
  drop-inj₁ (₁∼₁ x∼₁y) = x∼₁y

  drop-inj₂ : ∀ {x y} → (∼₁ ⊎-< ∼₂) (inj₂ x) (inj₂ y) → ∼₂ x y
  drop-inj₂ (₂∼₂ x∼₂y) = x∼₂y

  ⊎-<-refl : Reflexive ∼₁ → Reflexive ∼₂ →
             Reflexive (∼₁ ⊎-< ∼₂)
  ⊎-<-refl refl₁ refl₂ {inj₁ x} = ₁∼₁ refl₁
  ⊎-<-refl refl₁ refl₂ {inj₂ y} = ₂∼₂ refl₂

  ⊎-<-transitive : Transitive ∼₁ → Transitive ∼₂ →
                   Transitive (∼₁ ⊎-< ∼₂)
  ⊎-<-transitive trans₁ trans₂ ₁∼₂        (₂∼₂ x∼₂y)  = ₁∼₂
  ⊎-<-transitive trans₁ trans₂ (₁∼₁ x∼₁y) ₁∼₂         = ₁∼₂
  ⊎-<-transitive trans₁ trans₂ (₁∼₁ x∼₁y) (₁∼₁ x∼₁y₁) = ₁∼₁ (trans₁ x∼₁y x∼₁y₁)
  ⊎-<-transitive trans₁ trans₂ (₂∼₂ x∼₂y) (₂∼₂ x∼₂y₁) = ₂∼₂ (trans₂ x∼₂y x∼₂y₁)

  ⊎-<-asymmetric : Asymmetric ∼₁ → Asymmetric ∼₂ →
                   Asymmetric (∼₁ ⊎-< ∼₂)
  ⊎-<-asymmetric asym₁ asym₂ (₁∼₁ x∼₁y) (₁∼₁ x∼₁y₁) = asym₁ x∼₁y x∼₁y₁
  ⊎-<-asymmetric asym₁ asym₂ (₂∼₂ x∼₂y) (₂∼₂ x∼₂y₁) = asym₂ x∼₂y x∼₂y₁

  ⊎-<-total : Total ∼₁ → Total ∼₂ → Total (∼₁ ⊎-< ∼₂)
  ⊎-<-total total₁ total₂ = total
    where
    total : Total (_ ⊎-< _)
    total (inj₁ x) (inj₁ y) = Sum.map ₁∼₁ ₁∼₁ $ total₁ x y
    total (inj₁ x) (inj₂ y) = inj₁ ₁∼₂
    total (inj₂ x) (inj₁ y) = inj₂ ₁∼₂
    total (inj₂ x) (inj₂ y) = Sum.map ₂∼₂ ₂∼₂ $ total₂ x y

  ⊎-<-decidable : Decidable ∼₁ → Decidable ∼₂ →
                  Decidable (∼₁ ⊎-< ∼₂)
  ⊎-<-decidable dec₁ dec₂ (inj₁ x) (inj₁ y) = Dec.map′ ₁∼₁ drop-inj₁ (dec₁ x y)
  ⊎-<-decidable dec₁ dec₂ (inj₁ x) (inj₂ y) = yes ₁∼₂
  ⊎-<-decidable dec₁ dec₂ (inj₂ x) (inj₁ y) = no λ()
  ⊎-<-decidable dec₁ dec₂ (inj₂ x) (inj₂ y) = Dec.map′ ₂∼₂ drop-inj₂ (dec₂ x y)

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {≈₁ : Rel A₁ ℓ₂}
         {ℓ₃ ℓ₄} {∼₂ : Rel A₂ ℓ₃} {≈₂ : Rel A₂ ℓ₄}
         where

  ⊎-<-reflexive : ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ →
                  (Pointwise ≈₁ ≈₂) ⇒ (∼₁ ⊎-< ∼₂)
  ⊎-<-reflexive refl₁ refl₂ (inj₁ x) = ₁∼₁ (refl₁ x)
  ⊎-<-reflexive refl₁ refl₂ (inj₂ x) = ₂∼₂ (refl₂ x)

  ⊎-<-irreflexive : Irreflexive ≈₁ ∼₁ → Irreflexive ≈₂ ∼₂ →
                    Irreflexive (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-irreflexive irrefl₁ irrefl₂ (inj₁ x) (₁∼₁ x∼₁y) = irrefl₁ x x∼₁y
  ⊎-<-irreflexive irrefl₁ irrefl₂ (inj₂ x) (₂∼₂ x∼₂y) = irrefl₂ x x∼₂y

  ⊎-<-antisymmetric : Antisymmetric ≈₁ ∼₁ → Antisymmetric ≈₂ ∼₂ →
                      Antisymmetric (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-antisymmetric antisym₁ antisym₂ (₁∼₁ x∼₁y) (₁∼₁ x∼₁y₁) = inj₁ (antisym₁ x∼₁y x∼₁y₁)
  ⊎-<-antisymmetric antisym₁ antisym₂ (₂∼₂ x∼₂y) (₂∼₂ x∼₂y₁) = inj₂ (antisym₂ x∼₂y x∼₂y₁)

  ⊎-<-respectsʳ : ∼₁ Respectsʳ ≈₁ → ∼₂ Respectsʳ ≈₂ →
                  (∼₁ ⊎-< ∼₂) Respectsʳ (Pointwise ≈₁ ≈₂)
  ⊎-<-respectsʳ resp₁ resp₂ (inj₁ x₁) (₁∼₁ x∼₁y) = ₁∼₁ (resp₁ x₁ x∼₁y)
  ⊎-<-respectsʳ resp₁ resp₂ (inj₂ x₁) ₁∼₂        = ₁∼₂
  ⊎-<-respectsʳ resp₁ resp₂ (inj₂ x₁) (₂∼₂ x∼₂y) = ₂∼₂ (resp₂ x₁ x∼₂y)

  ⊎-<-respectsˡ : ∼₁ Respectsˡ ≈₁ → ∼₂ Respectsˡ ≈₂ →
                  (∼₁ ⊎-< ∼₂) Respectsˡ (Pointwise ≈₁ ≈₂)
  ⊎-<-respectsˡ resp₁ resp₂ (inj₁ x) ₁∼₂        = ₁∼₂
  ⊎-<-respectsˡ resp₁ resp₂ (inj₁ x) (₁∼₁ x∼₁y) = ₁∼₁ (resp₁ x x∼₁y)
  ⊎-<-respectsˡ resp₁ resp₂ (inj₂ x) (₂∼₂ x∼₂y) = ₂∼₂ (resp₂ x x∼₂y)

  ⊎-<-respects₂ : ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                  (∼₁ ⊎-< ∼₂) Respects₂ (Pointwise ≈₁ ≈₂)
  ⊎-<-respects₂ (r₁ , l₁) (r₂ , l₂) = ⊎-<-respectsʳ r₁ r₂ , ⊎-<-respectsˡ l₁ l₂

  ⊎-<-trichotomous : Trichotomous ≈₁ ∼₁ → Trichotomous ≈₂ ∼₂ →
                     Trichotomous (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-trichotomous tri₁ tri₂ (inj₁ x) (inj₂ y) = tri< ₁∼₂ (λ()) (λ())
  ⊎-<-trichotomous tri₁ tri₂ (inj₂ x) (inj₁ y) = tri> (λ()) (λ()) ₁∼₂
  ⊎-<-trichotomous tri₁ tri₂ (inj₁ x) (inj₁ y) with tri₁ x y
  ... | tri< x<y x≉y x≯y = tri< (₁∼₁ x<y) (x≉y ∘ PW.drop-inj₁) (x≯y ∘ drop-inj₁)
  ... | tri≈ x≮y x≈y x≯y = tri≈ (x≮y ∘ drop-inj₁) (inj₁ x≈y) (x≯y ∘ drop-inj₁)
  ... | tri> x≮y x≉y x>y = tri> (x≮y ∘ drop-inj₁) (x≉y ∘ PW.drop-inj₁) (₁∼₁ x>y)
  ⊎-<-trichotomous tri₁ tri₂ (inj₂ x) (inj₂ y) with tri₂ x y
  ... | tri< x<y x≉y x≯y = tri< (₂∼₂ x<y) (x≉y ∘ PW.drop-inj₂) (x≯y ∘ drop-inj₂)
  ... | tri≈ x≮y x≈y x≯y = tri≈ (x≮y ∘ drop-inj₂) (inj₂ x≈y) (x≯y ∘ drop-inj₂)
  ... | tri> x≮y x≉y x>y = tri> (x≮y ∘ drop-inj₂) (x≉y ∘ PW.drop-inj₂) (₂∼₂ x>y)

----------------------------------------------------------------------
-- Some collections of properties which are preserved

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₂}
         {ℓ₃ ℓ₄} {≈₂ : Rel A₂ ℓ₃} {∼₂ : Rel A₂ ℓ₄} where

  ⊎-<-isPreorder : IsPreorder ≈₁ ∼₁ → IsPreorder ≈₂ ∼₂ →
                   IsPreorder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-isPreorder pre₁ pre₂ = record
    { isEquivalence = PW.⊎-isEquivalence (isEquivalence pre₁) (isEquivalence pre₂)
    ; reflexive     = ⊎-<-reflexive (reflexive pre₁) (reflexive pre₂)
    ; trans         = ⊎-<-transitive (trans pre₁) (trans pre₂)
    }
    where open IsPreorder

  ⊎-<-isPartialOrder : IsPartialOrder ≈₁ ∼₁ →
                       IsPartialOrder ≈₂ ∼₂ →
                       IsPartialOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-isPartialOrder po₁ po₂ = record
    { isPreorder = ⊎-<-isPreorder (isPreorder po₁) (isPreorder po₂)
    ; antisym    = ⊎-<-antisymmetric (antisym po₁) (antisym    po₂)
    }
    where open IsPartialOrder

  ⊎-<-isStrictPartialOrder : IsStrictPartialOrder ≈₁ ∼₁ →
                             IsStrictPartialOrder ≈₂ ∼₂ →
                             IsStrictPartialOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-isStrictPartialOrder spo₁ spo₂ = record
    { isEquivalence = PW.⊎-isEquivalence (isEquivalence spo₁) (isEquivalence spo₂)
    ; irrefl        = ⊎-<-irreflexive   (irrefl spo₁) (irrefl   spo₂)
    ; trans         = ⊎-<-transitive    (trans spo₁)  (trans    spo₂)
    ; <-resp-≈      = ⊎-<-respects₂   (<-resp-≈ spo₁) (<-resp-≈ spo₂)
    }
    where open IsStrictPartialOrder

  ⊎-<-isTotalOrder : IsTotalOrder ≈₁ ∼₁ →
                     IsTotalOrder ≈₂ ∼₂ →
                     IsTotalOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-isTotalOrder to₁ to₂ = record
    { isPartialOrder = ⊎-<-isPartialOrder (isPartialOrder to₁) (isPartialOrder to₂)
    ; total          = ⊎-<-total (total to₁) (total to₂)
    }
    where open IsTotalOrder

  ⊎-<-isDecTotalOrder : IsDecTotalOrder ≈₁ ∼₁ →
                        IsDecTotalOrder ≈₂ ∼₂ →
                        IsDecTotalOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-isDecTotalOrder to₁ to₂ = record
    { isTotalOrder = ⊎-<-isTotalOrder (isTotalOrder to₁) (isTotalOrder to₂)
    ; _≟_          = PW.⊎-decidable (_≟_  to₁) (_≟_  to₂)
    ; _≤?_         = ⊎-<-decidable (_≤?_ to₁) (_≤?_ to₂)
    }
    where open IsDecTotalOrder

  ⊎-<-isStrictTotalOrder : IsStrictTotalOrder ≈₁ ∼₁ →
                           IsStrictTotalOrder ≈₂ ∼₂ →
                           IsStrictTotalOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
  ⊎-<-isStrictTotalOrder sto₁ sto₂ = record
    { isEquivalence = PW.⊎-isEquivalence (isEquivalence sto₁) (isEquivalence sto₂)
    ; trans         = ⊎-<-transitive (trans sto₁) (trans sto₂)
    ; compare       = ⊎-<-trichotomous (compare sto₁) (compare sto₂)
    }
    where open IsStrictTotalOrder

------------------------------------------------------------------------
-- "Bundles" can also be combined.

module _ {a b c d e f} where

  ⊎-<-preorder : Preorder a b c →
                 Preorder d e f →
                 Preorder _ _ _
  ⊎-<-preorder p₁ p₂ = record
    { isPreorder   =
        ⊎-<-isPreorder (isPreorder p₁) (isPreorder p₂)
    } where open Preorder

  ⊎-<-poset : Poset a b c →
              Poset a b c →
              Poset _ _ _
  ⊎-<-poset po₁ po₂ = record
    { isPartialOrder =
        ⊎-<-isPartialOrder (isPartialOrder po₁) (isPartialOrder po₂)
    } where open Poset

  ⊎-<-strictPartialOrder : StrictPartialOrder a b c →
                           StrictPartialOrder d e f →
                           StrictPartialOrder _ _ _
  ⊎-<-strictPartialOrder spo₁ spo₂ = record
    { isStrictPartialOrder =
      ⊎-<-isStrictPartialOrder (isStrictPartialOrder spo₁) (isStrictPartialOrder spo₂)
    } where open StrictPartialOrder

  ⊎-<-totalOrder : TotalOrder a b c →
                   TotalOrder d e f →
                   TotalOrder _ _ _
  ⊎-<-totalOrder to₁ to₂ = record
    { isTotalOrder = ⊎-<-isTotalOrder (isTotalOrder to₁) (isTotalOrder to₂)
    } where open TotalOrder

  ⊎-<-decTotalOrder : DecTotalOrder a b c →
                      DecTotalOrder d e f →
                      DecTotalOrder _ _ _
  ⊎-<-decTotalOrder to₁ to₂ = record
    { isDecTotalOrder = ⊎-<-isDecTotalOrder (isDecTotalOrder to₁) (isDecTotalOrder to₂)
    } where open DecTotalOrder

  ⊎-<-strictTotalOrder : StrictTotalOrder a b c →
                         StrictTotalOrder a b c →
                         StrictTotalOrder _ _ _
  ⊎-<-strictTotalOrder sto₁ sto₂ = record
    { isStrictTotalOrder = ⊎-<-isStrictTotalOrder (isStrictTotalOrder sto₁) (isStrictTotalOrder sto₂)
    } where open StrictTotalOrder
