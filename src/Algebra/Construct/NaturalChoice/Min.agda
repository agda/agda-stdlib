------------------------------------------------------------------------
-- The Agda standard library
--
-- The min operator derived from an arbitrary total order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algebra.Construct.NaturalChoice.Min
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  where

open import Algebra.Core
open import Algebra.Bundles
open import Data.Sum.Base using (inj₁; inj₂; [_,_])
open import Data.Product using (_,_)
open import Function using (id)

open TotalOrder totalOrder renaming (Carrier to A)
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_

----------------------------------------------------------------------------
-- Definition

infixl 7 _⊓_

_⊓_ : Op₂ A
x ⊓ y with total x y
... | inj₁ x≤y = x
... | inj₂ y≤x = y

----------------------------------------------------------------------------
-- Algebraic properties

⊓-sel : Selective _⊓_
⊓-sel x y with total x y
... | inj₁ x≤y = inj₁ Eq.refl
... | inj₂ y≤x = inj₂ Eq.refl

⊓-idem : Idempotent _⊓_
⊓-idem x with ⊓-sel x x
... | inj₁ x⊓x=x = x⊓x=x
... | inj₂ x⊓x=x = x⊓x=x

⊓-cong : Congruent₂ _⊓_
⊓-cong {w} {x} {y} {z} w≈x y≈z with total w y | total x z
... | inj₁ w≤y | inj₁ x≤z = w≈x
... | inj₁ w≤y | inj₂ z≤x = antisym (≤-respʳ-≈ y≈z w≤y) (≤-respʳ-≈ (Eq.sym w≈x) z≤x)
... | inj₂ y≤w | inj₁ x≤z = antisym (≤-respʳ-≈ w≈x y≤w) (≤-respʳ-≈ (Eq.sym y≈z) x≤z)
... | inj₂ y≤w | inj₂ z≤x = y≈z

⊓-comm : Commutative _⊓_
⊓-comm x y with total x y | total y x
... | inj₁ x≤y | inj₁ y≤x = antisym x≤y y≤x
... | inj₁ _   | inj₂ _   = Eq.refl
... | inj₂ _   | inj₁ _   = Eq.refl
... | inj₂ y≤x | inj₂ x≤y = antisym y≤x x≤y

⊓-assoc : Associative _⊓_
⊓-assoc x y z with total x y | total x z | total y z
⊓-assoc x y z | inj₁ x≤y | inj₁ x≤z | inj₁ y≤z with total x z | total x y
... | inj₁ x≤z₂ | inj₁ _    = Eq.refl
... | inj₁ x≤z₂ | inj₂ y≤x  = antisym x≤y y≤x
... | inj₂ z≤x  | inj₁ _    = antisym z≤x (trans x≤y y≤z)
... | inj₂ z≤x  | inj₂ y≤x  = antisym (trans z≤x x≤y) (trans y≤x x≤z)
⊓-assoc x y z | inj₁ x≤y | inj₁ x≤z | inj₂ z≤y with total x z
... | inj₁ _                = Eq.refl
... | inj₂ _                = Eq.refl
⊓-assoc x y z | inj₁ x≤y | inj₂ z≤x | inj₁ y≤z with total x z | total x y
... | inj₁ x≤z  | inj₁ _    = Eq.refl
... | inj₁ x≤z  | inj₂ y≤x  = antisym x≤y (trans y≤z z≤x)
... | inj₂ _    | inj₁ _    = antisym z≤x (trans x≤y y≤z)
... | inj₂ _    | inj₂ y≤x  = antisym (trans z≤x x≤y) y≤z
⊓-assoc x y z | inj₁ x≤y | inj₂ z≤x | inj₂ z≤y with total x z
... | inj₁ _                = Eq.refl
... | inj₂ _                = Eq.refl
⊓-assoc x y z | inj₂ y≤x | inj₁ x≤z | inj₁ y≤z with total y z | total x y
... | inj₁ _    | inj₁ x≤y  = antisym y≤x x≤y
... | inj₁ _    | inj₂ _    = Eq.refl
... | inj₂ z≤y  | inj₁ x≤y  = antisym (trans z≤y y≤x) (trans x≤y y≤z)
... | inj₂ z≤y  | inj₂ _    = antisym z≤y (trans y≤x x≤z)
⊓-assoc x y z | inj₂ y≤x | inj₁ x≤z | inj₂ z≤y with total y z | total x z
... | inj₁ y≤z  | inj₁ _    = antisym y≤x (trans x≤z z≤y)
... | inj₁ y≤z  | inj₂ z≤x  = antisym (trans y≤x x≤z) z≤y
... | inj₂ _    | inj₁ _    = antisym (trans z≤y y≤x) x≤z
... | inj₂ _    | inj₂ z≤x  = Eq.refl
⊓-assoc x y z | inj₂ y≤x | inj₂ z≤x | inj₁ y≤z with total y z | total x y
... | inj₁ _    | inj₁ x≤y  = antisym (trans y≤z z≤x) x≤y
... | inj₁ _    | inj₂ _    = Eq.refl
... | inj₂ z≤y  | inj₁ x≤y  = antisym (trans z≤y y≤x) (trans x≤y y≤z)
... | inj₂ z≤y  | inj₂ _    = antisym z≤y y≤z
⊓-assoc x y z | inj₂ y≤x | inj₂ z≤x | inj₂ z≤y with total y z | total x z
... | inj₁ y≤z  | inj₁ x≤z  = antisym (trans y≤z z≤x) (trans x≤z z≤y)
... | inj₁ y≤z  | inj₂ _    = antisym y≤z z≤y
... | inj₂ _    | inj₁ x≤z  = antisym (trans z≤y y≤x) x≤z
... | inj₂ _    | inj₂ _    = Eq.refl

⊓-identityˡ : ∀ {⊥} → Maximum _≤_ ⊥ → LeftIdentity ⊥ _⊓_
⊓-identityˡ {⊥} top x with total ⊥ x
... | inj₁ ⊥≤x = antisym ⊥≤x (top x)
... | inj₂ x≤⊥ = Eq.refl

⊓-identityʳ : ∀ {⊥} → Maximum _≤_ ⊥ → RightIdentity ⊥ _⊓_
⊓-identityʳ {⊥} top x with total x ⊥
... | inj₁ x≤⊥ = Eq.refl
... | inj₂ ⊥≤x = antisym ⊥≤x (top x)

⊓-identity : ∀ {⊥} → Maximum _≤_ ⊥ → Identity ⊥ _⊓_
⊓-identity top = (⊓-identityˡ top , ⊓-identityʳ top)

⊓-zeroˡ : ∀ {⊥} → Minimum _≤_ ⊥ → LeftZero ⊥ _⊓_
⊓-zeroˡ {⊥} bot x with total ⊥ x
... | inj₁ ⊥≤x = Eq.refl
... | inj₂ x≤⊥ = antisym x≤⊥ (bot x)

⊓-zeroʳ : ∀ {⊥} → Minimum _≤_ ⊥ → RightZero ⊥ _⊓_
⊓-zeroʳ {⊥} bot x with total x ⊥
... | inj₁ x≤⊥ = antisym x≤⊥ (bot x)
... | inj₂ ⊥≤x = Eq.refl

⊓-zero : ∀ {⊥} → Minimum _≤_ ⊥ → Zero ⊥ _⊓_
⊓-zero bot = (⊓-zeroˡ bot , ⊓-zeroʳ bot)

----------------------------------------------------------------------------
-- Algebraic structures

⊓-isMagma : IsMagma _⊓_
⊓-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = ⊓-cong
  }

⊓-isSemigroup : IsSemigroup _⊓_
⊓-isSemigroup = record
  { isMagma = ⊓-isMagma
  ; assoc   = ⊓-assoc
  }

⊓-isBand : IsBand _⊓_
⊓-isBand = record
  { isSemigroup = ⊓-isSemigroup
  ; idem        = ⊓-idem
  }

⊓-isSemilattice : IsSemilattice _⊓_
⊓-isSemilattice = record
  { isBand = ⊓-isBand
  ; comm   = ⊓-comm
  }

⊓-isMonoid : ∀ {⊥} → Maximum _≤_ ⊥ → IsMonoid _⊓_ ⊥
⊓-isMonoid top = record
  { isSemigroup = ⊓-isSemigroup
  ; identity    = ⊓-identity top
  }

⊓-isSelectiveMagma : IsSelectiveMagma _⊓_
⊓-isSelectiveMagma = record
  { isMagma = ⊓-isMagma
  ; sel     = ⊓-sel
  }

----------------------------------------------------------------------------
-- Algebraic bundles

⊓-magma : Magma a ℓ₁
⊓-magma = record
  { isMagma = ⊓-isMagma
  }

⊓-semigroup : Semigroup a ℓ₁
⊓-semigroup = record
  { isSemigroup = ⊓-isSemigroup
  }

⊓-band : Band a ℓ₁
⊓-band = record
  { isBand = ⊓-isBand
  }

⊓-semilattice : Semilattice a ℓ₁
⊓-semilattice = record
  { isSemilattice = ⊓-isSemilattice
  }

⊓-monoid : ∀ {⊥} → Maximum _≤_ ⊥ → Monoid a ℓ₁
⊓-monoid top = record
  { isMonoid = ⊓-isMonoid top
  }

⊓-selectiveMagma : SelectiveMagma a ℓ₁
⊓-selectiveMagma = record
  { isSelectiveMagma = ⊓-isSelectiveMagma
  }

----------------------------------------------------------------------------
-- Other properties

x⊓y≈y⇒y≤x : ∀ {x y} → x ⊓ y ≈ y → y ≤ x
x⊓y≈y⇒y≤x {x} {y} x⊓y≈y with total x y
... | inj₁ _   = reflexive (Eq.sym x⊓y≈y)
... | inj₂ y≤x = y≤x

x⊓y≈x⇒x≤y : ∀ {x y} → x ⊓ y ≈ x → x ≤ y
x⊓y≈x⇒x≤y {x} {y} x⊓y≈x with total x y
... | inj₁ x≤y = x≤y
... | inj₂ _   = reflexive (Eq.sym x⊓y≈x)
