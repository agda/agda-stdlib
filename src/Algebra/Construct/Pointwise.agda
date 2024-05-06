------------------------------------------------------------------------
-- The Agda standard library
--
-- For each `IsX` algebraic structure `S`, lift the structure to the
-- 'pointwise' function space `A → S`: categorically, this is the
-- *power* object in the relevant category of `X` objects and morphisms
--
-- NB the module is parametrised only wrt `A`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Construct.Pointwise {a} (A : Set a) where

open import Algebra.Bundles
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Structures
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘′_; const)
import Function.Relation.Binary.Setoid.Equality as FunctionEquality
open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)


private

  variable
    c ℓ : Level
    C : Set c
    _≈_ : Rel C ℓ
    ε 0# 1# : C
    _⁻¹ -_ : Op₁ C
    _∙_ _+_ _*_ : Op₂ C

  lift₀ : C → A → C
  lift₀ = const

  lift₁ : Op₁ C → Op₁ (A → C)
  lift₁ = _∘′_

  lift₂ : Op₂ C → Op₂ (A → C)
  lift₂ _∙_ g h x = (g x) ∙ (h x)

  liftRel : Rel C ℓ → Rel (A → C) (a ⊔ ℓ)
  liftRel _≈_ g h = ∀ x → (g x) ≈ (h x)


------------------------------------------------------------------------
-- Setoid structure: here rather than elsewhere? (could be imported?)

module _ (isEquivalenceC : IsEquivalence _≈_) where

  open IsEquivalence isEquivalenceC

  isEquivalence : IsEquivalence (liftRel _≈_)
  isEquivalence = record
    { refl = λ {f} x → refl {f x}
    ; sym = λ f≈g x → sym (f≈g x)
    ; trans = λ f≈g g≈h x → trans (f≈g x) (g≈h x)
    }

------------------------------------------------------------------------
-- Structures

module _ (isMagmaC : IsMagma _≈_ _∙_) where

  private
    module M = IsMagma isMagmaC

  isMagma : IsMagma (liftRel _≈_) (lift₂ _∙_)
  isMagma = record
    { isEquivalence = isEquivalence M.isEquivalence
    ; ∙-cong = λ g h x → M.∙-cong (g x) (h x)
    }

module _ (isSemigroupC : IsSemigroup _≈_ _∙_) where

  private
    module M = IsSemigroup isSemigroupC

  isSemigroup : IsSemigroup (liftRel _≈_) (lift₂ _∙_)
  isSemigroup = record
    { isMagma = isMagma M.isMagma
    ; assoc = λ f g h x → M.assoc (f x) (g x) (h x)
    }

module _ (isBandC : IsBand _≈_ _∙_) where

  private
    module M = IsBand isBandC

  isBand : IsBand (liftRel _≈_) (lift₂ _∙_)
  isBand = record
    { isSemigroup = isSemigroup M.isSemigroup
    ; idem = λ f x → M.idem (f x)
    }

module _ (isCommutativeSemigroupC : IsCommutativeSemigroup _≈_ _∙_) where

  private
    module M = IsCommutativeSemigroup isCommutativeSemigroupC

  isCommutativeSemigroup : IsCommutativeSemigroup (liftRel _≈_) (lift₂ _∙_)
  isCommutativeSemigroup = record
    { isSemigroup = isSemigroup M.isSemigroup
    ; comm = λ f g x → M.comm (f x) (g x)
    }

module _ (isMonoidC : IsMonoid _≈_ _∙_ ε) where

  private
    module M = IsMonoid isMonoidC

  isMonoid : IsMonoid (liftRel _≈_) (lift₂ _∙_) (lift₀ ε)
  isMonoid = record
    { isSemigroup = isSemigroup M.isSemigroup
    ; identity = (λ f x → M.identityˡ (f x)) , λ f x → M.identityʳ (f x)
    }

module _ (isCommutativeMonoidC : IsCommutativeMonoid _≈_ _∙_ ε) where

  private
    module M = IsCommutativeMonoid isCommutativeMonoidC

  isCommutativeMonoid : IsCommutativeMonoid (liftRel _≈_) (lift₂ _∙_) (lift₀ ε)
  isCommutativeMonoid = record
    { isMonoid = isMonoid M.isMonoid
    ; comm = λ f g x → M.comm (f x) (g x)
    }

module _ (isGroupC : IsGroup _≈_ _∙_ ε _⁻¹) where

  private
    module M = IsGroup isGroupC

  isGroup : IsGroup (liftRel _≈_) (lift₂ _∙_) (lift₀ ε) (lift₁ _⁻¹)
  isGroup = record
    { isMonoid = isMonoid M.isMonoid
    ; inverse = (λ f x → M.inverseˡ (f x)) , λ f x → M.inverseʳ (f x)
    ; ⁻¹-cong = λ f x → M.⁻¹-cong (f x)
    }

module _ (isAbelianGroupC : IsAbelianGroup _≈_ _∙_ ε _⁻¹) where

  private
    module M = IsAbelianGroup isAbelianGroupC

  isAbelianGroup : IsAbelianGroup (liftRel _≈_) (lift₂ _∙_) (lift₀ ε) (lift₁ _⁻¹)
  isAbelianGroup = record
    { isGroup = isGroup M.isGroup
    ; comm = λ f g x → M.comm (f x) (g x)
    }

module _ (isSemiringWithoutAnnihilatingZeroC : IsSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1#) where

  private
    module M = IsSemiringWithoutAnnihilatingZero isSemiringWithoutAnnihilatingZeroC

  isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = isCommutativeMonoid M.+-isCommutativeMonoid
    ; *-cong =  λ g h x → M.*-cong (g x) (h x)
    ; *-assoc =  λ f g h x → M.*-assoc (f x) (g x) (h x)
    ; *-identity = (λ f x → M.*-identityˡ (f x)) , λ f x → M.*-identityʳ (f x)
    ; distrib = (λ f g h x → M.distribˡ (f x) (g x) (h x)) , λ f g h x → M.distribʳ (f x) (g x) (h x)
    }

module _ (isSemiringC : IsSemiring _≈_ _+_ _*_ 0# 1#) where

  private
    module M = IsSemiring isSemiringC

  isSemiring : IsSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero M.isSemiringWithoutAnnihilatingZero
    ; zero = (λ f x → M.zeroˡ (f x)) , λ f x → M.zeroʳ (f x)
    }

module _ (isRingC : IsRing _≈_ _+_ _*_ -_ 0# 1#) where

  private
    module M = IsRing isRingC

  isRing : IsRing (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₁ -_) (lift₀ 0#) (lift₀ 1#)
  isRing = record
    { +-isAbelianGroup = isAbelianGroup M.+-isAbelianGroup
    ; *-cong = λ g h x → M.*-cong (g x) (h x)
    ; *-assoc = λ f g h x → M.*-assoc (f x) (g x) (h x)
    ; *-identity = (λ f x → M.*-identityˡ (f x)) , λ f x → M.*-identityʳ (f x)
    ; distrib = (λ f g h x → M.distribˡ (f x) (g x) (h x)) , λ f g h x → M.distribʳ (f x) (g x) (h x)
    }


------------------------------------------------------------------------
-- Bundles

magma : Magma c ℓ → Magma (a ⊔ c) (a ⊔ ℓ)
magma m = record { isMagma = isMagma (Magma.isMagma m) }

semigroup : Semigroup c ℓ → Semigroup (a ⊔ c) (a ⊔ ℓ)
semigroup m = record { isSemigroup = isSemigroup (Semigroup.isSemigroup m) }

band : Band c ℓ → Band (a ⊔ c) (a ⊔ ℓ)
band m = record { isBand = isBand (Band.isBand m) }

commutativeSemigroup : CommutativeSemigroup c ℓ → CommutativeSemigroup (a ⊔ c) (a ⊔ ℓ)
commutativeSemigroup m = record { isCommutativeSemigroup = isCommutativeSemigroup (CommutativeSemigroup.isCommutativeSemigroup m) }

monoid : Monoid c ℓ → Monoid (a ⊔ c) (a ⊔ ℓ)
monoid m = record { isMonoid = isMonoid (Monoid.isMonoid m) }

group : Group c ℓ → Group (a ⊔ c) (a ⊔ ℓ)
group m = record { isGroup = isGroup (Group.isGroup m) }

abelianGroup : AbelianGroup c ℓ → AbelianGroup (a ⊔ c) (a ⊔ ℓ)
abelianGroup m = record { isAbelianGroup = isAbelianGroup (AbelianGroup.isAbelianGroup m) }

semiring : Semiring c ℓ → Semiring (a ⊔ c) (a ⊔ ℓ)
semiring m = record { isSemiring = isSemiring (Semiring.isSemiring m) }

ring : Ring c ℓ → Ring (a ⊔ c) (a ⊔ ℓ)
ring m = record { isRing = isRing (Ring.isRing m) }

