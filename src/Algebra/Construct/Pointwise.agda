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

isEquivalence : IsEquivalence _≈_ → IsEquivalence (liftRel _≈_)
isEquivalence isEquivalence = record
  { refl = λ {f} _ → refl {f _}
  ; sym = λ f≈g _ → sym (f≈g _)
  ; trans = λ f≈g g≈h _ → trans (f≈g _) (g≈h _)
  }
  where open IsEquivalence isEquivalence

------------------------------------------------------------------------
-- Structures

isMagma : IsMagma _≈_ _∙_ → IsMagma (liftRel _≈_) (lift₂ _∙_)
isMagma isMagma = record
  { isEquivalence = isEquivalence M.isEquivalence
  ; ∙-cong = λ g h _ → M.∙-cong (g _) (h _)
  }
  where module M = IsMagma isMagma

isSemigroup : IsSemigroup _≈_ _∙_ → IsSemigroup (liftRel _≈_) (lift₂ _∙_)
isSemigroup isSemigroup = record
  { isMagma = isMagma M.isMagma
  ; assoc = λ f g h _ → M.assoc (f _) (g _) (h _)
  }
  where module M = IsSemigroup isSemigroup

isBand : IsBand _≈_ _∙_ → IsBand (liftRel _≈_) (lift₂ _∙_)
isBand isBand = record
  { isSemigroup = isSemigroup M.isSemigroup
  ; idem = λ f _ → M.idem (f _)
  }
  where module M = IsBand isBand

isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _∙_ →
                         IsCommutativeSemigroup (liftRel _≈_) (lift₂ _∙_)
isCommutativeSemigroup isCommutativeSemigroup = record
  { isSemigroup = isSemigroup M.isSemigroup
  ; comm = λ f g _ → M.comm (f _) (g _)
  }
  where module M = IsCommutativeSemigroup isCommutativeSemigroup

isMonoid : IsMonoid _≈_ _∙_ ε → IsMonoid (liftRel _≈_) (lift₂ _∙_) (lift₀ ε)
isMonoid isMonoid = record
  { isSemigroup = isSemigroup M.isSemigroup
  ; identity = (λ f _ → M.identityˡ (f _)) , λ f _ → M.identityʳ (f _)
  }
  where module M = IsMonoid isMonoid

isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε →
                      IsCommutativeMonoid (liftRel _≈_) (lift₂ _∙_) (lift₀ ε)
isCommutativeMonoid isCommutativeMonoid = record
  { isMonoid = isMonoid M.isMonoid
  ; comm = λ f g _ → M.comm (f _) (g _)
  }
  where module M = IsCommutativeMonoid isCommutativeMonoid

isGroup : IsGroup _≈_ _∙_ ε _⁻¹ →
          IsGroup (liftRel _≈_) (lift₂ _∙_) (lift₀ ε) (lift₁ _⁻¹)
isGroup isGroup = record
  { isMonoid = isMonoid M.isMonoid
  ; inverse = (λ f _ → M.inverseˡ (f _)) , λ f _ → M.inverseʳ (f _)
  ; ⁻¹-cong = λ f _ → M.⁻¹-cong (f _)
  }
  where module M = IsGroup isGroup

isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε _⁻¹ →
                 IsAbelianGroup (liftRel _≈_) (lift₂ _∙_) (lift₀ ε) (lift₁ _⁻¹)
isAbelianGroup isAbelianGroup = record
  { isGroup = isGroup M.isGroup
  ; comm = λ f g _ → M.comm (f _) (g _)
  }
  where module M = IsAbelianGroup isAbelianGroup

isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1# →
  IsSemiringWithoutAnnihilatingZero (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
isSemiringWithoutAnnihilatingZero isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = isCommutativeMonoid M.+-isCommutativeMonoid
  ; *-cong =  λ g h _ → M.*-cong (g _) (h _)
  ; *-assoc =  λ f g h _ → M.*-assoc (f _) (g _) (h _)
  ; *-identity = (λ f _ → M.*-identityˡ (f _)) , λ f _ → M.*-identityʳ (f _)
  ; distrib = (λ f g h _ → M.distribˡ (f _) (g _) (h _)) , λ f g h _ → M.distribʳ (f _) (g _) (h _)
  }
  where module M = IsSemiringWithoutAnnihilatingZero isSemiringWithoutAnnihilatingZero

isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1# →
             IsSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
isSemiring isSemiring = record
  { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero M.isSemiringWithoutAnnihilatingZero
  ; zero = (λ f _ → M.zeroˡ (f _)) , λ f _ → M.zeroʳ (f _)
  }
  where module M = IsSemiring isSemiring

isRing : IsRing _≈_ _+_ _*_ -_ 0# 1# →
         IsRing (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₁ -_) (lift₀ 0#) (lift₀ 1#)
isRing isRing = record
  { +-isAbelianGroup = isAbelianGroup M.+-isAbelianGroup
  ; *-cong = λ g h _ → M.*-cong (g _) (h _)
  ; *-assoc = λ f g h _ → M.*-assoc (f _) (g _) (h _)
  ; *-identity = (λ f _ → M.*-identityˡ (f _)) , λ f _ → M.*-identityʳ (f _)
  ; distrib = (λ f g h _ → M.distribˡ (f _) (g _) (h _)) , λ f g h _ → M.distribʳ (f _) (g _) (h _)
  }
  where module M = IsRing isRing


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

