------------------------------------------------------------------------
-- The Agda standard library
--
-- This module constructs the biproduct of two R-modules, and similar
-- for weaker module-like structures.
-- The intended universal property is that the biproduct is both a
-- product and a coproduct in the category of R-modules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Construct.DirectProduct where

open import Algebra.Bundles
open import Algebra.Construct.DirectProduct
open import Algebra.Module.Bundles
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Level

private
  variable
    r s ℓr ℓs m m′ ℓm ℓm′ : Level

------------------------------------------------------------------------
-- Bundles

leftSemimodule : {R : Semiring r ℓr} →
                 LeftSemimodule R m ℓm →
                 LeftSemimodule R m′ ℓm′ →
                 LeftSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
leftSemimodule M N = record
  { _*ₗ_ = λ r → map (r M.*ₗ_) (r N.*ₗ_)
  ; isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
      (commutativeMonoid M.+ᴹ-commutativeMonoid N.+ᴹ-commutativeMonoid)
    ; isPreleftSemimodule = record
      { *ₗ-cong = λ where rr (mm , nn) → M.*ₗ-cong rr mm , N.*ₗ-cong rr nn
      ; *ₗ-zeroˡ = λ where (m , n) → M.*ₗ-zeroˡ m , N.*ₗ-zeroˡ n
      ; *ₗ-distribʳ = λ where
        (m , n) x y → M.*ₗ-distribʳ m x y , N.*ₗ-distribʳ n x y
      ; *ₗ-identityˡ = λ where (m , n) → M.*ₗ-identityˡ m , N.*ₗ-identityˡ n
      ; *ₗ-assoc = λ where x y (m , n) → M.*ₗ-assoc x y m , N.*ₗ-assoc x y n
      ; *ₗ-zeroʳ = λ x → M.*ₗ-zeroʳ x , N.*ₗ-zeroʳ x
      ; *ₗ-distribˡ = λ where
        x (m , n) (m′ , n′) → M.*ₗ-distribˡ x m m′ , N.*ₗ-distribˡ x n n′
      }
    }
  } where module M = LeftSemimodule M; module N = LeftSemimodule N

rightSemimodule : {R : Semiring r ℓr} →
                  RightSemimodule R m ℓm →
                  RightSemimodule R m′ ℓm′ →
                  RightSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
rightSemimodule M N = record
  { _*ᵣ_ = λ mn r → map (M._*ᵣ r) (N._*ᵣ r) mn
  ; isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
      (commutativeMonoid M.+ᴹ-commutativeMonoid N.+ᴹ-commutativeMonoid)
    ; isPrerightSemimodule = record
      { *ᵣ-cong = λ where (mm , nn) rr → M.*ᵣ-cong mm rr , N.*ᵣ-cong nn rr
      ; *ᵣ-zeroʳ = λ where (m , n) → M.*ᵣ-zeroʳ m , N.*ᵣ-zeroʳ n
      ; *ᵣ-distribˡ = λ where
        (m , n) x y → M.*ᵣ-distribˡ m x y , N.*ᵣ-distribˡ n x y
      ; *ᵣ-identityʳ = λ where (m , n) → M.*ᵣ-identityʳ m , N.*ᵣ-identityʳ n
      ; *ᵣ-assoc = λ where
        (m , n) x y → M.*ᵣ-assoc m x y , N.*ᵣ-assoc n x y
      ; *ᵣ-zeroˡ = λ x → M.*ᵣ-zeroˡ x , N.*ᵣ-zeroˡ x
      ; *ᵣ-distribʳ = λ where
        x (m , n) (m′ , n′) → M.*ᵣ-distribʳ x m m′ , N.*ᵣ-distribʳ x n n′
      }
    }
  } where module M = RightSemimodule M; module N = RightSemimodule N

bisemimodule : {R : Semiring r ℓr} {S : Semiring s ℓs} →
               Bisemimodule R S m ℓm →
               Bisemimodule R S m′ ℓm′ →
               Bisemimodule R S (m ⊔ m′) (ℓm ⊔ ℓm′)
bisemimodule M N = record
  { isBisemimodule = record
    { +ᴹ-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
      (commutativeMonoid M.+ᴹ-commutativeMonoid N.+ᴹ-commutativeMonoid)
    ; isPreleftSemimodule = LeftSemimodule.isPreleftSemimodule
      (leftSemimodule M.leftSemimodule N.leftSemimodule)
    ; isPrerightSemimodule = RightSemimodule.isPrerightSemimodule
      (rightSemimodule M.rightSemimodule N.rightSemimodule)
    ; *ₗ-*ᵣ-assoc = λ where
      x (m , n) y → M.*ₗ-*ᵣ-assoc x m y , N.*ₗ-*ᵣ-assoc x n y
    }
  } where module M = Bisemimodule M; module N = Bisemimodule N

semimodule : {R : CommutativeSemiring r ℓr} →
             Semimodule R m ℓm →
             Semimodule R m′ ℓm′ →
             Semimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
semimodule M N = record
  { isSemimodule = record
    { isBisemimodule = Bisemimodule.isBisemimodule
      (bisemimodule M.bisemimodule N.bisemimodule)
    }
  } where module M = Semimodule M; module N = Semimodule N

leftModule : {R : Ring r ℓr} →
             LeftModule R m ℓm →
             LeftModule R m′ ℓm′ →
             LeftModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
leftModule M N = record
  { -ᴹ_ = map M.-ᴹ_ N.-ᴹ_
  ; isLeftModule = record
    { isLeftSemimodule = LeftSemimodule.isLeftSemimodule
      (leftSemimodule M.leftSemimodule N.leftSemimodule)
    ; -ᴹ‿cong = λ where (mm , nn) → M.-ᴹ‿cong mm , N.-ᴹ‿cong nn
    ; -ᴹ‿inverse = λ where
      .proj₁ (m , n) → M.-ᴹ‿inverseˡ m , N.-ᴹ‿inverseˡ n
      .proj₂ (m , n) → M.-ᴹ‿inverseʳ m , N.-ᴹ‿inverseʳ n
    }
  } where module M = LeftModule M; module N = LeftModule N

rightModule : {R : Ring r ℓr} →
              RightModule R m ℓm →
              RightModule R m′ ℓm′ →
              RightModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
rightModule M N = record
  { -ᴹ_ = map M.-ᴹ_ N.-ᴹ_
  ; isRightModule = record
    { isRightSemimodule = RightSemimodule.isRightSemimodule
      (rightSemimodule M.rightSemimodule N.rightSemimodule)
    ; -ᴹ‿cong = λ where (mm , nn) → M.-ᴹ‿cong mm , N.-ᴹ‿cong nn
    ; -ᴹ‿inverse = λ where
      .proj₁ (m , n) → M.-ᴹ‿inverseˡ m , N.-ᴹ‿inverseˡ n
      .proj₂ (m , n) → M.-ᴹ‿inverseʳ m , N.-ᴹ‿inverseʳ n
    }
  } where module M = RightModule M; module N = RightModule N

bimodule : {R : Ring r ℓr} {S : Ring s ℓs} →
           Bimodule R S m ℓm →
           Bimodule R S m′ ℓm′ →
           Bimodule R S (m ⊔ m′) (ℓm ⊔ ℓm′)
bimodule M N = record
  { -ᴹ_ = map M.-ᴹ_ N.-ᴹ_
  ; isBimodule = record
    { isBisemimodule = Bisemimodule.isBisemimodule
      (bisemimodule M.bisemimodule N.bisemimodule)
    ; -ᴹ‿cong = λ where (mm , nn) → M.-ᴹ‿cong mm , N.-ᴹ‿cong nn
    ; -ᴹ‿inverse = λ where
      .proj₁ (m , n) → M.-ᴹ‿inverseˡ m , N.-ᴹ‿inverseˡ n
      .proj₂ (m , n) → M.-ᴹ‿inverseʳ m , N.-ᴹ‿inverseʳ n
    }
  } where module M = Bimodule M; module N = Bimodule N

⟨module⟩ : {R : CommutativeRing r ℓr} →
           Module R m ℓm →
           Module R m′ ℓm′ →
           Module R (m ⊔ m′) (ℓm ⊔ ℓm′)
⟨module⟩ M N = record
  { isModule = record
    { isBimodule = Bimodule.isBimodule (bimodule M.bimodule N.bimodule)
    }
  } where module M = Module M; module N = Module N
