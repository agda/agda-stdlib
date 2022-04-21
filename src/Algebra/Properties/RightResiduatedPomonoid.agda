------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right-residuated partially ordered monoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Ordered.Residuated

module Algebra.Properties.RightResiduatedPomonoid
  {a ℓ₁ ℓ₂} (rrp : RightResiduatedPomonoid a ℓ₁ ℓ₂)
  where

open import Algebra.Definitions using (Congruent₂; Commutative)
import Algebra.Construct.Flip.Op as FlipOp
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Base using (flip)
open import Function.GaloisConnection
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
open import Relation.Binary.Consequences using (mono₂⇒cong₂)
open import Relation.Binary.Definitions using (Adjoint)

open RightResiduatedPomonoid rrp
open PosetReasoning (record { isPartialOrder = isPartialOrder })


------------------------------------------------------------------------------
-- Useful (in)equations.

\\-cong : Congruent₂ _≈_ _\\_
\\-cong x≈y u≈v =
  antisym (\\-mono (reflexive (Eq.sym x≈y)) (reflexive u≈v))
          (\\-mono (reflexive x≈y) (reflexive (Eq.sym u≈v)))

∙-\\-assoc : ∀ {x y z} → ((x ∙ y) \\ z) ≈ (y \\ (x \\ z))
∙-\\-assoc {x} {y} {z} = antisym
  (proj₁ adjoint (proj₁ adjoint (begin
    x ∙ (y ∙ ((x ∙ y) \\ z))    ≈⟨ Eq.sym (assoc x y _) ⟩
    (x ∙ y) ∙ ((x ∙ y) \\ z)    ≤⟨ counit ⟩
    z ∎)))
  (proj₁ adjoint (begin
    (x ∙ y) ∙ (y \\ (x \\ z))   ≈⟨ assoc x y _ ⟩
    x ∙ (y ∙ (y \\ (x \\ z)))   ≤⟨ ∙-mono₂ x counit ⟩
    x ∙ (x \\ z)                ≤⟨ counit ⟩
    z ∎))

\\-∙-assoc : ∀ {x y z} → ((x \\ y) ∙ z) ≤ (x \\ (y ∙ z))
\\-∙-assoc {x} {y} {z} = proj₁ adjoint (begin
  x ∙ ((x \\ y) ∙ z)   ≈⟨ Eq.sym (assoc x (x \\ y) z) ⟩
  (x ∙ (x \\ y)) ∙ z   ≤⟨ ∙-mono₁ z counit ⟩
  y ∙ z                ∎)

unit-ε : ∀ {x} → ε ≤ (x \\ x)
unit-ε {x} = begin
  ε              ≤⟨ unit ⟩
  x \\ (x ∙ ε)   ≈⟨ \\-cong Eq.refl (identityʳ x) ⟩
  x \\ x         ∎

\\-identityˡ : ∀ {x} → (ε \\ x) ≈ x
\\-identityˡ {x} = antisym
  (begin
    ε \\ x         ≈⟨ Eq.sym (identityˡ (ε \\ x)) ⟩
    ε ∙ (ε \\ x)   ≤⟨ counit ⟩
    x              ∎)
  (proj₁ adjoint (begin
    ε ∙ x          ≈⟨ identityˡ x ⟩
    x   ∎))

------------------------------------------------------------------------------
-- The operations of a residuated pomonoid form a Galois connection

isGaloisConnection : ∀ z → IsGaloisConnection _≈_ _≈_ _≤_ _≤_ (z ∙_) (z \\_)
isGaloisConnection z = record
  { ≤₁-isPartialOrder = isPartialOrder
  ; ≤₂-isPartialOrder = isPartialOrder
  ; left-mono         = ∙-mono₂ z
  ; right-mono        = \\-mono₂ z
  ; adjoint           = adjoint
  }

galoisConnection : ∀ z → GaloisConnection a a ℓ₁ ℓ₁ ℓ₂ ℓ₂
galoisConnection z = record { isGaloisConnection = isGaloisConnection z }

------------------------------------------------------------------------------
-- If the underlying monoid is commutative, _\\_ is also a left residual

module _ (∙-comm : Commutative _≈_ _∙_) where

  ∙-comm-\\-left-residual : ∀ {z} → Adjoint _≤_ _≤_ (_∙ z) (z \\_)
  ∙-comm-\\-left-residual {z} {x} {y} =
    (λ x∙z≤y →
      proj₁ adjoint (begin
        z ∙ x  ≤⟨ reflexive (∙-comm z x) ⟩
        x ∙ z  ≤⟨ x∙z≤y ⟩
        y      ∎)) ,
    (λ x≤z\\y →
      begin
        x ∙ z  ≤⟨ reflexive (∙-comm x z) ⟩
        z ∙ x  ≤⟨ proj₂ adjoint x≤z\\y ⟩
        y      ∎)

  ∙-comm-isLeftResiduatedPomonoid :
    IsRightResiduatedPomonoid _≈_ _≤_ (flip _∙_) _\\_ ε
  ∙-comm-isLeftResiduatedPomonoid = record
    { isPartialOrder = isPartialOrder
    ; ∙-mono₁        = ∙-mono₂
    ; assoc          = FlipOp.associative _≈_ _∙_ Eq.sym assoc
    ; identity       = FlipOp.identity _≈_ _∙_ identity
    ; adjoint        = ∙-comm-\\-left-residual
    }
