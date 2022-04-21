------------------------------------------------------------------------
-- The Agda standard library
--
-- Galois connections
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.GaloisConnection where

open import Data.Product using (proj₁; proj₂; _,_)
open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)
open import Relation.Binary.Bundles using (Poset)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)


------------------------------------------------------------------------
-- Galois connections

record IsGaloisConnection {a b ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂} {A : Set a} {B : Set b}
                          (≈₁ : Rel A ℓ₁₁) (≈₂ : Rel B ℓ₁₂)
                          (≤₁ : Rel A ℓ₂₁) (≤₂ : Rel B ℓ₂₂)
                          (f : A → B) (g : B → A)
                          : Set (a ⊔ b ⊔ ℓ₁₁ ⊔ ℓ₁₂ ⊔ ℓ₂₁ ⊔ ℓ₂₂) where
  field
    ≤₁-isPartialOrder : IsPartialOrder ≈₁ ≤₁
    ≤₂-isPartialOrder : IsPartialOrder ≈₂ ≤₂
    left-mono         : Monotonic₁ ≤₁ ≤₂ f
    right-mono        : Monotonic₁ ≤₂ ≤₁ g
    adjoint           : Adjoint ≤₁ ≤₂ f g

  open IsPartialOrder ≤₁-isPartialOrder public using () renaming
    ( isEquivalence to ≈₁-isEquivalence
    ; isPreorder    to ≤₁-isPreorder
    ; reflexive     to ≤₁-reflexive
    ; refl          to ≤₁-refl
    ; trans         to ≤₁-trans
    ; antisym       to ≤₁-antisym
    ; ≤-resp-≈      to ≤₁-resp-≈₁
    ; module Eq     to Eq₁
    )

  open IsPartialOrder ≤₂-isPartialOrder public using () renaming
    ( isEquivalence to ≈₂-isEquivalence
    ; isPreorder    to ≤₂-isPreorder
    ; reflexive     to ≤₂-reflexive
    ; refl          to ≤₂-refl
    ; trans         to ≤₂-trans
    ; antisym       to ≤₂-antisym
    ; ≤-resp-≈      to ≤₂-resp-≈₂
    ; module Eq     to Eq₂
    )

  unit : ∀ {x} → ≤₁ x (g (f x))
  unit = proj₁ adjoint ≤₂-refl

  counit : ∀ {x} → ≤₂ (f (g x)) x
  counit = proj₂ adjoint ≤₁-refl

  -- Left adjoints preserve colimits (suprema, minima).

  ⊥-pres : ∀ {⊥₁ ⊥₂} → Minimum ≤₁ ⊥₁ → Minimum ≤₂ ⊥₂ → ≈₂ (f ⊥₁) ⊥₂
  ⊥-pres minimum₁ minimum₂ =
    ≤₂-antisym (proj₂ adjoint (minimum₁ (g _))) (minimum₂ (f _))

  ∨-pres : ∀ {_∨₁_ _∨₂_} → Supremum ≤₁ _∨₁_ → Supremum ≤₂ _∨₂_ →
           ∀ x y → ≈₂ (f (x ∨₁ y)) (f x ∨₂ f y)
  ∨-pres {_∨₁_} {_∨₂_} supremum₁ supremum₂ x y =
    let (x≤x∨y ,    y≤x∨y ,    least₁) = supremum₁ x y
        (fx≤fx∨fy , fy≤fx∨fy , least₂) = supremum₂ (f x) (f y)
    in ≤₂-antisym (proj₂ adjoint (least₁ (g (f x ∨₂ f y))
                    (begin
                      x                ≤⟨ unit ⟩
                      g (f x)          ≤⟨ right-mono fx≤fx∨fy ⟩
                      g (f x ∨₂ f y)   ∎)
                    (begin
                      y                ≤⟨ unit ⟩
                      g (f y)          ≤⟨ right-mono fy≤fx∨fy ⟩
                      g (f x ∨₂ f y)   ∎)))
                  (least₂ (f (x ∨₁ y)) (left-mono x≤x∨y)
                                       (left-mono y≤x∨y))
    where open PosetReasoning (record { isPartialOrder = ≤₁-isPartialOrder })


  -- Right adjoints preserve limits (infima, maxima).

  ⊤-pres : ∀ {⊤₁ ⊤₂} → Maximum ≤₁ ⊤₁ → Maximum ≤₂ ⊤₂ → ≈₁ (g ⊤₂) ⊤₁
  ⊤-pres maximum₁ maximum₂ =
    ≤₁-antisym (maximum₁ (g _)) (proj₁ adjoint (maximum₂ (f _)))

  ∧-pres : ∀ {_∧₁_ _∧₂_} → Infimum ≤₁ _∧₁_ → Infimum ≤₂ _∧₂_ →
           ∀ x y → ≈₁ (g (x ∧₂ y)) (g x ∧₁ g y)
  ∧-pres {_∧₁_} {_∧₂_} infimum₁ infimum₂ x y =
    let (gx∧gy≤gx , gx∧gy≤gy , greatest₁) = infimum₁ (g x) (g y)
        (x∧y≤x ,    x∧y≤y ,    greatest₂) = infimum₂ x y
    in ≤₁-antisym (greatest₁ (g (x ∧₂ y)) (right-mono x∧y≤x)
                                          (right-mono x∧y≤y))
                  (proj₁ adjoint (greatest₂ (f (g x ∧₁ g y))
                    (begin
                      f (g x ∧₁ g y)   ≤⟨ left-mono gx∧gy≤gx ⟩
                      f (g x)          ≤⟨ counit ⟩
                      x                ∎)
                    (begin
                      f (g x ∧₁ g y)   ≤⟨ left-mono gx∧gy≤gy ⟩
                      f (g y)          ≤⟨ counit ⟩
                      y                ∎)))
    where open PosetReasoning (record { isPartialOrder = ≤₂-isPartialOrder })

record GaloisConnection a b ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂
                        : Set (suc (a ⊔ b ⊔ ℓ₁₁ ⊔ ℓ₁₂ ⊔ ℓ₂₁ ⊔ ℓ₂₂)) where
  infix  4 _≈₁_ _≈₂_ _≤₁_ _≤₂_
  field
    Carrier₁ : Set a
    Carrier₂ : Set b
    _≈₁_     : Rel Carrier₁ ℓ₁₁
    _≈₂_     : Rel Carrier₂ ℓ₁₂
    _≤₁_     : Rel Carrier₁ ℓ₂₁
    _≤₂_     : Rel Carrier₂ ℓ₂₂
    left     : Carrier₁ → Carrier₂
    right    : Carrier₂ → Carrier₁
    isGaloisConnection : IsGaloisConnection _≈₁_ _≈₂_ _≤₁_ _≤₂_ left right

  open IsGaloisConnection isGaloisConnection public

  ≤₁-poset : Poset a ℓ₁₁ ℓ₂₁
  ≤₁-poset = record { isPartialOrder = ≤₁-isPartialOrder }

  open Poset ≤₁-poset public using () renaming (preorder to ≤₁-preorder)

  ≤₂-poset : Poset b ℓ₁₂ ℓ₂₂
  ≤₂-poset = record { isPartialOrder = ≤₂-isPartialOrder }

  open Poset ≤₂-poset public using () renaming (preorder to ≤₂-preorder)
