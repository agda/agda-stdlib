------------------------------------------------------------------------
-- The Agda standard library
--
-- The non-commutative analogue of Nagata's construction of
-- the "idealization of a module", (Local Rings, 1962; Wiley)
-- defined here on R-R-*bi*modules M over a ring R, as used in
-- "Forward- or reverse-mode automatic differentiation: What's the difference?"
-- (Van den Berg, Schrijvers, McKinna, Vandenbroucke;
-- Science of Computer Programming, Vol. 234, January 2024
-- https://doi.org/10.1016/j.scico.2023.103010)
--
-- The construction N =def R ⋉ M , for which there is unfortunately
-- no consistent notation in the literature, consists of:
-- * carrier: pairs |R| × |M|
-- * with additive structure that of the direct sum R ⊕ M _of modules_
-- * but with multiplication _*ᴺ_ such that M forms an _ideal_ of N
-- * moreover satisfying 'm *ᴺ m ≈ 0' for every m ∈ M ⊆ N
--
-- The fundamental lemma (proved here) is that N, in fact, defines a Ring.
--
-- Nagata's more fundamental insight (not yet shown here) is that
-- the lattice of R-submodules of M is in order-isomorphism with
-- the lattice of _ideals_ of R ⋉ M , and hence that the study of
-- modules can be reduced to that of ideals of a ring, and vice versa.
--
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Construct.Nagata where

open import Algebra.Bundles using (AbelianGroup; Ring)
open import Algebra.Core
import Algebra.Consequences.Setoid as Consequences
import Algebra.Definitions as Definitions
open import Algebra.Module.Bundles using (Bimodule)
import Algebra.Module.Construct.DirectProduct as DirectProduct
import Algebra.Module.Construct.TensorUnit as TensorUnit
open import Algebra.Structures using (IsAbelianGroup; IsRing)
open import Data.Product using (_,_; ∃-syntax)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    m ℓm r ℓr : Level

------------------------------------------------------------------------
-- Definitions

module Nagata (ring : Ring r ℓr) (bimodule : Bimodule ring ring m ℓm) where

  open Ring ring
    renaming (Carrier to R
             ; 0# to 0ᴿ
             ; 1# to 1ᴿ
             ; _+_ to _+ᴿ_
             ; _*_ to _*ᴿ_
             ; *-cong to *ᴿ-cong
             ; *-assoc to *ᴿ-assoc
             ; *-identityʳ to *ᴿ-identityʳ
             ; *-identityˡ to *ᴿ-identityˡ
             ; distribˡ to *ᴿ-distribˡ-+ᴿ
             ; distribʳ to *ᴿ-distribʳ-+ᴿ
             )
    --hiding (zero; zeroˡ; zeroʳ)

  open Bimodule bimodule
    renaming (Carrierᴹ to M
             )

  open AbelianGroup +ᴹ-abelianGroup
    renaming (setoid to setoidᴹ
             ; isEquivalence to isEquivalenceᴹ
             )

  open IsEquivalence isEquivalenceᴹ
    renaming (sym to symᴹ)

  +ᴺ-bimodule = DirectProduct.bimodule TensorUnit.bimodule bimodule

  open Bimodule +ᴺ-bimodule public using ()
    renaming (Carrierᴹ to N
             ; _≈ᴹ_ to _≈ᴺ_
             ; _+ᴹ_ to _+ᴺ_
             ; 0ᴹ to 0ᴺ
             ; -ᴹ_ to -ᴺ_
             ; +ᴹ-abelianGroup to +ᴺ-abelianGroup
             )

  open AbelianGroup +ᴺ-abelianGroup
    renaming (isAbelianGroup to +ᴺ-isAbelianGroup)

  open Definitions _≈ᴺ_

-- injections ι from the components of the direct sum
-- ιᴹ in fact exhibits M as an _ideal_ of R ⋉ M (not yet shown)
  ιᴿ : R → N
  ιᴿ r = r , 0ᴹ

  ιᴹ : M → N
  ιᴹ m = 0ᴿ , m

-- multiplicative unit

  1ᴺ : N
  1ᴺ = ιᴿ 1ᴿ

-- multiplication

  infixl 7 _*ᴺ_

  _*ᴺ_ : Op₂ N
  (r₁ , m₁) *ᴺ (r₂ , m₂) = r₁ *ᴿ r₂ , r₁ *ₗ m₂ +ᴹ m₁ *ᵣ r₂

-- properties: because we work in the direct sum, every proof
-- has an 'R'-component, which inherits directly from R,
-- and an 'M'-component, where the work happens

  open ≈-Reasoning setoidᴹ

  private
    +ᴹ-middleFour = Consequences.comm∧assoc⇒middleFour setoidᴹ +ᴹ-cong +ᴹ-comm +ᴹ-assoc

  *ᴺ-identity : Identity 1ᴺ _*ᴺ_
  *ᴺ-identity = lᴺ , rᴺ
    where
      lᴺ : LeftIdentity 1ᴺ _*ᴺ_
      lᴺ (r , m) = *ᴿ-identityˡ r , (begin
        1ᴿ *ₗ m +ᴹ 0ᴹ *ᵣ r ≈⟨ +ᴹ-cong (*ₗ-identityˡ m) (*ᵣ-zeroˡ r) ⟩
        m +ᴹ 0ᴹ            ≈⟨ +ᴹ-identityʳ m ⟩
        m                  ∎)
      rᴺ : RightIdentity 1ᴺ _*ᴺ_
      rᴺ (r , m) = (*ᴿ-identityʳ r) , (begin
        r *ₗ 0ᴹ +ᴹ m *ᵣ 1ᴿ ≈⟨ +ᴹ-cong (*ₗ-zeroʳ r) (*ᵣ-identityʳ m) ⟩
        0ᴹ +ᴹ m            ≈⟨ +ᴹ-identityˡ m ⟩
        m                  ∎)

  *ᴺ-cong : Congruent₂ _*ᴺ_
  *ᴺ-cong (r₁ , m₁) (r₂ , m₂) = *ᴿ-cong r₁ r₂ , +ᴹ-cong (*ₗ-cong r₁ m₂) (*ᵣ-cong m₁ r₂)

  *ᴺ-assoc : Associative _*ᴺ_
  *ᴺ-assoc (r₁ , m₁) (r₂ , m₂) (r₃ , m₃) = *ᴿ-assoc r₁ r₂ r₃ , (begin
    (r₁ *ᴿ r₂) *ₗ m₃ +ᴹ (r₁ *ₗ m₂ +ᴹ m₁ *ᵣ r₂) *ᵣ r₃
      ≈⟨ +ᴹ-cong (*ₗ-assoc r₁ r₂ m₃) (*ᵣ-distribʳ r₃ (r₁ *ₗ m₂) (m₁ *ᵣ r₂)) ⟩
    r₁ *ₗ (r₂ *ₗ m₃) +ᴹ ((r₁ *ₗ m₂) *ᵣ r₃ +ᴹ (m₁ *ᵣ r₂) *ᵣ r₃)
       ≈⟨ +ᴹ-congˡ (+ᴹ-congʳ (*ₗ-*ᵣ-assoc r₁ m₂ r₃)) ⟩
    r₁ *ₗ (r₂ *ₗ m₃) +ᴹ (r₁ *ₗ (m₂ *ᵣ r₃) +ᴹ (m₁ *ᵣ r₂) *ᵣ r₃)
      ≈⟨ symᴹ (+ᴹ-assoc (r₁ *ₗ (r₂ *ₗ m₃)) (r₁ *ₗ (m₂ *ᵣ r₃)) ((m₁ *ᵣ r₂) *ᵣ r₃)) ⟩
    (r₁ *ₗ (r₂ *ₗ m₃) +ᴹ r₁ *ₗ (m₂ *ᵣ r₃)) +ᴹ (m₁ *ᵣ r₂) *ᵣ r₃
      ≈⟨ +ᴹ-cong (symᴹ (*ₗ-distribˡ r₁ (r₂ *ₗ m₃) (m₂ *ᵣ r₃))) (*ᵣ-assoc m₁ r₂ r₃) ⟩
    r₁ *ₗ (r₂ *ₗ m₃ +ᴹ m₂ *ᵣ r₃) +ᴹ m₁ *ᵣ (r₂ *ᴿ r₃) ∎)

  *ᴺ-distrib-+ᴺ : _*ᴺ_ DistributesOver _+ᴺ_
  *ᴺ-distrib-+ᴺ = lᴺ , rᴺ
    where
      lᴺ : _*ᴺ_ DistributesOverˡ _+ᴺ_
      lᴺ (r₁ , m₁) (r₂ , m₂) (r₃ , m₃) = *ᴿ-distribˡ-+ᴿ r₁ r₂ r₃ , (begin
        r₁ *ₗ (m₂ +ᴹ m₃) +ᴹ m₁ *ᵣ (r₂ +ᴿ r₃)
          ≈⟨ +ᴹ-cong (*ₗ-distribˡ r₁ m₂ m₃) (*ᵣ-distribˡ m₁ r₂ r₃) ⟩
        (r₁ *ₗ m₂ +ᴹ r₁ *ₗ m₃) +ᴹ (m₁ *ᵣ r₂ +ᴹ m₁ *ᵣ r₃)
          ≈⟨ +ᴹ-middleFour (r₁ *ₗ m₂) (r₁ *ₗ m₃) (m₁ *ᵣ r₂) (m₁ *ᵣ r₃) ⟩
        (r₁ *ₗ m₂ +ᴹ m₁ *ᵣ r₂) +ᴹ (r₁ *ₗ m₃ +ᴹ m₁ *ᵣ r₃) ∎)
      rᴺ : _*ᴺ_ DistributesOverʳ _+ᴺ_
      rᴺ (r₁ , m₁) (r₂ , m₂) (r₃ , m₃) = *ᴿ-distribʳ-+ᴿ r₁ r₂ r₃ , (begin
        (r₂ +ᴿ r₃) *ₗ m₁ +ᴹ (m₂ +ᴹ m₃) *ᵣ r₁
          ≈⟨ +ᴹ-cong (*ₗ-distribʳ m₁ r₂ r₃) (*ᵣ-distribʳ r₁ m₂ m₃) ⟩
        (r₂ *ₗ m₁ +ᴹ r₃ *ₗ m₁) +ᴹ (m₂ *ᵣ r₁ +ᴹ m₃ *ᵣ r₁)
          ≈⟨ +ᴹ-middleFour (r₂ *ₗ m₁) (r₃ *ₗ m₁) (m₂ *ᵣ r₁) (m₃ *ᵣ r₁) ⟩
        (r₂ *ₗ m₁ +ᴹ m₂ *ᵣ r₁) +ᴹ (r₃ *ₗ m₁ +ᴹ m₃ *ᵣ r₁) ∎)


------------------------------------------------------------------------
-- The Fundamental Lemma

  isRingᴺ : IsRing _≈ᴺ_ _+ᴺ_ _*ᴺ_ -ᴺ_ 0ᴺ  1ᴺ
  isRingᴺ = record
    { +-isAbelianGroup = +ᴺ-isAbelianGroup
    ; *-cong = *ᴺ-cong
    ; *-assoc = *ᴺ-assoc
    ; *-identity = *ᴺ-identity
    ; distrib = *ᴺ-distrib-+ᴺ
    }

------------------------------------------------------------------------
-- M is an ideal of R ⋉ M satisying m * m ≈ 0

  idealˡ-M : (n : N) (m : M) → ∃[ n*m ] n *ᴺ ιᴹ m ≈ᴺ ιᴹ n*m
  idealˡ-M (r₀ , m₀) m = _ , zeroʳ r₀ , ≈ᴹ-refl

  idealʳ-M : (n : N) (m : M) → ∃[ m*n ] ιᴹ m *ᴺ n ≈ᴺ ιᴹ m*n
  idealʳ-M (r₀ , m₀) m = _ , zeroˡ r₀ , ≈ᴹ-refl

  m*m≈0 : (m : M) → ιᴹ m *ᴺ ιᴹ m ≈ᴺ 0ᴺ
  m*m≈0 m = zeroˡ 0ᴿ , (begin
    0ᴿ *ₗ m +ᴹ m *ᵣ 0ᴿ ≈⟨ +ᴹ-cong (*ₗ-zeroˡ m) (*ᵣ-zeroʳ m) ⟩
    0ᴹ +ᴹ 0ᴹ           ≈⟨ +ᴹ-identityˡ 0ᴹ ⟩
    0ᴹ                 ∎)
  
------------------------------------------------------------------------
-- Bundle

infixl 4 _⋉_

_⋉_ : (R : Ring r ℓr) (M : Bimodule R R m ℓm) → Ring (r ⊔ m) (ℓr ⊔ ℓm)

R ⋉ M = record { isRing = isRingᴺ } where open Nagata R M

