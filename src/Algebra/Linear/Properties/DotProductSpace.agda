------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of dot product spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Linear.Bundles using (DotProductSpace)
open import Level                  using (Level; _⊔_; suc)

module Algebra.Linear.Properties.DotProductSpace
  {r ℓr m ℓm    : Level}
  (dotProdSpace : DotProductSpace r ℓr m ℓm)
  where

open import Algebra using (CommutativeRing; Field)
open import Algebra.Module                             using (Module)
open import Algebra.Module.Construct.TensorUnit        using (⟨module⟩)
import      Algebra.Module.Morphism.Structures         as MorphismStructures
open import Data.List
import      Data.List.Relation.Binary.Equality.Setoid  as ListEq
open import Function
import      Function.Relation.Binary.Equality          as ExtEq
open import Relation.Binary
import      Relation.Binary.PropositionalEquality      as Eq
open import Relation.Binary.Reasoning.MultiSetoid

open DotProductSpace dotProdSpace
open CommutativeRing (Field.ring fld)
  renaming (Carrier to S)
open Module mod
  renaming (Carrierᴹ to V)
open MorphismStructures.ModuleMorphisms mod ⟨module⟩
open ExtEq  setoid

------------------------------------------------------------------------
-- Congruence of helper functions in `Algebra.Linear.Structures`.
vscale-cong : ∀ f → Congruent _≈ᴹ_ _≈_ f → Congruent _≈ᴹ_ _≈ᴹ_ (vscale f)
vscale-cong f f-cong {x} {y} x≈y = begin⟨ ≈ᴹ-setoid ⟩
  vscale f x ≡⟨⟩
  f x *ₗ x   ≈⟨ *ₗ-congʳ (f-cong x≈y) ⟩
  f y *ₗ x   ≈⟨ *ₗ-congˡ x≈y ⟩
  f y *ₗ y   ≡⟨⟩
  vscale f y ∎

vgen-cong : ∀ {f₁ f₂} → ∀ xs → f₁ ≗ f₂ → vgen f₁ xs ≈ᴹ vgen f₂ xs
vgen-cong {f₁} {f₂} []       f₁≗f₂ = Setoid.reflexive ≈ᴹ-setoid Eq.refl
vgen-cong {f₁} {f₂} (x ∷ xs) f₁≗f₂ = begin⟨ ≈ᴹ-setoid ⟩
  f₁ x *ₗ x +ᴹ vgen f₁ xs ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (f₁≗f₂ x)) ⟩
  f₂ x *ₗ x +ᴹ vgen f₁ xs ≈⟨ +ᴹ-congˡ (vgen-cong xs f₁≗f₂) ⟩
  f₂ x *ₗ x +ᴹ vgen f₂ xs ∎

------------------------------------------------------------------------
-- Some consequences of `VectorSpace` inner product properties.
v∙g[x]+y-cong₂ : {g : V → V} → Congruent _≈ᴹ_ _≈ᴹ_ g →
                 {v x w : V} {y z : S} → x ≈ᴹ w → y ≈ z →
                 v ∙ g x + y ≈ v ∙ g w + z
v∙g[x]+y-cong₂ {g} g-cong {v} {x} {w} {y} {z} x≈w y≈z = begin⟨ setoid ⟩
  v ∙ g x + y ≈⟨ +-congʳ (∙-congˡ (g-cong x≈w)) ⟩
  v ∙ g w + y ≈⟨ +-congˡ y≈z ⟩
  v ∙ g w + z ∎

foldr-homo-∙ : {g : V → V} → Congruent _≈ᴹ_ _≈ᴹ_ g →
               {v x₀ : V} (xs : List V) →
               v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs ≈
                 foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) xs
foldr-homo-∙ _ [] = ∙-congˡ (≈ᴹ-reflexive Eq.refl)
foldr-homo-∙ {g} g-cong {v} {x₀} (x ∷ xs) = begin⟨ setoid ⟩
  v ∙ (g x +ᴹ foldr (_+ᴹ_ ∘ g) x₀ xs)
    ≈⟨ ∙-distrib-+ len[u]≡len[v] len[u]≡len[v] ⟩
  v ∙ g x + v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs
    ≈⟨ +-congˡ (foldr-homo-∙ g-cong xs) ⟩
  foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) (x ∷ xs)
    ∎

u∙-homo : ∀ {u} → IsModuleHomomorphism (u ∙_)
u∙-homo = record
  { isBimoduleHomomorphism = record
      { +ᴹ-isGroupHomomorphism = record
          { isMonoidHomomorphism = record
              { isMagmaHomomorphism = record
                  { isRelHomomorphism = record
                      { cong = ∙-congˡ
                      }
                  ; homo = λ x y → ∙-distrib-+ len[u]≡len[v] len[u]≡len[v]
                  }
              ; ε-homo = ∙-idʳ
              }
          ; ⁻¹-homo = λ x → ∙-homo-⁻¹
          }
      ; *ₗ-homo = λ r x → ∙-comm-*ₗ
      ; *ᵣ-homo = λ r x → ∙-comm-*ᵣ
      }
  }
