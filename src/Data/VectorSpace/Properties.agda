------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
  using (CommutativeRing; Congruent₁; Congruent₂; Op₁; Op₂)
open import Algebra.Module        using (Module)
open import Data.VectorSpace.Core
open import Level                 using (Level; _⊔_; suc)

module Data.VectorSpace.Properties
  {r ℓr m ℓm : Level}
  {ring : CommutativeRing r ℓr}
  {mod  : Module ring m ℓm}
  (vs   : VectorSpace mod)
  where

import Algebra.Module.Morphism.Structures    as MorphismStructures
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid      as Reasoning

open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Linear.Properties mod ⟨module⟩
open import Data.List
open import Data.Product                        hiding (map)
open import Function
open import Function.Equivalence                using (⇔-setoid)
open import Relation.Binary                     hiding (_⇔_)
open import Relation.Binary.Reasoning.MultiSetoid

open CommutativeRing ring
  using ( _+_; _*_; _≈_; setoid; sym; 0#; +-congˡ; +-congʳ; +-cong
        ; +-comm; reflexive; *-comm)
  renaming (Carrier to S)
open Module mod renaming (Carrierᴹ to T)
open MorphismStructures.ModuleMorphisms mod ⟨module⟩
open VectorSpace vs

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Pointwise equality for equivalence.
-- (Copied from `Relation.Binary.PropositionalEquality` and modified.)
infix 4 _≗_

_≗_ : (f g : A → S) → Set _
f ≗ g = ∀ x → f x ≈ g x

------------------------------------------------------------------------
-- Some consequences of certain `VectorSpace` property fields.
v∙g[x]+y-cong₂ : {g : T → T} {v x w : T} {y z : S} →
                 Congruent _≈ᴹ_ _≈ᴹ_ g → x ≈ᴹ w → y ≈ z →
                 v ∙ g x + y ≈ v ∙ g w + z
v∙g[x]+y-cong₂ {g} {v} {x} {w} {y} {z} g-cong x≈w y≈z = begin⟨ setoid ⟩
  v ∙ g x + y ≈⟨ +-congʳ (∙-congˡ (g-cong x≈w)) ⟩
  v ∙ g w + y ≈⟨ +-congˡ y≈z ⟩
  v ∙ g w + z ∎

foldr-cong : ∀ {f g : T → S → S} {d e : S} →
             (∀ {y z} → y ≈ z → ∀ x → f x y ≈ g x z) → d ≈ e →
             foldr f d ≗ foldr g e
foldr-cong f≈g d≈e []       = d≈e
foldr-cong f≈g d≈e (x ∷ xs) = f≈g (foldr-cong f≈g d≈e xs) x

-- ToDo: Rewrite in terms of `foldr-homo`, below.
foldr-homo-∙ : {v x₀ : T} {g : T → T} → Congruent _≈ᴹ_ _≈ᴹ_ g →
               (xs : List T) →
               v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs ≈
                 foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) xs
foldr-homo-∙ _ [] = ∙-congˡ (≈ᴹ-reflexive Eq.refl)
foldr-homo-∙ {v} {x₀} {g} g-cong (x ∷ xs) = begin⟨ setoid ⟩
  v ∙ (g x +ᴹ foldr (_+ᴹ_ ∘ g) x₀ xs)        ≈⟨ ∙-distrib-+ ⟩
  v ∙ g x + v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs       ≈⟨ +-congˡ (foldr-homo-∙ g-cong xs) ⟩
  foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) (x ∷ xs) ∎

-- Properties predicated upon a linear map from tensor to scalar.
module _
  {f : T → S}
  (isModuleHomomorphism : IsModuleHomomorphism f)
  where

  open IsModuleHomomorphism isModuleHomomorphism

  foldr-homo : (g : T → S) → (xs : List T) →
               f (foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < g , id >) 0ᴹ xs) ≈
                 foldr (_+_ ∘ (uncurry _*_) ∘ < g , f >) 0# xs
  foldr-homo g []       = f0≈0 isModuleHomomorphism
  foldr-homo g (x ∷ xs) = begin⟨ setoid ⟩
    f (h x (foldr h 0ᴹ xs))
      ≈⟨ +ᴹ-homo (g x *ₗ x) (foldr h 0ᴹ xs) ⟩
    f (g x *ₗ x) + f (foldr h 0ᴹ xs)
      ≈⟨ +-congʳ (*ₗ-homo (g x) x) ⟩
    g x * f x + f (foldr h 0ᴹ xs)
      ≈⟨ +-congˡ (foldr-homo g xs) ⟩
    g x * f x + (foldr (_+_ ∘ uncurry _*_ ∘ < g , f >) 0# xs)
      ∎
    where
    h = _+ᴹ_ ∘ uncurry _*ₗ_ ∘ < g , id >

  -- Any linear map from T to S is equivalent to an inner product with
  -- some vector, v.
  T⊸S≈v∙ : ∀ {a} → ∃[ v ] f a ≈ v ∙ a
  T⊸S≈v∙ {a} =
    ( v
    , sym (begin⟨ setoid ⟩
        v ∙ a ≈⟨ ∙-comm ⟩
        a ∙ v ≈⟨ foldr-homo-∙ g-cong basisSet ⟩
        foldr (_+_ ∘ (a ∙_) ∘ g) (a ∙ 0ᴹ) basisSet
          ≈⟨ foldr-cong (λ {y≈z _ → +-congˡ y≈z}) ∙-idʳ basisSet ⟩
        foldr (_+_ ∘ (a ∙_) ∘ (uncurry _*ₗ_) ∘ < f , id >) 0# basisSet
          ≈⟨ foldr-cong (λ y≈z _ → +-cong ∙-comm-*ₗ y≈z)
                        (reflexive Eq.refl) basisSet ⟩
        foldr (_+_ ∘ (uncurry _*_) ∘ < f , (a ∙_) >) 0# basisSet
          ≈⟨ foldr-cong (λ y≈z x → +-cong (*-comm (f x) (a ∙ x)) y≈z)
                        (reflexive Eq.refl) basisSet ⟩
        foldr (_+_ ∘ (uncurry _*_) ∘ < (a ∙_) , f >) 0# basisSet
          ≈⟨ sym (foldr-homo (a ∙_) basisSet) ⟩
        f (foldr (_+ᴹ_ ∘ (uncurry _*ₗ_) ∘ < (a ∙_) , id >) 0ᴹ basisSet)
          ≈⟨ ⟦⟧-cong (Setoid.sym ≈ᴹ-setoid (basisComplete)) ⟩
        f a
          ∎)
    )
    where
    g : Op₁ T
    g = uncurry _*ₗ_ ∘ < f , id >
    v = foldr (_+ᴹ_ ∘ g) 0ᴹ basisSet
    g-cong : Congruent _≈ᴹ_ _≈ᴹ_ g
    g-cong {x} {y} x≈y = begin⟨ ≈ᴹ-setoid ⟩
      g x ≡⟨⟩
      f x *ₗ x ≈⟨ *ₗ-congʳ (⟦⟧-cong x≈y) ⟩
      f y *ₗ x ≈⟨ *ₗ-congˡ x≈y ⟩
      f y *ₗ y ≡⟨⟩
      g y ∎

  -- ToDo: Is this next proof to solve, or uneeded scrap?
  -- x·z≈y·z→x≈y : {x y : T} → Σ[ y ∈ T ] f y ≉ 0# →
  --   (∀ {z : T} → x ∙ z ≈ y ∙ z) → x ≈ᵀ y
  -- x·z≈y·z→x≈y {x = x} {y = y} Σ[y]fy≉𝟘 x∙z≈y∙z =
  --   let z = foldl (λ acc v → acc T.+ᴹ f v *ₗ v) T.0ᴹ basisSet
  --       -- x·z≈y·z = x∙z≈y∙z {z}
  --       z·x≈y·z : z ∙ x ≈ y ∙ z
  --       -- z·x≈y·z = step-≈ (z ∙ x) x·z≈y·z comm-∙
  --       -- z·x≈y·z = step-≈ (z ∙ x) x∙z≈y∙z {z} comm-∙
  --       z·x≈y·z = begin (z ∙ x) ≈⟨ comm-∙ ⟩ x∙z≈y∙z {z} ∎
  --       z·x≈z·y : z ∙ x ≈ z ∙ y
  --       z·x≈z·y = sym (step-≈ (z ∙ y) (sym z·x≈y·z) comm-∙)
  --       fx≈z·y : f x ≈ z ∙ y
  --       fx≈z·y = step-≈ (f x) z·x≈z·y (sym orthonormal)
  --       fx≈fy : f x ≈ f y
  --       fx≈fy = sym (step-≈ (f y) (sym fx≈z·y) (sym orthonormal))
  --    in inj-lm Σ[y]fy≉𝟘 fx≈fy
