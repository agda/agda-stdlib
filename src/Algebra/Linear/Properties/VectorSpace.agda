------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
  using (CommutativeRing; Congruent₁; Congruent₂; Op₁; Op₂)
open import Algebra.Module        using (Module)
open import Algebra.Linear.Bundles
open import Level                 using (Level; _⊔_; suc)

module Algebra.Linear.Properties.VectorSpace
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  {mod       : Module ring m ℓm}
  {vs        : VectorSpace mod}
  (basis     : Basis vs)
  where

open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
import      Algebra.Module.Morphism.ModuleHomomorphism as ModHomo
import      Algebra.Module.Morphism.Structures as MorphismStructures
open import Axiom.DoubleNegationElimination
open import Data.List
open import Data.Product
open import Function
open import Relation.Binary
import      Relation.Binary.PropositionalEquality      as Eq
open import Relation.Binary.Reasoning.MultiSetoid

open Basis basis
open MorphismStructures.ModuleMorphisms mod ⟨module⟩

import Function.Relation.Binary.Equality as ExtEq
open ExtEq setoid
-- import Function.Relation.Binary.Equality2 as ExtEq
-- open ExtEq ≈ᴹ-setoid setoid

------------------------------------------------------------------------
-- Scale a vector according to some reduction function.
vscale : (V → S) → V → V
vscale f = uncurry _*ₗ_ ∘ < f , id >

-- Accumulate a list of vectors, according to some reduction function.
vgen : (V → S) → List V → V
vgen f = foldr (_+ᴹ_ ∘ vscale f) 0ᴹ

-- Congruency of `IsBasisOver` helper functions.
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
foldr-cong : ∀ {f g : V → S → S} {d e : S} →
             (∀ {y z} → y ≈ z → ∀ x → f x y ≈ g x z) → d ≈ e →
             foldr f d ≗ foldr g e
foldr-cong f≈g d≈e []       = d≈e
foldr-cong f≈g d≈e (x ∷ xs) = f≈g (foldr-cong f≈g d≈e xs) x

v∙g[x]+y-cong₂ : {g : V → V} → Congruent _≈ᴹ_ _≈ᴹ_ g →
                 {v x w : V} {y z : S} → x ≈ᴹ w → y ≈ z →
                 v ∙ g x + y ≈ v ∙ g w + z
v∙g[x]+y-cong₂ {g} g-cong {v} {x} {w} {y} {z} x≈w y≈z = begin⟨ setoid ⟩
  v ∙ g x + y ≈⟨ +-congʳ (∙-congˡ (g-cong x≈w)) ⟩
  v ∙ g w + y ≈⟨ +-congˡ y≈z ⟩
  v ∙ g w + z ∎

-- sum ∘ map?
foldr-homo-∙ : {g : V → V} → Congruent _≈ᴹ_ _≈ᴹ_ g →
               {v x₀ : V} (xs : List V) →
               v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs ≈
                 foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) xs
foldr-homo-∙ _ [] = ∙-congˡ (≈ᴹ-reflexive Eq.refl)
foldr-homo-∙ {g} g-cong {v} {x₀} (x ∷ xs) = begin⟨ setoid ⟩
  v ∙ (g x +ᴹ foldr (_+ᴹ_ ∘ g) x₀ xs)        ≈⟨ ∙-distrib-+ ⟩
  v ∙ g x + v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs       ≈⟨ +-congˡ (foldr-homo-∙ g-cong xs) ⟩
  foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) (x ∷ xs) ∎

u∙-homo : ∀ {u} → IsModuleHomomorphism (u ∙_)
u∙-homo = record
  { isBimoduleHomomorphism = record
      { +ᴹ-isGroupHomomorphism = record
          { isMonoidHomomorphism = record
              { isMagmaHomomorphism = record
                  { isRelHomomorphism = record
                      { cong = ∙-congˡ
                      }
                  ; homo = λ x y → ∙-distrib-+
                  }
              ; ε-homo = ∙-idʳ
              }
          ; ⁻¹-homo = λ x → ∙-homo-⁻¹
          }
      ; *ₗ-homo = λ r x → ∙-comm-*ₗ
      ; *ᵣ-homo = λ r x → ∙-comm-*ᵣ
      }
  }

------------------------------------------------------------------------
-- Properties of linear maps from vectors to their underlying scalars.
--
-- Note: `f` in the code below refers to the linear function.
--
-- ToDo: `List` ==> `Foldable Functor`
module _ (lm : LinearMap mod ⟨module⟩) where

  open LinearMap lm
  open ModHomo   mod ⟨module⟩ (LinearMap.homo lm)

  -- Proof that the linear function in a `LinearMap` must be homomorphic
  -- over sums of products.
  vred : (V → S) → List V → S
  vred g = foldr (_+_ ∘ uncurry _*_ ∘ < g , f >) 0#

  foldr-homo : (g : V → S) → (xs : List V) → f (vgen g xs) ≈ vred g xs
  foldr-homo g []       = 0ᴹ-homo
  foldr-homo g (x ∷ xs) = begin⟨ setoid ⟩
    f (h x (foldr h 0ᴹ xs))
      ≈⟨ +ᴹ-homo (g x *ₗ x) (foldr h 0ᴹ xs) ⟩
    f (g x *ₗ x) + f (foldr h 0ᴹ xs)
      ≈⟨ +-congʳ (*ₗ-homo (g x) x) ⟩
    g x * f x + f (foldr h 0ᴹ xs)
      ≈⟨ +-congˡ (foldr-homo g xs) ⟩
    g x * f x + vred g xs
      ∎
    where
    h = _+ᴹ_ ∘ vscale g

  -- Proof that the linear function inside a `LinearMap` is always
  -- equivalent to taking the inner product with some vector.
  f[u]⇔v∙[u] : ∀ {a} → f a ≈ lmToVec lm ∙ a
  f[u]⇔v∙[u] {a} = sym (begin⟨ setoid ⟩
    v′ ∙ a ≈⟨ ∙-comm ⟩
    a ∙ v′ ≈⟨ foldr-homo-∙ (vscale-cong f ⟦⟧-cong) basisSet ⟩
    foldr (_+_ ∘ (a ∙_) ∘ fScale) (a ∙ 0ᴹ) basisSet
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
    f a ∎)
    where
    v′ = lmToVec lm
    fScale : V → V
    fScale = vscale f

  -- Inner product extensional equivalence.
  x·z≈y·z⇒x≈y : DoubleNegationElimination ℓm → ∀ {x y} →
                ∃₂ (λ s z → ((s *ₗ (x +ᴹ -ᴹ y) ≈ᴹ z) × (f z ≉ 0#))) →
                (∀ {z} → x ∙ z ≈ y ∙ z) → x ≈ᴹ y
  x·z≈y·z⇒x≈y dne {x} {y} Σ[z]fz≉𝟘 x∙z≈y∙z = fx≈fy⇒x≈y {dne} Σ[z]fz≉𝟘 fx≈fy
    where
    v′ = lmToVec lm
    fx≈fy : f x ≈ f y
    fx≈fy = begin⟨ setoid ⟩
      f x   ≈⟨ f[u]⇔v∙[u] {x} ⟩
      v′ ∙ x ≈⟨ ∙-comm ⟩
      x ∙ v′ ≈⟨ x∙z≈y∙z ⟩
      y ∙ v′ ≈⟨ ∙-comm ⟩
      v′ ∙ y ≈⟨ sym (f[u]⇔v∙[u] {y}) ⟩
      f y   ∎

-- Isomorphism 1: (V ⊸ S) ↔ V
--
-- A linear map from a vector to its underlying scalar field is
-- isomorphic to a lone vector.
V⊸S↔V : Inverse (≈ᴸ-setoid mod ⟨module⟩) ≈ᴹ-setoid
V⊸S↔V = record
  { to        = lmToVec
  ; from      = λ u  → mkLM (u ∙_) u∙-homo
  ; to-cong   = vgen-cong basisSet
  ; from-cong = λ z x → ∙-congʳ z
  ; inverse   = fwd , rev
  }
  where
  fwd : Inverseˡ _≈ᴸ_ _≈ᴹ_ lmToVec (λ u → mkLM (u ∙_) u∙-homo)
  fwd v = begin⟨ ≈ᴹ-setoid ⟩
    vgen (v ∙_) basisSet ≈⟨ Setoid.sym ≈ᴹ-setoid basisComplete ⟩
    v                    ∎
  rev : Inverseʳ _≈ᴸ_ _≈ᴹ_ lmToVec (λ u → mkLM (u ∙_) u∙-homo)
  rev lm x = begin⟨ setoid ⟩
    lmToVec lm ∙ x           ≈⟨ sym (f[u]⇔v∙[u] lm) ⟩
    LinearMap.f lm x   ∎
