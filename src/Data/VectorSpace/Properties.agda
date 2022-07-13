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
  {ring      : CommutativeRing r ℓr}
  {mod       : Module ring m ℓm}
  (vs        : VectorSpace mod)
  where

open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
import      Algebra.Module.Morphism.Properties     as MorphismProperties
open import Axiom.DoubleNegationElimination
open import Data.List
open import Data.Product
open import Function
open import Relation.Binary
import      Relation.Binary.ExtensionalEquivalence as ExtEq
import      Relation.Binary.PropositionalEquality  as Eq
open import Relation.Binary.Reasoning.MultiSetoid

open VectorSpace vs
open ExtEq       setoid

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Some consequences of certain `VectorSpace` property fields.
v∙g[x]+y-cong₂ : {g : V → V} {v x w : V} {y z : S} →
                 Congruent _≈ᴹ_ _≈ᴹ_ g → x ≈ᴹ w → y ≈ z →
                 v ∙ g x + y ≈ v ∙ g w + z
v∙g[x]+y-cong₂ {g} {v} {x} {w} {y} {z} g-cong x≈w y≈z = begin⟨ setoid ⟩
  v ∙ g x + y ≈⟨ +-congʳ (∙-congˡ (g-cong x≈w)) ⟩
  v ∙ g w + y ≈⟨ +-congˡ y≈z ⟩
  v ∙ g w + z ∎

foldr-cong : ∀ {f g : V → S → S} {d e : S} →
             (∀ {y z} → y ≈ z → ∀ x → f x y ≈ g x z) → d ≈ e →
             foldr f d ≗ foldr g e
foldr-cong f≈g d≈e []       = d≈e
foldr-cong f≈g d≈e (x ∷ xs) = f≈g (foldr-cong f≈g d≈e xs) x

-- ToDo: Rewrite in terms of `foldr-homo`, below.
foldr-homo-∙ : {v x₀ : V} {g : V → V} → Congruent _≈ᴹ_ _≈ᴹ_ g →
               (xs : List V) →
               v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs ≈
                 foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) xs
foldr-homo-∙ _ [] = ∙-congˡ (≈ᴹ-reflexive Eq.refl)
foldr-homo-∙ {v} {x₀} {g} g-cong (x ∷ xs) = begin⟨ setoid ⟩
  v ∙ (g x +ᴹ foldr (_+ᴹ_ ∘ g) x₀ xs)        ≈⟨ ∙-distrib-+ ⟩
  v ∙ g x + v ∙ foldr (_+ᴹ_ ∘ g) x₀ xs       ≈⟨ +-congˡ (foldr-homo-∙ g-cong xs) ⟩
  foldr (_+_ ∘ (v ∙_) ∘ g) (v ∙ x₀) (x ∷ xs) ∎

------------------------------------------------------------------------
-- Properties of linear maps from vectors to their underlying scalars.
module _ (lm : LinearMap mod ⟨module⟩) where

  open LinearMap lm
  open MorphismProperties.LinearMapProperties lm

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

  vSum : List V → V
  vSum xs = foldr _+ᴹ_ 0ᴹ xs

  fScale : V → V
  fScale = vscale f

  fGen : List V → V
  fGen = vgen f

  f≈v∙ : ∀ {a} → f a ≈ v lm ∙ a
  f≈v∙ {a} = sym (begin⟨ setoid ⟩
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
    v′ = v lm

  -- Inner product extensional equivalence.
  x·z≈y·z⇒x≈y : ∀ {x y} → DoubleNegationElimination ℓm →
                 Σ[ (s , z) ∈ S × V ]
                   ((s *ₗ (x +ᴹ -ᴹ y) ≈ᴹ z) × (f z ≉ 0#)) →
                 (∀ {z} → x ∙ z ≈ y ∙ z) → x ≈ᴹ y
  x·z≈y·z⇒x≈y {x} {y} dne Σ[z]fz≉𝟘 x∙z≈y∙z = fx≈fy⇒x≈y {dne} Σ[z]fz≉𝟘 fx≈fy
    where
    v′ = v lm
    fx≈fy : f x ≈ f y
    fx≈fy = begin⟨ setoid ⟩
      f x   ≈⟨ f≈v∙ {x} ⟩
      v′ ∙ x ≈⟨ ∙-comm ⟩
      x ∙ v′ ≈⟨ x∙z≈y∙z ⟩
      y ∙ v′ ≈⟨ ∙-comm ⟩
      v′ ∙ y ≈⟨ sym (f≈v∙ {y}) ⟩
      f y   ∎

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

vgen-cong : ∀ {f₁ f₂} → ∀ xs → f₁ ≗ f₂ → vgen f₁ xs ≈ᴹ vgen f₂ xs
vgen-cong {f₁} {f₂} []       f₁≗f₂ = Setoid.reflexive ≈ᴹ-setoid Eq.refl
vgen-cong {f₁} {f₂} (x ∷ xs) f₁≗f₂ = begin⟨ ≈ᴹ-setoid ⟩
  f₁ x *ₗ x +ᴹ vgen f₁ xs ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (f₁≗f₂ x)) ⟩
  f₂ x *ₗ x +ᴹ vgen f₁ xs ≈⟨ +ᴹ-congˡ (vgen-cong xs f₁≗f₂) ⟩
  f₂ x *ₗ x +ᴹ vgen f₂ xs ∎

-- Isomorphism 1: (V ⊸ S) ↔ V
V⊸S↔V : Inverse (≈ᴸ-setoid mod ⟨module⟩) ≈ᴹ-setoid
V⊸S↔V = record
  { to        = v
  ; from      = λ u  → mkLM (u ∙_) u∙-homo
  ; to-cong   = vgen-cong basisSet
  ; from-cong = λ z x → ∙-congʳ z
  ; inverse   = (λ v → begin⟨ ≈ᴹ-setoid ⟩
                     vgen (v ∙_) basisSet
                       ≈⟨ Setoid.sym ≈ᴹ-setoid basisComplete ⟩
                     v ∎ )
                , λ lm x → begin⟨ setoid ⟩
                      v lm ∙ x ≈⟨ sym (f≈v∙ lm) ⟩
                      LinearMap.f lm x   ∎
  }
