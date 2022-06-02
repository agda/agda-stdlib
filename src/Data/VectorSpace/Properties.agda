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
open import Axiom.DoubleNegationElimination
open import Data.List
open import Data.Product                        hiding (map)
open import Function
open import Function.Equivalence                using (⇔-setoid)
open import Relation.Binary                     hiding (_⇔_)
open import Relation.Binary.Reasoning.MultiSetoid

open VectorSpace vs

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

-- Proofs predicated upon a `VectorSpace.LinMap` instance.
module _ (lm : LinMap) where

  open LinMap lm
  
  foldr-homo : (g : V → S) → (xs : List V) →
               f (foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < g , id >) 0ᴹ xs) ≈
                 foldr (_+_ ∘ uncurry _*_ ∘ < g , f >) 0# xs
  foldr-homo g []       = 0ᴹ-homo
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

  vSum : List V → V
  vSum xs = foldr _+ᴹ_ 0ᴹ xs

  fScale : V → V
  fScale = uncurry _*ₗ_ ∘ < f , id >

  fScale-distrib-+ᴹ : ∀ u v → fScale (u +ᴹ v) ≈ᴹ fScale u +ᴹ fScale v
  fScale-distrib-+ᴹ u v = begin⟨ ≈ᴹ-setoid ⟩
    fScale (u +ᴹ v)                      ≡⟨⟩
    f (u +ᴹ v)  *ₗ (u +ᴹ v)              ≈⟨ {!!} ⟩
    (f u + f v) *ₗ (u +ᴹ v)              ≈⟨ {!!} ⟩
    (f u + f v) *ₗ u +ᴹ (f u + f v) *ₗ v ≈⟨ {!!} ⟩
    -- Shoot! I don't think `fScale` actually distributes over `_+ᴹ_`. :(
    f u *ₗ u +ᴹ f v *ₗ v                 ≡⟨⟩
    fScale u +ᴹ fScale v                 ∎
    
  foldr-homo′ : ∀ (xs) →
               foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < f , id >) 0ᴹ xs
               ≈ᴹ f (vSum xs) *ₗ vSum xs
  foldr-homo′ []       = Setoid.sym ≈ᴹ-setoid (begin⟨ ≈ᴹ-setoid ⟩
    f (vSum []) *ₗ vSum [] ≡⟨⟩
    f 0ᴹ *ₗ 0ᴹ             ≈⟨ *ₗ-congʳ 0ᴹ-homo ⟩
    0#   *ₗ 0ᴹ             ≈⟨ *ₗ-zeroʳ 0# ⟩
    0ᴹ ∎)
  foldr-homo′ (x ∷ xs) = begin⟨ ≈ᴹ-setoid ⟩
    f x *ₗ x +ᴹ foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < f , id >) 0ᴹ xs
      ≈⟨ +ᴹ-congˡ (foldr-homo′ xs) ⟩
    (fScale x) +ᴹ (fScale (vSum xs))
      ≈⟨ {!!} ⟩
    f (vSum (x ∷ xs)) *ₗ vSum (x ∷ xs) ∎
    
  f≈v∙ : ∀ {a} → f a ≈ v ∙ a
  f≈v∙ {a} = sym (begin⟨ setoid ⟩
    v ∙ a ≈⟨ ∙-comm ⟩
    a ∙ v ≈⟨ foldr-homo-∙ (vscale-cong f ⟦⟧-cong) basisSet ⟩
    foldr (_+_ ∘ (a ∙_) ∘ vscale f) (a ∙ 0ᴹ) basisSet
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

  -- Inner product extensional equivalence.
  x·z≈y·z⇒x≈y : ∀ {x y} → DoubleNegationElimination ℓm →
                 Σ[ (s , z) ∈ S × V ]
                   ((s *ₗ (x +ᴹ -ᴹ y) ≈ᴹ z) × (f z ≉ 0#)) →
                 (∀ {z} → x ∙ z ≈ y ∙ z) → x ≈ᴹ y
  x·z≈y·z⇒x≈y {x} {y} dne Σ[z]fz≉𝟘 x∙z≈y∙z = inj-lm homo {dne} Σ[z]fz≉𝟘 fx≈fy
    where
    fx≈fy : f x ≈ f y
    fx≈fy = begin⟨ setoid ⟩
      f x   ≈⟨ f≈v∙ {x} ⟩
      v ∙ x ≈⟨ ∙-comm ⟩
      x ∙ v ≈⟨ x∙z≈y∙z ⟩
      y ∙ v ≈⟨ ∙-comm ⟩
      v ∙ y ≈⟨ sym (f≈v∙ {y}) ⟩
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

vgen-cong : ∀ f₁ f₂ (xs : List V) →
            foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < f₁ , id >) 0ᴹ xs
            ≈ᴹ foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < f₂ , id >) 0ᴹ xs
vgen-cong f₁ f₂ [] = Setoid.reflexive ≈ᴹ-setoid Eq.refl
vgen-cong f₁ f₂ (x ∷ xs) = {!!}

v-cong : ∀ {lm₁ lm₂} → lm₁ ≈ᴸ lm₂ → LinMap.v lm₁ ≈ᴹ LinMap.v lm₂
v-cong {lm₁} {lm₂} lm₁≈lm₂ = begin⟨ ≈ᴹ-setoid ⟩
  LinMap.v lm₁                                          ≡⟨⟩
  foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < f₁ , id >) 0ᴹ basisSet ≈⟨ fold[f₁]≈fold[f₂] ⟩
  foldr (_+ᴹ_ ∘ uncurry _*ₗ_ ∘ < f₂ , id >) 0ᴹ basisSet ≡⟨⟩
  LinMap.v lm₂                                          ∎
  where
  f₁ = LinMap.f lm₁
  f₂ = LinMap.f lm₂
  fold[f₁]≈fold[f₂] = {!!}
  
-- Isomorphism 1: (V ⊸ S) ↔ V
V⊸S↔V : Inverse lm-setoid ≈ᴹ-setoid
V⊸S↔V = record
  { to        = λ lm → LinMap.v lm
  ; from      = λ u  → mkLM (u ∙_) u∙-homo
  ; to-cong   = λ {lm₁≈lm₂ → {! ≈ᴹ-setoid.cong!}}
  ; from-cong = {!!}
  ; inverse   = {!!}
  }
  -- where
  -- a⊸§→a : {V : Set ℓ₁} {A : Set ℓ₁}
  --          ⦃ _ : Ring V ⦄ ⦃ _ : Ring A ⦄
  --          ⦃ _ : Scalable T A ⦄
  --          ⦃ _ : VectorSpace T A ⦄
  --          ------------------------------
  --       → LinMap T A {A} → T
  -- a⊸§→a = λ { lm → foldl (λ acc v →
  --                      acc + (LinMap.f lm v) · v) 𝟘 basisSet }

  -- a⊸§←a : {T : Set ℓ₁} {A : Set ℓ₁}
  --          ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
  --          ⦃ _ : Scalable T A ⦄
  --          ⦃ _ : VectorSpace T A ⦄
  --          --------------------------------------
  --       → T → LinMap T A {A}
  -- a⊸§←a = λ { a → mkLM (a ⊙_) ⊙-distrib-+ ⊙-comm-· }

  -- a⊸§↔a : {T : Set ℓ₁} {A : Set ℓ₁}
  --          ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
  --          ⦃ _ : Scalable T A ⦄ ⦃ _ : ScalableCont T A ⦄
  --          ⦃ _ : VectorSpace T A ⦄ ⦃ _ : LinMap T A ⦄
  --       → Σ[ y ∈ T ] f y ≢ 𝟘
  --          ---------------------------------------------
  --       → (LinMap T A) ↔ T
  -- a⊸§↔a Σ[y]fy≢𝟘 =
  --   mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}
  --       ( (λ {x → begin
  --                   a⊸§→a (a⊸§←a x)
  --                 ≡⟨⟩
  --                   a⊸§→a (mkLM (x ⊙_) ⊙-distrib-+ ⊙-comm-·)
  --                 ≡⟨⟩
  --                   foldl (λ acc v → acc + (x ⊙ v) · v) 𝟘 basisSet
  --                 ≡⟨ x·z≡y·z→x≡y Σ[y]fy≢𝟘 orthonormal ⟩
  --                   x
  --                 ∎})
  --       , λ {lm → begin
  --                     a⊸§←a (a⊸§→a lm)
  --                   ≡⟨⟩
  --                     a⊸§←a (foldl (λ acc v →
  --                                      acc + (LinMap.f lm v) · v) 𝟘 basisSet)
  --                   ≡⟨⟩
  --                     mkLM ( foldl ( λ acc v →
  --                                      acc + (LinMap.f lm v) · v
  --                                  ) 𝟘 basisSet
  --                            ⊙_
  --                          ) ⊙-distrib-+ ⊙-comm-·
  --                   ≡⟨ ⊸≡ ( extensionality
  --                             ( λ x → orthonormal {f = LinMap.f lm} {x = x} )
  --                         )
  --                    ⟩
  --                     lm
  --                   ∎}
  --       )

