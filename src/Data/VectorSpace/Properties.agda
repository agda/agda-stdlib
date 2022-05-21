------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
  using (CommutativeRing; Congruent₁; Congruent₂)
open import Algebra.Module        using (Module)
open import Data.VectorSpace.Core using (VectorSpace)
open import Level                 using (Level; _⊔_; suc)

module Data.VectorSpace.Properties
  {r ℓr m ℓm : Level}
  {ring : CommutativeRing r ℓr}
  {mod  : Module ring m ℓm}
  (vs   : VectorSpace mod)
  where

-- import Algebra.Module.Properties                 as ModuleProperties
import Relation.Binary.PropositionalEquality     as Eq
import Relation.Binary.Reasoning.Setoid          as Reasoning

open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
-- open import Algebra.Module.Morphism.Linear.Properties mod ⟨module⟩
import Algebra.Module.Morphism.Structures as MorphismStructures
open MorphismStructures.ModuleMorphisms mod ⟨module⟩
-- open import Function using ()
-- open import Function.Consequences -- using (∘-cong₂)      -- using (_$_)
-- open import Data.List     -- using (foldl; List; []; _∷_; _∷ʳ_)
open import Data.Product
  -- using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
-- open import Relation.Binary.PropositionalEquality using (cong₂)

open VectorSpace vs
open CommutativeRing ring
  -- using (_+_; _*_; _≈_; setoid; sym; refl; 0#)
  renaming (Carrier to S)
module T = Module mod
open T -- using (_*ₗ_)
  renaming (Carrierᴹ to T)

-- open MorphismStructures.ModuleMorphisms mod ⟨module⟩

-- Properties predicated upon a linear map from tensor to scalar.
module _
  {f : T → S}
  (isModuleHomomorphism : IsModuleHomomorphism f)
  where

  open IsModuleHomomorphism isModuleHomomorphism

  -- Any linear map from T to S is equivalent to an inner product with
  -- some vector, v.
  T⊸S≈v∙ : ∀ {a} → ∃[ v ] f a ≈ v ∙ a
  T⊸S≈v∙ = {!!}

  --          f a ≈ ( foldl (λ acc b → acc T.+ᴹ ⟦ b ⟧ *ₗ b)
  --                          T.0ᴹ basisSet
  --                  ) ∙ a
  -- T⊸S≈v∙ {a = a} = sym $ begin
  --   (foldl (λ acc b → acc T.+ᴹ ⟦ b ⟧ *ₗ b) T.0ᴹ basisSet) ∙ a ≈⟨ {!!} ⟩
  --   ⟦ a ⟧ ∎

--   -- x·z≈y·z→x≈y : {x y : T} → Σ[ y ∈ T ] f y ≉ 0# →
--   --   (∀ {z : T} → x ∙ z ≈ y ∙ z) → x ≈ᵀ y
--   -- x·z≈y·z→x≈y {x = x} {y = y} Σ[y]fy≉𝟘 x∙z≈y∙z =
--   --   let z = foldl (λ acc v → acc T.+ᴹ f v *ₗ v) T.0ᴹ basisSet
--   --       -- x·z≈y·z = x∙z≈y∙z {z}
--   --       z·x≈y·z : z ∙ x ≈ y ∙ z
--   --       -- z·x≈y·z = step-≈ (z ∙ x) x·z≈y·z comm-∙
--   --       -- z·x≈y·z = step-≈ (z ∙ x) x∙z≈y∙z {z} comm-∙
--   --       z·x≈y·z = begin (z ∙ x) ≈⟨ comm-∙ ⟩ x∙z≈y∙z {z} ∎
--   --       z·x≈z·y : z ∙ x ≈ z ∙ y
--   --       z·x≈z·y = sym (step-≈ (z ∙ y) (sym z·x≈y·z) comm-∙)
--   --       fx≈z·y : f x ≈ z ∙ y
--   --       fx≈z·y = step-≈ (f x) z·x≈z·y (sym orthonormal)
--   --       fx≈fy : f x ≈ f y
--   --       fx≈fy = sym (step-≈ (f y) (sym fx≈z·y) (sym orthonormal))
--   --    in inj-lm Σ[y]fy≉𝟘 fx≈fy
  
--   -- basisSet = {b₀, b₁}
--   -- orthonormal :
--   --   (0 + f b₀ · b₀ + f b₁ · b₁) ∙ a ≈ f a        ≈⟨ ∙-distrib-+ ⟩
--   --   f a ≈ a ∙ (f b₀ · b₀) + a ∙ (f b₁ · b₁)      ≈⟨ ∙-comm-· ⟩
--   --   f a ≈ f b₀ * (a ∙ b₀) + f b₁ * (a ∙ b₁)      ≈⟨ f linear ⟩
--   --   f a ≈ f ((a ∙ b₀) · b₀) + f ((a ∙ b₁) · b₁)  ≈⟨ f linear ⟩
--   --   f a ≈ f ((a ∙ b₀) · b₀ + (a ∙ b₁) · b₁)      ≈⟨ subst ⟩
--   --   a ≈ (a ∙ b₀) · b₀ + (a ∙ b₁) · b₁            ≈⟨ generalize ⟩
--   --   a ≈ foldl (λ acc b → acc + (a ∙ b)·b) 0 basisSet


-- foldr-ʳ++ : ∀ (f : A → B → B) b xs {ys} →
--             foldr f b (xs ʳ++ ys) ≡ foldl (flip f) (foldr f b ys) xs
-- foldl-ʳ++ : ∀ (f : B → A → B) b xs {ys} →
--             foldl f b (xs ʳ++ ys) ≡ foldl f (foldr (flip f) b xs) ys
-- reverse-foldr : ∀ (f : A → B → B) b →
--                 foldr f b ∙ reverse ≗ foldl (flip f) b
-- reverse-foldl : ∀ (f : B → A → B) b xs →
--                 foldl f b (reverse xs) ≡ foldr (flip f) b xs
-- foldr-cong : ∀ {f g : A → B → B} {d e : B} →
--              (∀ x y → f x y ≡ g x y) → d ≡ e →
--              foldr f d ≗ foldr g e

-- Some useful properties of left folds.
-- foldl-cong-init : ∀ {f x₁ x₂} → Congruent₂ _≈ᴹ_ _≈ᴹ_ f → x₁ T.≈ᴹ x₂ →
-- foldl-cong-init : ∀ {f x₁ x₂} → Congruent₂ _≈ᴹ_ f → x₁ T.≈ᴹ x₂ →
--                   ∀ xs → foldl f x₁ xs T.≈ᴹ foldl f x₂ xs
-- foldl-cong-init f-cong₂ x₁≈x₂ []       = x₁≈x₂
-- foldl-cong-init f-cong₂ x₁≈x₂ (x ∷ xs) =
--   foldl-cong-init f-cong₂ (f-cong₂ x₁≈x₂ (≈ᴹ-reflexive Eq.refl)) xs

-- foldl-+-[𝟘+x]-xs≈foldl-+-𝟘-x∷xs : ∀ {x} {xs} →
--   -- foldl _+_ (0# + x) xs ≈ foldl _+_ 0# (x ∷ xs)
--   foldl _+_ x xs ≈ foldl _+_ 0# (x ∷ xs)
-- -- foldl-+-[𝟘+x]-xs≈foldl-+-𝟘-x∷xs = refl
-- foldl-+-[𝟘+x]-xs≈foldl-+-𝟘-x∷xs {x} {xs} = begin
--   -- foldl _+_ x xs        ≈⟨ foldl-cong-init ? (sym (+-identityˡ x)) ⟩
--   foldl _+_ x xs        ≈⟨ {!foldl-cong₁!} ⟩
--   foldl _+_ (0# + x) xs ≈⟨ {!!} ⟩
--   foldl _+_ 0# (x ∷ xs) ∎
--   where open Reasoning setoid
  
-- ∙-distrib-foldl-acc : ∀ (a : T) → (f : T → T) → Congruent₁ _≈ᴹ_ _≈ᴹ_ f →
-- ∙-distrib-foldl-acc : ∀ (a : T) → (f : T → T) → Congruent₁ _≈ᴹ_ f →
--                       (bs : List T) →
--                       a ∙ foldl (λ acc b → acc T.+ᴹ f b) T.0ᴹ bs ≈
--                       foldl (λ acc b → acc + a ∙ f b) 0# bs
-- ∙-distrib-foldl-acc a f f-cong bs with bs
-- ... | []     = ∙-idʳ
-- ... | x ∷ xs = begin
--   a ∙ foldl (λ acc b → acc T.+ᴹ f b) (T.0ᴹ T.+ᴹ f x) xs
--     ≈⟨ ∙-congˡ (foldl-cong-init (flip-cong₂ ≈ᴹ-setoid (∘-cong₂ f-cong +ᴹ-cong))
--                                 (+ᴹ-identityˡ (f x)) xs) ⟩
--   a ∙ foldl (λ acc b → acc T.+ᴹ f b) (f x) xs         ≈⟨ {!!} ⟩
--   a ∙ (f x T.+ᴹ foldl (λ acc b → acc T.+ᴹ f b) T.0ᴹ xs)   ≈⟨ {!!} ⟩
--   a ∙ f x + a ∙ foldl (λ acc b → acc T.+ᴹ f b) T.0ᴹ xs  ≈⟨ {!!} ⟩
--   a ∙ f x + foldl (λ acc b → acc + a ∙ f b) 0# xs    ≈⟨ {!!} ⟩
--   foldl (λ acc b → acc + a ∙ f b) (0# + a ∙ f x) xs ∎
--   where open Reasoning setoid
  -- where open Reasoning ≈ᴹ-setoid

