------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Algebra.Module.Morphism.Linear.Properties where

open import Agda.Builtin.Sigma
open import Algebra                             using (CommutativeRing)
open import Algebra.Module                      using (Module)
open import Algebra.Module.Morphism.Linear.Core
open import Axiom.Extensionality.Propositional  using (Extensionality)
open import Data.List
open import Data.Product   using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Function       using (_↔_; mk↔; id; const)
open import Level          using (Level; _⊔_)
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

private
  variable
    ℓ₁ ℓ₂ r ℓr m ℓm : Level
    ring           : CommutativeRing r ℓr
    modA modB      : Module ring m ℓm
  
postulate
  extensionality  : Extensionality ℓ₁ ℓ₂
  -- excluded-middle : ∀ {A : Set ℓ₁} → ¬ (¬ A) ≡ A
  -- ≡-involutive    : ∀ {A : Set ℓ₁} → {x y : A} → ¬ (x ≢ y) → x ≡ y

module _ (lm : LinMap modA modB) where

  open LinMap lm
    
  -- f(x) ≈ 0 iff x ≈ 0, for linear non-trivial f
  f𝟘≈𝟘 : {x : A} → f 0ᴬ ≈ᴮ 0ᴮ
  f𝟘≈𝟘 {x = x} = begin
    f 0ᴬ       ≈⟨ f-cong (symᴬ (·ᴬ-zeroˡ x)) ⟩
    f (𝟘 ·ᴬ x) ≈⟨ scales ⟩
    𝟘 ·ᴮ f x   ≈⟨ ·ᴮ-zeroˡ (f x) ⟩
    0ᴮ ∎

  x≈𝟘→fx≈𝟘 : {x : A} → x ≈ᴬ 0ᴬ → f x ≈ᴮ 0ᴮ
  x≈𝟘→fx≈𝟘 {x = x} x≈𝟘 = begin
    f x  ≈⟨ f-cong x≈𝟘 ⟩
    f 0ᴬ ≈⟨ f𝟘≈𝟘 {x = x} ⟩
    0ᴮ ∎
           
  fx≉𝟘→x≉𝟘 : {x : A} → f x ≉ᴮ 0ᴮ → x ≉ᴬ 0ᴬ
  fx≉𝟘→x≉𝟘 = contraposition x≈𝟘→fx≈𝟘

  -- Zero is unique output of linear map ≉ `const 𝟘`.
  zero-unique : {x : A} → Σ[ y ∈ A ] f y ≉ᴮ 0ᴮ → x ≉ᴬ 𝟘 → f x ≉ᴮ 𝟘
  zero-unique {x = x} (y , fy≉𝟘) x≉𝟘 =
    let y≉𝟘 : y ≉ᴬ 0ᴬ
        y≉𝟘 = fx≉𝟘→x≉𝟘 fy≉𝟘
        Σs→s·x≈y : Σ[ s ∈ S ] s ·ᴬ x ≈ᴬ y
        -- Σs→s·x≈y = cont x y
        Σs→s·x≈y = ?
        Σs→fs·x≈fy : Σ[ s ∈ S ] f (s ·ᴬ x) ≈ᴮ f y
        Σs→fs·x≈fy = let (s , g) = Σs→s·x≈y
                       in (s , f-cong g)
        Σs→s·fx≈fy : Σ[ s ∈ S ] s ·ᴮ f x ≈ᴮ f y
        Σs→s·fx≈fy = let (s , g) = Σs→fs·x≈fy
                       in (s , (begin
                                 s ·ᴮ f x
                               ≈⟨ sym scales ⟩
                                 f (s ·ᴬ x)
                               ≈⟨ g ⟩
                                 f y
                               ∎))
        s·fx≉𝟘 : Σ[ s ∈ S ] s ·ᴮ f x ≉ᴮ 0ᴮ
        s·fx≉𝟘 = let (s , g) = Σs→s·fx≈fy
                  in (s , λ s·fx≈𝟘 → fy≉𝟘 (step-≈ (f y) s·fx≈𝟘 (sym g)))
     in non-zeroʳ (snd s·fx≉𝟘)

