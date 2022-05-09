------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Linear.Properties where

open import Agda.Builtin.Sigma
open import Algebra                             using (CommutativeRing)
open import Algebra.Module                      using (Module)
open import Algebra.Module.Morphism.Linear.Core
open import Data.List
open import Data.Product   using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open import Function       using (_↔_; mk↔; id; const)
open import Level          using (Level; _⊔_)
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

private
  variable
    ℓ₁ ℓ₂ r ℓr m ℓm : Level
    ring           : CommutativeRing r ℓr
    modA modB      : Module ring m ℓm
  
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

  -- Zero is a unique output of linear map ≉ `const 𝟘`.
  zero-unique : {x : A} →
    Σ[ (s , y) ∈ S × A ] ((s ·ᴬ x ≈ᴬ y) × (f y ≉ᴮ 0ᴮ)) →
    x ≉ᴬ 0ᴬ → f x ≉ᴮ 0ᴮ
  zero-unique {x = x} ((s , y) , (s·x≈y , fy≉𝟘)) x≉𝟘 =
    let y≉𝟘 : y ≉ᴬ 0ᴬ
        y≉𝟘 = fx≉𝟘→x≉𝟘 fy≉𝟘
        fs·x≈fy : f (s ·ᴬ x) ≈ᴮ f y
        fs·x≈fy = f-cong s·x≈y
        s·fx≈fy : s ·ᴮ f x ≈ᴮ f y
        s·fx≈fy = begin
          s ·ᴮ f x   ≈⟨ symᴮ scales ⟩
          f (s ·ᴬ x) ≈⟨ fs·x≈fy ⟩
          f y ∎
        s·fx≉𝟘 : (s ·ᴮ f x) ≉ᴮ 0ᴮ
        s·fx≉𝟘 = λ s·fx≈𝟘 →
          fy≉𝟘 ( begin
                 f y        ≈⟨ f-cong (symᴬ s·x≈y) ⟩
                 f (s ·ᴬ x) ≈⟨ scales ⟩
                 s ·ᴮ f x   ≈⟨ s·fx≈𝟘 ⟩
                 0ᴮ ∎
               )
     in non-zeroʳᴮ s·fx≉𝟘

  fx≈𝟘⇒x≈𝟘 : {x : A} →
    Σ[ (s , y) ∈ S × A ] ((s ·ᴬ x ≈ᴬ y) × (f y ≉ᴮ 0ᴮ)) →
    f x ≈ᴮ 0ᴮ → x ≈ᴬ 0ᴬ
  fx≈𝟘⇒x≈𝟘 {x = x} ((s , y) , (s·x≈y , fy≉𝟘)) fx≈𝟘 =
    let ¬x≉𝟘 : ¬ (x ≉ᴬ 0ᴬ)
        ¬x≉𝟘 = λ x≉𝟘 → zero-unique ((s , y) , (s·x≈y , fy≉𝟘)) x≉𝟘 fx≈𝟘
     in ¬-involutive-≈ᴬ ¬x≉𝟘
  
  -- f is odd (i.e. - f (-x) ≈ - (f x)).
  fx+f-x≈𝟘 : {x : A} → f x +ᴮ f (-ᴬ x) ≈ᴮ 0ᴮ
  fx+f-x≈𝟘 {x = x} = begin
    f x +ᴮ f (-ᴬ x) ≈⟨ symᴮ adds ⟩
    f (x +ᴬ (-ᴬ x))      ≈⟨ f-cong (-ᴬ‿inverseʳ x) ⟩
    f 0ᴬ           ≈⟨ f𝟘≈𝟘 {x = x} ⟩
    0ᴮ ∎

  f-x≈-fx : {x : A} → f (-ᴬ x) ≈ᴮ -ᴮ (f x)
  f-x≈-fx {x = x} = uniqueʳ‿-ᴮ (f x) (f (-ᴬ x)) fx+f-x≈𝟘

  -- A non-trivial linear function is injective.
  inj-lm : {x y : A} →
    Σ[ (s , z) ∈ S × A ] ((s ·ᴬ (x +ᴬ -ᴬ y) ≈ᴬ z) × (f z ≉ᴮ 0ᴮ)) →
    f x ≈ᴮ f y → x ≈ᴬ y
  inj-lm {x = x} {y = y} ((s , z) , (s·[x-y]≈z , fz≉𝟘)) fx≈fy =
    let fx-fy≈𝟘 : f x +ᴮ (-ᴮ f y) ≈ᴮ 0ᴮ
        fx-fy≈𝟘 = begin
          f x +ᴮ (-ᴮ f y) ≈⟨ +ᴮ-congˡ (-ᴮ‿cong (symᴮ fx≈fy)) ⟩
          f x +ᴮ (-ᴮ f x) ≈⟨ -ᴮ‿inverseʳ (f x) ⟩
          0ᴮ ∎
        fx-y≈𝟘 : f (x +ᴬ (-ᴬ y)) ≈ᴮ 0ᴮ
        fx-y≈𝟘 = begin
          f (x +ᴬ (-ᴬ y))   ≈⟨ adds ⟩
          f x +ᴮ f (-ᴬ y)   ≈⟨ +ᴮ-congˡ f-x≈-fx ⟩
          f x +ᴮ (-ᴮ (f y)) ≈⟨ fx-fy≈𝟘 ⟩
          0ᴮ ∎
        x-y≈𝟘 : x +ᴬ (-ᴬ y) ≈ᴬ 0ᴬ
        x-y≈𝟘 = fx≈𝟘⇒x≈𝟘 {x = x +ᴬ (-ᴬ y)} ((s , z) , s·[x-y]≈z , fz≉𝟘) fx-y≈𝟘
        x≈--y : x ≈ᴬ -ᴬ (-ᴬ y)
        x≈--y = uniqueʳ‿-ᴬ (-ᴬ y) x
          ( beginᴬ
            -ᴬ y +ᴬ x ≈ᴬ⟨ +ᴬ-comm (-ᴬ y) x ⟩
            x +ᴬ -ᴬ y ≈ᴬ⟨ x-y≈𝟘 ⟩
            0ᴬ ∎ᴬ
          )
     in beginᴬ
        x         ≈ᴬ⟨ x≈--y ⟩
        -ᴬ (-ᴬ y) ≈ᴬ⟨ -ᴬ‿involutive ⟩
        y ∎ᴬ

