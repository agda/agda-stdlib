------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                   using (CommutativeRing)
open import Algebra.Module            using (Module)
open import Level                     using (Level; _⊔_)

module Algebra.Module.Morphism.Linear.Properties
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (modA modB  : Module ring m ℓm)
  where

import Algebra.Module.Properties          as Properties
import Function.Definitions
import Relation.Binary.Reasoning.Setoid   as Reasoning
import Algebra.Module.Morphism.Structures as MorphismStructures

open import Agda.Builtin.Sigma
open import Axiom.DoubleNegationElimination
open import Data.List
open import Data.Product
  using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

open MorphismStructures.ModuleMorphisms modA modB
open Module modA
  using () renaming
  ( Carrierᴹ       to A
  ; _+ᴹ_           to _+ᴬ_
  ; _*ₗ_           to _·ᴬ_
  ; -ᴹ_            to -ᴬ_
  ; _≈ᴹ_           to _≈ᴬ_
  ; 0ᴹ             to 0ᴬ
  ; +ᴹ-comm        to +ᴬ-comm
  ; +ᴹ-congˡ       to +ᴬ-congˡ
  ; +ᴹ-congʳ       to +ᴬ-congʳ
  ; *ₗ-zeroˡ       to ·ᴬ-zeroˡ
  ; -ᴹ‿cong        to -ᴬ‿cong
  ; -ᴹ‿inverseʳ    to -ᴬ‿inverseʳ
  ; -ᴹ‿involutive  to -ᴬ‿involutive
  ; uniqueʳ‿-ᴹ     to uniqueʳ‿-ᴬ
  ; ≈ᴹ-setoid      to ≈ᴬ-setoid
  ; ≈ᴹ-sym         to symᴬ
  ; leftSemimodule to leftSemimoduleᴬ
  )
open Properties leftSemimoduleᴬ
  using () renaming
  ( non-zeroʳ to non-zeroʳᴬ
  ; non-zeroˡ to non-zeroˡᴬ
  )
open Module modB
  using () renaming
  ( Carrierᴹ       to B
  ; _+ᴹ_           to _+ᴮ_
  ; _*ₗ_           to _·ᴮ_
  ; -ᴹ_            to -ᴮ_
  ; _≈ᴹ_           to _≈ᴮ_
  ; 0ᴹ             to 0ᴮ
  ; +ᴹ-comm        to +ᴮ-comm
  ; +ᴹ-congˡ       to +ᴮ-congˡ
  ; +ᴹ-congʳ       to +ᴮ-congʳ
  ; *ₗ-zeroˡ       to ·ᴮ-zeroˡ
  ; -ᴹ‿cong        to -ᴮ‿cong
  ; -ᴹ‿inverseʳ    to -ᴮ‿inverseʳ
  ; -ᴹ‿involutive  to -ᴮ‿involutive
  ; uniqueʳ‿-ᴹ     to uniqueʳ‿-ᴮ
  ; ≈ᴹ-setoid      to ≈ᴮ-setoid
  ; ≈ᴹ-sym         to symᴮ
  ; leftSemimodule to leftSemimoduleᴮ
  )
open Properties leftSemimoduleᴮ
  using () renaming
  ( non-zeroʳ to non-zeroʳᴮ
  ; non-zeroˡ to non-zeroˡᴮ
  )
open CommutativeRing ring
  using (_≈_; _*_; _+_) renaming
  ( Carrier to S
  ; 0#      to 𝟘
  ; 1#      to 𝟙
  )
open module Reasoningᴬ = Reasoning ≈ᴬ-setoid
  using () renaming
  ( begin_ to beginᴬ_
  ; _∎     to _∎ᴬ
  )
infixr 2 step-≈ᴬ
step-≈ᴬ = Reasoningᴬ.step-≈
syntax step-≈ᴬ x y≈z x≈y = x ≈ᴬ⟨ x≈y ⟩ y≈z
open module Reasoningᴮ = Reasoning ≈ᴮ-setoid
open Function.Definitions _≈ᴬ_ _≈ᴮ_

_≉ᴬ_ : A → A → Set ℓm
x ≉ᴬ y = ¬ (x ≈ᴬ y)

_≉ᴮ_ : B → B → Set ℓm
x ≉ᴮ y = ¬ (x ≈ᴮ y)

module _
  {⟦_⟧ : A → B}
  (isModuleHomomorphism : IsModuleHomomorphism ⟦_⟧)
  where

  open IsModuleHomomorphism isModuleHomomorphism

  -- f(x) ≈ 0 iff x ≈ 0, for linear non-trivial f
  f𝟘≈𝟘 : {x : A} → ⟦ 0ᴬ ⟧ ≈ᴮ 0ᴮ
  f𝟘≈𝟘 {x = x} = begin
    ⟦ 0ᴬ ⟧       ≈⟨ ⟦⟧-cong (symᴬ (·ᴬ-zeroˡ x)) ⟩
    ⟦ (𝟘 ·ᴬ x) ⟧ ≈⟨ *ₗ-homo 𝟘 x ⟩
    𝟘 ·ᴮ ⟦ x ⟧   ≈⟨ ·ᴮ-zeroˡ ⟦ x ⟧ ⟩
    0ᴮ ∎

  x≈𝟘→fx≈𝟘 : {x : A} → x ≈ᴬ 0ᴬ → ⟦ x ⟧ ≈ᴮ 0ᴮ
  x≈𝟘→fx≈𝟘 {x = x} x≈𝟘 = begin
    ⟦ x ⟧  ≈⟨ ⟦⟧-cong x≈𝟘 ⟩
    ⟦ 0ᴬ ⟧ ≈⟨ f𝟘≈𝟘 {x = x} ⟩
    0ᴮ ∎

  fx≉𝟘→x≉𝟘 : {x : A} → ⟦ x ⟧ ≉ᴮ 0ᴮ → x ≉ᴬ 0ᴬ
  fx≉𝟘→x≉𝟘 = contraposition x≈𝟘→fx≈𝟘

  -- Zero is a unique output of linear map ≉ `const 𝟘`.
  zero-unique : {x : A} →
    Σ[ (s , y) ∈ S × A ] ((s ·ᴬ x ≈ᴬ y) × (⟦ y ⟧ ≉ᴮ 0ᴮ)) →
    x ≉ᴬ 0ᴬ → ⟦ x ⟧ ≉ᴮ 0ᴮ
  zero-unique {x = x} ((s , y) , (s·x≈y , fy≉𝟘)) x≉𝟘 =
    non-zeroʳᴮ s·fx≉𝟘
    where
    y≉𝟘     : y ≉ᴬ 0ᴬ
    y≉𝟘     = fx≉𝟘→x≉𝟘 fy≉𝟘
    fs·x≈fy : ⟦ (s ·ᴬ x) ⟧ ≈ᴮ ⟦ y ⟧
    fs·x≈fy = ⟦⟧-cong s·x≈y
    s·fx≈fy : s ·ᴮ ⟦ x ⟧ ≈ᴮ ⟦ y ⟧
    s·fx≈fy = begin
      s ·ᴮ ⟦ x ⟧   ≈⟨ symᴮ (*ₗ-homo s x) ⟩
      ⟦ (s ·ᴬ x) ⟧ ≈⟨ fs·x≈fy ⟩
      ⟦ y ⟧ ∎
    s·fx≉𝟘  : (s ·ᴮ ⟦ x ⟧) ≉ᴮ 0ᴮ
    s·fx≉𝟘  = λ s·fx≈𝟘 →
      fy≉𝟘 ( begin
             ⟦ y ⟧        ≈⟨ ⟦⟧-cong (symᴬ s·x≈y) ⟩
             ⟦ (s ·ᴬ x) ⟧ ≈⟨ *ₗ-homo s x ⟩
             s ·ᴮ ⟦ x ⟧   ≈⟨ s·fx≈𝟘 ⟩
             0ᴮ ∎
           )

  -- f is odd (i.e. - f (-x) ≈ - (f x)).
  fx+f-x≈𝟘 : {x : A} → ⟦ x ⟧ +ᴮ ⟦ (-ᴬ x) ⟧ ≈ᴮ 0ᴮ
  fx+f-x≈𝟘 {x = x} = begin
    ⟦ x ⟧ +ᴮ ⟦ (-ᴬ x) ⟧ ≈⟨ symᴮ (+ᴹ-homo x (-ᴬ x)) ⟩
    ⟦ (x +ᴬ (-ᴬ x)) ⟧   ≈⟨ ⟦⟧-cong (-ᴬ‿inverseʳ x) ⟩
    ⟦ 0ᴬ ⟧              ≈⟨ f𝟘≈𝟘 {x = x} ⟩
    0ᴮ ∎

  f-x≈-fx : {x : A} → ⟦ (-ᴬ x) ⟧ ≈ᴮ -ᴮ ⟦ x ⟧
  f-x≈-fx {x = x} = uniqueʳ‿-ᴮ ⟦ x ⟧ ⟦ -ᴬ x ⟧ fx+f-x≈𝟘

  module _ {dne : DoubleNegationElimination _} where

    fx≈𝟘⇒x≈𝟘 : {x : A} →
      Σ[ (s , y) ∈ S × A ] ((s ·ᴬ x ≈ᴬ y) × (⟦ y ⟧ ≉ᴮ 0ᴮ)) →
      ⟦ x ⟧ ≈ᴮ 0ᴮ → x ≈ᴬ 0ᴬ
    fx≈𝟘⇒x≈𝟘 {x = x} ((s , y) , (s·x≈y , fy≉𝟘)) fx≈𝟘 =
      dne ¬x≉𝟘
      where
      ¬x≉𝟘 : ¬ (x ≉ᴬ 0ᴬ)
      ¬x≉𝟘 = λ x≉𝟘 → zero-unique ((s , y) , (s·x≈y , fy≉𝟘)) x≉𝟘 fx≈𝟘

    -- A non-trivial linear function is injective.
    inj-lm : {x y : A} →
      Σ[ (s , z) ∈ S × A ] ((s ·ᴬ (x +ᴬ -ᴬ y) ≈ᴬ z) × (⟦ z ⟧ ≉ᴮ 0ᴮ)) →
      ⟦ x ⟧ ≈ᴮ ⟦ y ⟧ → x ≈ᴬ y
    inj-lm {x = x} {y = y} ((s , z) , (s·[x-y]≈z , fz≉𝟘)) fx≈fy =
      beginᴬ
      x         ≈ᴬ⟨ x≈--y ⟩
      -ᴬ (-ᴬ y) ≈ᴬ⟨ -ᴬ‿involutive ⟩
      y ∎ᴬ
      where
      fx-fy≈𝟘 : ⟦ x ⟧ +ᴮ (-ᴮ ⟦ y ⟧) ≈ᴮ 0ᴮ
      fx-fy≈𝟘 = begin
        ⟦ x ⟧ +ᴮ (-ᴮ ⟦ y ⟧) ≈⟨ +ᴮ-congˡ (-ᴮ‿cong (symᴮ fx≈fy)) ⟩
        ⟦ x ⟧ +ᴮ (-ᴮ ⟦ x ⟧) ≈⟨ -ᴮ‿inverseʳ (⟦ x ⟧) ⟩
        0ᴮ ∎
      fx-y≈𝟘 : ⟦ (x +ᴬ (-ᴬ y)) ⟧ ≈ᴮ 0ᴮ
      fx-y≈𝟘 = begin
        ⟦ x +ᴬ (-ᴬ y) ⟧     ≈⟨ +ᴹ-homo x (-ᴬ y) ⟩
        ⟦ x ⟧ +ᴮ ⟦ -ᴬ y ⟧   ≈⟨ +ᴮ-congˡ f-x≈-fx ⟩
        ⟦ x ⟧ +ᴮ (-ᴮ ⟦ y ⟧) ≈⟨ fx-fy≈𝟘 ⟩
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
