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
open Function.Definitions _≈ᴬ_ _≈ᴮ_

_≉ᴬ_ : A → A → Set ℓm
x ≉ᴬ y = ¬ (x ≈ᴬ y)

_≉ᴮ_ : B → B → Set ℓm
x ≉ᴮ y = ¬ (x ≈ᴮ y)

module _
  {f : A → B}
  (isModuleHomomorphism : IsModuleHomomorphism f)
  where

  open IsModuleHomomorphism isModuleHomomorphism

  -- f(x) ≈ 0 iff x ≈ 0, for linear non-trivial f
  f𝟘≈𝟘 : f 0ᴬ ≈ᴮ 0ᴮ
  f𝟘≈𝟘 = begin
    f 0ᴬ        ≈⟨ ⟦⟧-cong (symᴬ (·ᴬ-zeroˡ 0ᴬ)) ⟩
    f (𝟘 ·ᴬ 0ᴬ) ≈⟨ *ₗ-homo 𝟘 0ᴬ ⟩
    𝟘 ·ᴮ f 0ᴬ   ≈⟨ ·ᴮ-zeroˡ (f 0ᴬ) ⟩
    0ᴮ ∎
    where open Reasoning ≈ᴮ-setoid

  x≈𝟘→fx≈𝟘 : {x : A} → x ≈ᴬ 0ᴬ → f x ≈ᴮ 0ᴮ
  x≈𝟘→fx≈𝟘 {x = x} x≈𝟘 = begin
    f x  ≈⟨ ⟦⟧-cong x≈𝟘 ⟩
    f 0ᴬ ≈⟨ f𝟘≈𝟘 ⟩
    0ᴮ ∎
    where open Reasoning ≈ᴮ-setoid

  fx≉𝟘→x≉𝟘 : {x : A} → f x ≉ᴮ 0ᴮ → x ≉ᴬ 0ᴬ
  fx≉𝟘→x≉𝟘 = contraposition x≈𝟘→fx≈𝟘

  -- Zero is a unique output of linear map ≉ `const 𝟘`.
  zero-unique : {x : A} →
    Σ[ (s , y) ∈ S × A ] ((s ·ᴬ x ≈ᴬ y) × (f y ≉ᴮ 0ᴮ)) →
    x ≉ᴬ 0ᴬ → f x ≉ᴮ 0ᴮ
  zero-unique {x = x} ((s , y) , (s·x≈y , fy≉𝟘)) x≉𝟘 =
    non-zeroʳᴮ s·fx≉𝟘
    where
    open Reasoning ≈ᴮ-setoid
    y≉𝟘     : y ≉ᴬ 0ᴬ
    y≉𝟘     = fx≉𝟘→x≉𝟘 fy≉𝟘
    fs·x≈fy : f (s ·ᴬ x) ≈ᴮ f y
    fs·x≈fy = ⟦⟧-cong s·x≈y
    s·fx≈fy : s ·ᴮ f x ≈ᴮ f y
    s·fx≈fy = begin
      s ·ᴮ f x   ≈⟨ symᴮ (*ₗ-homo s x) ⟩
      f (s ·ᴬ x) ≈⟨ fs·x≈fy ⟩
      f y ∎
    s·fx≉𝟘  : (s ·ᴮ f x) ≉ᴮ 0ᴮ
    s·fx≉𝟘  = λ s·fx≈𝟘 →
      fy≉𝟘 ( begin
             f y        ≈⟨ ⟦⟧-cong (symᴬ s·x≈y) ⟩
             f (s ·ᴬ x) ≈⟨ *ₗ-homo s x ⟩
             s ·ᴮ f x   ≈⟨ s·fx≈𝟘 ⟩
             0ᴮ ∎
           )

  -- f is odd (i.e. - f (-x) ≈ - (f x)).
  fx+f-x≈𝟘 : {x : A} → f x +ᴮ f (-ᴬ x) ≈ᴮ 0ᴮ
  fx+f-x≈𝟘 {x = x} = begin
    f x +ᴮ f (-ᴬ x) ≈⟨ symᴮ (+ᴹ-homo x (-ᴬ x)) ⟩
    f (x +ᴬ (-ᴬ x)) ≈⟨ ⟦⟧-cong (-ᴬ‿inverseʳ x) ⟩
    f 0ᴬ            ≈⟨ f𝟘≈𝟘 ⟩
    0ᴮ ∎
    where open Reasoning ≈ᴮ-setoid

  f-x≈-fx : {x : A} → f (-ᴬ x) ≈ᴮ -ᴮ f x
  f-x≈-fx {x = x} = uniqueʳ‿-ᴮ (f x) (f (-ᴬ x)) fx+f-x≈𝟘

  module _ {dne : DoubleNegationElimination _} where

    fx≈𝟘⇒x≈𝟘 : {x : A} →
      Σ[ (s , y) ∈ S × A ] ((s ·ᴬ x ≈ᴬ y) × (f y ≉ᴮ 0ᴮ)) →
      f x ≈ᴮ 0ᴮ → x ≈ᴬ 0ᴬ
    fx≈𝟘⇒x≈𝟘 {x = x} ((s , y) , (s·x≈y , fy≉𝟘)) fx≈𝟘 =
      dne ¬x≉𝟘
      where
      ¬x≉𝟘 : ¬ (x ≉ᴬ 0ᴬ)
      ¬x≉𝟘 = λ x≉𝟘 → zero-unique ((s , y) , (s·x≈y , fy≉𝟘)) x≉𝟘 fx≈𝟘

    -- A non-trivial linear function is injective.
    fx-fy≈𝟘 : {x y : A} {fx≈fy : f x ≈ᴮ f y} → f x +ᴮ (-ᴮ f y) ≈ᴮ 0ᴮ
    fx-fy≈𝟘 {x = x} {y = y} {fx≈fy = fx≈fy} = begin
      f x +ᴮ (-ᴮ f y) ≈⟨ +ᴮ-congˡ (-ᴮ‿cong (symᴮ fx≈fy)) ⟩
      f x +ᴮ (-ᴮ f x) ≈⟨ -ᴮ‿inverseʳ (f x) ⟩
      0ᴮ ∎
      where open Reasoning ≈ᴮ-setoid

    fx-y≈𝟘 : {x y : A} {fx≈fy : f x ≈ᴮ f y} → f (x +ᴬ (-ᴬ y)) ≈ᴮ 0ᴮ
    fx-y≈𝟘 {x = x} {y = y} {fx≈fy = fx≈fy} = begin
      f (x +ᴬ (-ᴬ y)) ≈⟨ +ᴹ-homo x (-ᴬ y) ⟩
      f x +ᴮ f (-ᴬ y) ≈⟨ +ᴮ-congˡ f-x≈-fx ⟩
      f x +ᴮ (-ᴮ f y) ≈⟨ fx-fy≈𝟘 {fx≈fy = fx≈fy} ⟩
      0ᴮ ∎
      where open Reasoning ≈ᴮ-setoid

    inj-lm : {x y : A} →
      Σ[ (s , z) ∈ S × A ] ((s ·ᴬ (x +ᴬ -ᴬ y) ≈ᴬ z) × (f z ≉ᴮ 0ᴮ)) →
      f x ≈ᴮ f y → x ≈ᴬ y
    inj-lm {x = x} {y = y} ((s , z) , (s·[x-y]≈z , fz≉𝟘)) fx≈fy =
      begin
      x         ≈⟨ x≈--y ⟩
      -ᴬ (-ᴬ y) ≈⟨ -ᴬ‿involutive ⟩
      y ∎
      where
      open Reasoning ≈ᴬ-setoid
      x-y≈𝟘 : x +ᴬ (-ᴬ y) ≈ᴬ 0ᴬ
      x-y≈𝟘 = fx≈𝟘⇒x≈𝟘 {x = x +ᴬ (-ᴬ y)}
                        ((s , z) , s·[x-y]≈z , fz≉𝟘)
                        (fx-y≈𝟘 {fx≈fy = fx≈fy})
      x≈--y : x ≈ᴬ -ᴬ (-ᴬ y)
      x≈--y = uniqueʳ‿-ᴬ (-ᴬ y) x
        ( begin
          -ᴬ y +ᴬ x ≈⟨ +ᴬ-comm (-ᴬ y) x ⟩
          x +ᴬ -ᴬ y ≈⟨ x-y≈𝟘 ⟩
          0ᴬ ∎
        )
