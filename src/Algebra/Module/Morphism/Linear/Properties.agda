------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                   using (CommutativeRing)
open import Algebra.Module            using (Module)
open import Level                     using (Level)

module Algebra.Module.Morphism.Linear.Properties
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (modA modB  : Module ring m ℓm)
  where

import Algebra.Module.Properties            as ModuleProperties
import Relation.Binary.Reasoning.Setoid     as Reasoning
import Algebra.Module.Morphism.Structures   as MorphismStructures

open import Axiom.DoubleNegationElimination
open import Data.Product
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

open MorphismStructures.ModuleMorphisms modA modB
module A = Module modA
open A using () renaming (Carrierᴹ to A)
module B = Module modB
open B using () renaming (Carrierᴹ to B)
module PA = ModuleProperties modA
module PB = ModuleProperties modB
open CommutativeRing ring renaming (Carrier to S)

module _
  {f : A → B}
  (isModuleHomomorphism : IsModuleHomomorphism f)
  where

  open IsModuleHomomorphism isModuleHomomorphism

  -- f(x) ≈ 0 iff x ≈ 0, for linear non-trivial f
  f0≈0 : f A.0ᴹ B.≈ᴹ B.0ᴹ
  f0≈0 = begin
    f A.0ᴹ           ≈⟨ ⟦⟧-cong (A.≈ᴹ-sym (A.*ₗ-zeroˡ A.0ᴹ)) ⟩
    f (0# A.*ₗ A.0ᴹ) ≈⟨ *ₗ-homo 0# A.0ᴹ ⟩
    0# B.*ₗ f A.0ᴹ   ≈⟨ B.*ₗ-zeroˡ (f A.0ᴹ) ⟩
    B.0ᴹ             ∎
    where open Reasoning B.≈ᴹ-setoid

  x≈0⇒fx≈0 : ∀ {x} → x A.≈ᴹ A.0ᴹ → f x B.≈ᴹ B.0ᴹ
  x≈0⇒fx≈0 {x} x≈0 = begin
    f x    ≈⟨ ⟦⟧-cong x≈0 ⟩
    f A.0ᴹ ≈⟨ f0≈0 ⟩
    B.0ᴹ   ∎
    where open Reasoning B.≈ᴹ-setoid

  fx≉0⇒x≉0 : ∀ {x} → f x B.≉ᴹ B.0ᴹ → x A.≉ᴹ A.0ᴹ
  fx≉0⇒x≉0 = contraposition x≈0⇒fx≈0

  -- Zero is a unique output of linear map ≉ `const 0`.
  zero-unique : ∀ {x} →
    Σ[ (s , y) ∈ S × A ] ((s A.*ₗ x A.≈ᴹ y) × (f y B.≉ᴹ B.0ᴹ)) →
    x A.≉ᴹ A.0ᴹ → f x B.≉ᴹ B.0ᴹ
  zero-unique {x} ((s , y) , (s·x≈y , fy≉0)) x≉0 =
    PB.non-zeroʳ s·fx≉0
    where
    open Reasoning B.≈ᴹ-setoid
    y≉0     : y A.≉ᴹ A.0ᴹ
    y≉0     = fx≉0⇒x≉0 fy≉0
    fs·x≈fy : f (s A.*ₗ x) B.≈ᴹ f y
    fs·x≈fy = ⟦⟧-cong s·x≈y
    s·fx≈fy : s B.*ₗ f x B.≈ᴹ f y
    s·fx≈fy = begin
      s B.*ₗ f x   ≈⟨ B.≈ᴹ-sym (*ₗ-homo s x) ⟩
      f (s A.*ₗ x) ≈⟨ fs·x≈fy ⟩
      f y          ∎
    s·fx≉0  : (s B.*ₗ f x) B.≉ᴹ B.0ᴹ
    s·fx≉0 s·fx≈0 =
      fy≉0 ( begin
             f y          ≈⟨ ⟦⟧-cong (A.≈ᴹ-sym s·x≈y) ⟩
             f (s A.*ₗ x) ≈⟨ *ₗ-homo s x ⟩
             s B.*ₗ f x   ≈⟨ s·fx≈0 ⟩
             B.0ᴹ         ∎
           )

  -- f is odd (i.e. - f (-x) ≈ - (f x)).
  fx+f[-x]≈0 : ∀ {x} → f x B.+ᴹ f (A.-ᴹ x) B.≈ᴹ B.0ᴹ
  fx+f[-x]≈0 {x} = begin
    f x B.+ᴹ f (A.-ᴹ x) ≈⟨ B.≈ᴹ-sym (+ᴹ-homo x (A.-ᴹ x)) ⟩
    f (x A.+ᴹ (A.-ᴹ x)) ≈⟨ ⟦⟧-cong (A.-ᴹ‿inverseʳ x) ⟩
    f A.0ᴹ              ≈⟨ f0≈0 ⟩
    B.0ᴹ                ∎
    where open Reasoning B.≈ᴹ-setoid

  f[-x]≈-fx : ∀ {x} → f (A.-ᴹ x) B.≈ᴹ B.-ᴹ f x
  f[-x]≈-fx {x} = B.uniqueʳ‿-ᴹ (f x) (f (A.-ᴹ x)) fx+f[-x]≈0

  module _ {dne : DoubleNegationElimination _} where

    fx≈0⇒x≈0 : ∀ {x} →
      Σ[ (s , y) ∈ S × A ] ((s A.*ₗ x A.≈ᴹ y) × (f y B.≉ᴹ B.0ᴹ)) →
      f x B.≈ᴹ B.0ᴹ → x A.≈ᴹ A.0ᴹ
    fx≈0⇒x≈0 {x} ((s , y) , (s·x≈y , fy≉0)) fx≈0 =
      dne ¬x≉0
      where
      ¬x≉0 : ¬ (x A.≉ᴹ A.0ᴹ)
      ¬x≉0 = λ x≉0 → zero-unique ((s , y) , (s·x≈y , fy≉0)) x≉0 fx≈0

    -- A non-trivial linear function is injective.
    fx-fy≈0 : ∀ {x} {y} → (f x B.≈ᴹ f y) → f x B.+ᴹ (B.-ᴹ f y) B.≈ᴹ B.0ᴹ
    fx-fy≈0 {x} {y} fx≈fy = begin
      f x B.+ᴹ (B.-ᴹ f y) ≈⟨ B.+ᴹ-congˡ (B.-ᴹ‿cong (B.≈ᴹ-sym fx≈fy)) ⟩
      f x B.+ᴹ (B.-ᴹ f x) ≈⟨ B.-ᴹ‿inverseʳ (f x) ⟩
      B.0ᴹ                ∎
      where open Reasoning B.≈ᴹ-setoid

    fx-y≈0 : ∀ {x} {y} → (f x B.≈ᴹ f y) → f (x A.+ᴹ (A.-ᴹ y)) B.≈ᴹ B.0ᴹ
    fx-y≈0 {x} {y} fx≈fy = begin
      f (x A.+ᴹ (A.-ᴹ y)) ≈⟨ +ᴹ-homo x (A.-ᴹ y) ⟩
      f x B.+ᴹ f (A.-ᴹ y) ≈⟨ B.+ᴹ-congˡ f[-x]≈-fx ⟩
      f x B.+ᴹ (B.-ᴹ f y) ≈⟨ fx-fy≈0 fx≈fy ⟩
      B.0ᴹ                ∎
      where open Reasoning B.≈ᴹ-setoid

    inj-lm : ∀ {x} {y} →
      Σ[ (s , z) ∈ S × A ] ( (s A.*ₗ (x A.+ᴹ A.-ᴹ y) A.≈ᴹ z)
                           × (f z B.≉ᴹ B.0ᴹ)) →
      f x B.≈ᴹ f y → x A.≈ᴹ y
    inj-lm {x} {y} ((s , z) , (s·[x-y]≈z , fz≉0)) fx≈fy =
      begin
      x             ≈⟨ x≈--y ⟩
      A.-ᴹ (A.-ᴹ y) ≈⟨ PA.-ᴹ-involutive y ⟩
      y             ∎
      where
      open Reasoning A.≈ᴹ-setoid
      x-y≈0 : x A.+ᴹ (A.-ᴹ y) A.≈ᴹ A.0ᴹ
      x-y≈0 = fx≈0⇒x≈0 {x = x A.+ᴹ (A.-ᴹ y)}
                        ((s , z) , s·[x-y]≈z , fz≉0)
                        (fx-y≈0 fx≈fy)
      x≈--y : x A.≈ᴹ A.-ᴹ (A.-ᴹ y)
      x≈--y = A.uniqueʳ‿-ᴹ (A.-ᴹ y) x
        ( begin
          A.-ᴹ y A.+ᴹ x ≈⟨ A.+ᴹ-comm (A.-ᴹ y) x ⟩
          x A.+ᴹ A.-ᴹ y ≈⟨ x-y≈0 ⟩
          A.0ᴹ          ∎
        )
