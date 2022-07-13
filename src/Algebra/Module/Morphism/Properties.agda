------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Properties where

import Algebra.Module.Properties          as ModuleProperties
import Algebra.Module.Morphism.Structures as MorphismStructures

open import Algebra                   using (CommutativeRing)
open import Algebra.Module            using (Module)
open import Algebra.Module.Morphism.Bundles
open import Axiom.DoubleNegationElimination
open import Data.Product
open import Level                     using (Level)
open import Relation.Binary.Reasoning.MultiSetoid
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

module LinearMapProperties
  {r ℓr m ℓm n ℓn : Level}
  {ring           : CommutativeRing r ℓr}
  {modA           : Module ring m ℓm}
  {modB           : Module ring n ℓn}
  (lm             : LinearMap modA modB)
  where

  open MorphismStructures.ModuleMorphisms modA modB
  module A = Module modA
  open A using () renaming (Carrierᴹ to A)
  module B = Module modB
  open B using () renaming (Carrierᴹ to B)
  module PA = ModuleProperties modA
  module PB = ModuleProperties modB
  open CommutativeRing ring renaming (Carrier to S)
  open LinearMap lm

  x≈0⇒fx≈0 : ∀ {x} → x A.≈ᴹ A.0ᴹ → f x B.≈ᴹ B.0ᴹ
  x≈0⇒fx≈0 {x} x≈0 = begin⟨ B.≈ᴹ-setoid ⟩
    f x    ≈⟨ ⟦⟧-cong x≈0 ⟩
    f A.0ᴹ ≈⟨ 0ᴹ-homo ⟩
    B.0ᴹ   ∎

  fx≉0⇒x≉0 : ∀ {x} → f x B.≉ᴹ B.0ᴹ → x A.≉ᴹ A.0ᴹ
  fx≉0⇒x≉0 = contraposition x≈0⇒fx≈0

  -- Zero is a unique output of non-trivial (i.e. - ≉ `const 0`) linear map.
  x≉0⇒fx≉0 : ∀ {x} →
                Σ[ (s , y) ∈ S × A ] ((s A.*ₗ x A.≈ᴹ y) × (f y B.≉ᴹ B.0ᴹ)) →
                x A.≉ᴹ A.0ᴹ → f x B.≉ᴹ B.0ᴹ
  x≉0⇒fx≉0 {x} ((s , y) , (s·x≈y , fy≉0)) x≉0 =
    PB.s*v≉0⇒v≉0 s·fx≉0
    where
    y≉0     : y A.≉ᴹ A.0ᴹ
    y≉0     = fx≉0⇒x≉0 fy≉0
    s·fx≉0  : (s B.*ₗ f x) B.≉ᴹ B.0ᴹ
    s·fx≉0 s·fx≈0 =
      fy≉0 ( begin⟨ B.≈ᴹ-setoid ⟩
             f y          ≈⟨ ⟦⟧-cong (A.≈ᴹ-sym s·x≈y) ⟩
             f (s A.*ₗ x) ≈⟨ *ₗ-homo s x ⟩
             s B.*ₗ f x   ≈⟨ s·fx≈0 ⟩
             B.0ᴹ         ∎
           )

  -- f is odd (i.e. - f (-x) ≈ - (f x)).
  fx+f[-x]≈0 : ∀ {x} → f x B.+ᴹ f (A.-ᴹ x) B.≈ᴹ B.0ᴹ
  fx+f[-x]≈0 {x} = begin⟨ B.≈ᴹ-setoid ⟩
    f x B.+ᴹ f (A.-ᴹ x) ≈⟨ B.≈ᴹ-sym (+ᴹ-homo x (A.-ᴹ x)) ⟩
    f (x A.+ᴹ (A.-ᴹ x)) ≈⟨ ⟦⟧-cong (A.-ᴹ‿inverseʳ x) ⟩
    f A.0ᴹ              ≈⟨ 0ᴹ-homo ⟩
    B.0ᴹ                ∎

  f[-x]≈-fx : ∀ {x} → f (A.-ᴹ x) B.≈ᴹ B.-ᴹ f x
  f[-x]≈-fx {x} = B.uniqueʳ‿-ᴹ (f x) (f (A.-ᴹ x)) fx+f[-x]≈0

  -- A non-trivial linear function is injective.
  fx-fy≈0 : ∀ {x y} → f x B.≈ᴹ f y → f x B.+ᴹ (B.-ᴹ f y) B.≈ᴹ B.0ᴹ
  fx-fy≈0 {x} {y} fx≈fy = begin⟨ B.≈ᴹ-setoid ⟩
    f x B.+ᴹ (B.-ᴹ f y) ≈⟨ B.+ᴹ-congˡ (B.-ᴹ‿cong (B.≈ᴹ-sym fx≈fy)) ⟩
    f x B.+ᴹ (B.-ᴹ f x) ≈⟨ B.-ᴹ‿inverseʳ (f x) ⟩
    B.0ᴹ                ∎

  fx-y≈0 : ∀ {x y} → f x B.≈ᴹ f y → f (x A.+ᴹ (A.-ᴹ y)) B.≈ᴹ B.0ᴹ
  fx-y≈0 {x} {y} fx≈fy = begin⟨ B.≈ᴹ-setoid ⟩
    f (x A.+ᴹ (A.-ᴹ y)) ≈⟨ +ᴹ-homo x (A.-ᴹ y) ⟩
    f x B.+ᴹ f (A.-ᴹ y) ≈⟨ B.+ᴹ-congˡ f[-x]≈-fx ⟩
    f x B.+ᴹ (B.-ᴹ f y) ≈⟨ fx-fy≈0 fx≈fy ⟩
    B.0ᴹ                ∎

  module _ {dne : DoubleNegationElimination _} where

    fx≈0⇒x≈0 : ∀ {x} →
               Σ[ (s , y) ∈ S × A ] ((s A.*ₗ x A.≈ᴹ y) × (f y B.≉ᴹ B.0ᴹ)) →
               f x B.≈ᴹ B.0ᴹ → x A.≈ᴹ A.0ᴹ
    fx≈0⇒x≈0 {x} ((s , y) , (s·x≈y , fy≉0)) fx≈0 =
      dne ¬x≉0
      where
      ¬x≉0 : ¬ (x A.≉ᴹ A.0ᴹ)
      ¬x≉0 = λ x≉0 → x≉0⇒fx≉0 ((s , y) , (s·x≈y , fy≉0)) x≉0 fx≈0

    fx≈fy⇒x≈y : ∀ {x y} →
                Σ[ (s , z) ∈ S × A ] ( (s A.*ₗ (x A.+ᴹ A.-ᴹ y) A.≈ᴹ z)
                                     × (f z B.≉ᴹ B.0ᴹ)
                                     ) → f x B.≈ᴹ f y → x A.≈ᴹ y
    fx≈fy⇒x≈y {x} {y} ((s , z) , (s·[x-y]≈z , fz≉0)) fx≈fy =
      begin⟨ A.≈ᴹ-setoid ⟩
      x             ≈⟨ x≈--y ⟩
      A.-ᴹ (A.-ᴹ y) ≈⟨ PA.-ᴹ-involutive y ⟩
      y             ∎
      where
      x-y≈0 : x A.+ᴹ (A.-ᴹ y) A.≈ᴹ A.0ᴹ
      x-y≈0 = fx≈0⇒x≈0 {x = x A.+ᴹ (A.-ᴹ y)}
                        ((s , z) , s·[x-y]≈z , fz≉0)
                        (fx-y≈0 fx≈fy)
      x≈--y : x A.≈ᴹ A.-ᴹ (A.-ᴹ y)
      x≈--y = A.uniqueʳ‿-ᴹ (A.-ᴹ y) x
        ( begin⟨ A.≈ᴹ-setoid ⟩
          A.-ᴹ y A.+ᴹ x ≈⟨ A.+ᴹ-comm (A.-ᴹ y) x ⟩
          x A.+ᴹ A.-ᴹ y ≈⟨ x-y≈0 ⟩
          A.0ᴹ          ∎
        )
