------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

import Algebra.Module.Properties            as ModuleProperties
import Algebra.Module.Morphism.Structures   as MorphismStructures

open import Algebra                   using (CommutativeRing)
open import Algebra.Module            using (Module)
open import Level                     using (Level)

module Algebra.Module.Morphism.ModuleHomomorphism
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (modA modB  : Module ring m ℓm)
  (open Module modA using () renaming (Carrierᴹ to A))
  (open Module modB using () renaming (Carrierᴹ to B))
  {f : A → B}
  (open MorphismStructures.ModuleMorphisms modA modB)
  (isModuleHomomorphism : IsModuleHomomorphism f)
  where

open import Axiom.DoubleNegationElimination
open import Data.Product
open import Relation.Binary.Reasoning.MultiSetoid
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

module A = Module modA
module B = Module modB
module PA = ModuleProperties modA
module PB = ModuleProperties modB
open CommutativeRing ring renaming (Carrier to S)

open IsModuleHomomorphism isModuleHomomorphism

-- Some of the lemmas below only hold for continously scalable,
-- non-trivial functions, i.e., f x = f (s y) and f ≠ const 0.
-- This is a handy abbreviation for that rather verbose term.
NonTrivial : A → Set (r Level.⊔ m Level.⊔ ℓm)
NonTrivial x = ∃₂ λ s y → (s A.*ₗ x A.≈ᴹ y) × (f y B.≉ᴹ B.0ᴹ)

x≈0⇒fx≈0 : ∀ {x} → x A.≈ᴹ A.0ᴹ → f x B.≈ᴹ B.0ᴹ
x≈0⇒fx≈0 {x} x≈0 = begin⟨ B.≈ᴹ-setoid ⟩
  f x    ≈⟨ ⟦⟧-cong x≈0 ⟩
  f A.0ᴹ ≈⟨ 0ᴹ-homo ⟩
  B.0ᴹ   ∎

fx≉0⇒x≉0 : ∀ {x} → f x B.≉ᴹ B.0ᴹ → x A.≉ᴹ A.0ᴹ
fx≉0⇒x≉0 = contraposition x≈0⇒fx≈0

-- Zero is a unique output of non-trivial (i.e. - ≉ `const 0`) linear map.
x≉0⇒f[x]≉0 : ∀ {x} → NonTrivial x → x A.≉ᴹ A.0ᴹ → f x B.≉ᴹ B.0ᴹ
x≉0⇒f[x]≉0 {x} (s , y , s·x≈y , fy≉0) x≉0 =
  PB.x*y≉0⇒y≉0 ( λ s·fx≈0 → fy≉0 ( begin⟨ B.≈ᴹ-setoid ⟩
                   f y          ≈⟨ ⟦⟧-cong (A.≈ᴹ-sym s·x≈y) ⟩
                   f (s A.*ₗ x) ≈⟨ *ₗ-homo s x ⟩
                   s B.*ₗ f x   ≈⟨ s·fx≈0 ⟩
                   B.0ᴹ         ∎ )
               )

-- f is odd (i.e. - f (-x) ≈ - (f x)).
fx+f[-x]≈0 : (x : A) → f x B.+ᴹ f (A.-ᴹ x) B.≈ᴹ B.0ᴹ
fx+f[-x]≈0 x = begin⟨ B.≈ᴹ-setoid ⟩
  f x B.+ᴹ f (A.-ᴹ x) ≈⟨ B.≈ᴹ-sym (+ᴹ-homo x (A.-ᴹ x)) ⟩
  f (x A.+ᴹ (A.-ᴹ x)) ≈⟨ ⟦⟧-cong (A.-ᴹ‿inverseʳ x) ⟩
  f A.0ᴹ              ≈⟨ 0ᴹ-homo ⟩
  B.0ᴹ                ∎

f[-x]≈-fx : (x : A) → f (A.-ᴹ x) B.≈ᴹ B.-ᴹ f x
f[-x]≈-fx x = B.uniqueʳ‿-ᴹ (f x) (f (A.-ᴹ x)) (fx+f[-x]≈0 x)

-- A non-trivial linear function is injective.
fx≈fy⇒fx-fy≈0 : ∀ {x y} → f x B.≈ᴹ f y → f x B.+ᴹ (B.-ᴹ f y) B.≈ᴹ B.0ᴹ
fx≈fy⇒fx-fy≈0 {x} {y} fx≈fy = begin⟨ B.≈ᴹ-setoid ⟩
  f x B.+ᴹ (B.-ᴹ f y) ≈⟨ B.+ᴹ-congˡ (B.-ᴹ‿cong (B.≈ᴹ-sym fx≈fy)) ⟩
  f x B.+ᴹ (B.-ᴹ f x) ≈⟨ B.-ᴹ‿inverseʳ (f x) ⟩
  B.0ᴹ                ∎

fx≈fy⇒f[x-y]≈0 : ∀ {x y} → f x B.≈ᴹ f y → f (x A.+ᴹ (A.-ᴹ y)) B.≈ᴹ B.0ᴹ
fx≈fy⇒f[x-y]≈0 {x} {y} fx≈fy = begin⟨ B.≈ᴹ-setoid ⟩
  f (x A.+ᴹ (A.-ᴹ y)) ≈⟨ +ᴹ-homo x (A.-ᴹ y) ⟩
  f x B.+ᴹ f (A.-ᴹ y) ≈⟨ B.+ᴹ-congˡ (f[-x]≈-fx y) ⟩
  f x B.+ᴹ (B.-ᴹ f y) ≈⟨ fx≈fy⇒fx-fy≈0 fx≈fy ⟩
  B.0ᴹ                ∎

module _ {dne : DoubleNegationElimination _} where

  fx≈0⇒x≈0 : ∀ {x} → NonTrivial x → f x B.≈ᴹ B.0ᴹ → x A.≈ᴹ A.0ᴹ
  fx≈0⇒x≈0 {x} (s , y , s·x≈y , fy≉0) fx≈0 =
    dne ¬x≉0
    where
    ¬x≉0 : ¬ (x A.≉ᴹ A.0ᴹ)
    ¬x≉0 = λ x≉0 → x≉0⇒f[x]≉0 (s , y , s·x≈y , fy≉0) x≉0 fx≈0

  inj-lm : ∀ {x y} →
           (∃₂ λ s z → ((s A.*ₗ (x A.+ᴹ A.-ᴹ y) A.≈ᴹ z) × (f z B.≉ᴹ B.0ᴹ))) →
           f x B.≈ᴹ f y → x A.≈ᴹ y
  inj-lm {x} {y} (s , z , s·[x-y]≈z , fz≉0) fx≈fy =
    begin⟨ A.≈ᴹ-setoid ⟩
    x             ≈⟨ x≈--y ⟩
    A.-ᴹ (A.-ᴹ y) ≈⟨ PA.-ᴹ-involutive y ⟩
    y             ∎
    where
    x-y≈0 : x A.+ᴹ (A.-ᴹ y) A.≈ᴹ A.0ᴹ
    x-y≈0 = fx≈0⇒x≈0 (s , z , s·[x-y]≈z , fz≉0) (fx≈fy⇒f[x-y]≈0 fx≈fy)
    x≈--y : x A.≈ᴹ A.-ᴹ (A.-ᴹ y)
    x≈--y = A.uniqueʳ‿-ᴹ (A.-ᴹ y) x
      ( begin⟨ A.≈ᴹ-setoid ⟩
        A.-ᴹ y A.+ᴹ x ≈⟨ A.+ᴹ-comm (A.-ᴹ y) x ⟩
        x A.+ᴹ A.-ᴹ y ≈⟨ x-y≈0 ⟩
        A.0ᴹ          ∎
      )
