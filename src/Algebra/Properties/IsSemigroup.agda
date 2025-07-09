------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₂)
open import Algebra.Structures.IsSemigroup using (IsSemigroup)

module Algebra.Properties.IsSemigroup
  {a ℓ} {A} {_≈_} {_∙_} (isSemigroup : IsSemigroup {a = a} {ℓ = ℓ} {A = A} _≈_ _∙_)
  where

open import Algebra.Definitions _≈_
  using (Alternative; LeftAlternative; RightAlternative; Flexible)
open import Algebra.Structures.IsMagma _≈_
  using (IsMagma; IsAlternativeMagma; IsFlexibleMagma)
open import Data.Product.Base using (_,_)

open IsSemigroup isSemigroup
  using (setoid; trans ; refl; sym; assoc; ∙-cong; ∙-congˡ; ∙-congʳ; isMagma)
open import Algebra.Properties.IsMagma isMagma

private
  variable
    u v w x y z : A

x∙yz≈xy∙z : ∀ x y z → (x ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ z)
x∙yz≈xy∙z x y z = sym (assoc x y z)

alternativeˡ : LeftAlternative _∙_
alternativeˡ x y = assoc x x y

alternativeʳ : RightAlternative _∙_
alternativeʳ x y = sym (assoc x y y)

alternative : Alternative _∙_
alternative = alternativeˡ , alternativeʳ

flexible : Flexible _∙_
flexible x y = assoc x y x

isAlternativeMagma : IsAlternativeMagma _∙_
isAlternativeMagma = record { isMagma = isMagma ; alter = alternative }

isFlexibleMagma : IsFlexibleMagma _∙_
isFlexibleMagma = record { isMagma = isMagma ; flex = flexible }

