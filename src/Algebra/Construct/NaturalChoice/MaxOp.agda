------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a max operator derived from a spec over a total
-- preorder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.NaturalChoice.Base using (MaxOperator; MaxOp⇒MinOp)
open import Relation.Binary.Bundles using (TotalPreorder)

module Algebra.Construct.NaturalChoice.MaxOp
  {a ℓ₁ ℓ₂} {O : TotalPreorder a ℓ₁ ℓ₂} (maxOp : MaxOperator O)
  where

import Algebra.Construct.NaturalChoice.MinOp as MinOp
open import Algebra.Core using (Op₂)
open import Function.Base using (flip)
open MaxOperator maxOp
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Construct.Flip.EqAndOrd using ()
  renaming (totalPreorder to flipOrder)
open TotalPreorder O renaming (Carrier to A; _≲_ to _≤_)

-- Max is just min with a flipped order

private
  module Min = MinOp (MaxOp⇒MinOp maxOp)

open Min public
  using ()
  renaming
  ( ⊓-cong       to  ⊔-cong
  ; ⊓-congʳ      to  ⊔-congʳ
  ; ⊓-congˡ      to  ⊔-congˡ
  ; ⊓-idem       to  ⊔-idem
  ; ⊓-sel        to  ⊔-sel
  ; ⊓-assoc      to  ⊔-assoc
  ; ⊓-comm       to  ⊔-comm

  ; ⊓-identityˡ  to  ⊔-identityˡ
  ; ⊓-identityʳ  to  ⊔-identityʳ
  ; ⊓-identity   to  ⊔-identity
  ; ⊓-zeroˡ      to  ⊔-zeroˡ
  ; ⊓-zeroʳ      to  ⊔-zeroʳ
  ; ⊓-zero       to  ⊔-zero

  ; ⊓-isMagma                 to  ⊔-isMagma
  ; ⊓-isSemigroup             to  ⊔-isSemigroup
  ; ⊓-isCommutativeSemigroup  to  ⊔-isCommutativeSemigroup
  ; ⊓-isBand                  to  ⊔-isBand
  ; ⊓-isMonoid                to  ⊔-isMonoid
  ; ⊓-isSelectiveMagma        to  ⊔-isSelectiveMagma

  ; ⊓-magma                   to  ⊔-magma
  ; ⊓-semigroup               to  ⊔-semigroup
  ; ⊓-commutativeSemigroup    to  ⊔-commutativeSemigroup
  ; ⊓-band                    to  ⊔-band
  ; ⊓-monoid                  to  ⊔-monoid
  ; ⊓-selectiveMagma          to  ⊔-selectiveMagma

  ; x⊓y≈y⇒y≤x  to x⊔y≈y⇒x≤y
  ; x⊓y≈x⇒x≤y  to x⊔y≈x⇒y≤x
  ; x⊓y≤x      to x≤x⊔y
  ; x⊓y≤y      to x≤y⊔x
  ; x≤y⇒x⊓z≤y  to x≤y⇒x≤y⊔z
  ; x≤y⇒z⊓x≤y  to x≤y⇒x≤z⊔y
  ; x≤y⊓z⇒x≤y  to x⊔y≤z⇒x≤z
  ; x≤y⊓z⇒x≤z  to x⊔y≤z⇒y≤z

  ; ⊓-glb              to  ⊔-lub
  ; ⊓-triangulate      to  ⊔-triangulate
  ; ⊓-mono-≤           to  ⊔-mono-≤
  ; ⊓-monoˡ-≤          to  ⊔-monoˡ-≤
  ; ⊓-monoʳ-≤          to  ⊔-monoʳ-≤
  )

mono-≤-distrib-⊔ : ∀ {f} → f Preserves _≈_ ⟶ _≈_ → f Preserves _≤_ ⟶ _≤_ →
                   ∀ x y → f (x ⊔ y) ≈ f x ⊔ f y
mono-≤-distrib-⊔ cong pres = Min.mono-≤-distrib-⊓ cong pres
