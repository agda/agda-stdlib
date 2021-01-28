------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a max operator derived from a spec over a total order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinOp as MinOp

open import Relation.Binary
open import Relation.Binary.Construct.Converse using ()
  renaming (totalOrder to flip)

module Algebra.Construct.NaturalChoice.MaxOp
  {a ℓ₁ ℓ₂} (O : TotalOrder a ℓ₁ ℓ₂) (maxOp : MaxOperator O)
  where

open TotalOrder O renaming (Carrier to A)
open MaxOperator maxOp

-- Max is just min with a flipped order

open MinOp (flip O) (MaxOp⇒MinOp maxOp) public
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
  ; ⊓-isSemilattice           to  ⊔-isSemilattice
  ; ⊓-isMonoid                to  ⊔-isMonoid
  ; ⊓-isSelectiveMagma        to  ⊔-isSelectiveMagma

  ; ⊓-magma                   to  ⊔-magma
  ; ⊓-semigroup               to  ⊔-semigroup
  ; ⊓-commutativeSemigroup    to  ⊔-commutativeSemigroup
  ; ⊓-band                    to  ⊔-band
  ; ⊓-semilattice             to  ⊔-semilattice
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
  ; mono-≤-distrib-⊓   to  mono-≤-distrib-⊔
  )
