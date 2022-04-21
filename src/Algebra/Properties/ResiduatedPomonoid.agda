------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right-residuated partially ordered monoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Ordered.Residuated using (ResiduatedPomonoid)

module Algebra.Properties.ResiduatedPomonoid
  {a ℓ₁ ℓ₂} (rp : ResiduatedPomonoid a ℓ₁ ℓ₂)
  where

import Algebra.Properties.RightResiduatedPomonoid as RightResiduatedPomonoid

open ResiduatedPomonoid rp

open RightResiduatedPomonoid rightResiduatedPomonoid public
  renaming
    ( unit-ε             to \\-unit-ε
    ; isGaloisConnection to ∙-\\-isGaloisConnection
    ; galoisConnection   to ∙-\\-galoisConnection
    )

open RightResiduatedPomonoid leftResiduatedPomonoid public
  using () renaming
    ( \\-cong            to //-cong
    ; ∙-\\-assoc         to //-∙-assoc
    ; \\-∙-assoc         to ∙-//-assoc
    ; \\-identityˡ       to //-identityʳ
    ; unit-ε             to //-unit-ε
    ; isGaloisConnection to ∙-//-isGaloisConnection
    ; galoisConnection   to ∙-//-galoisConnection
    )
