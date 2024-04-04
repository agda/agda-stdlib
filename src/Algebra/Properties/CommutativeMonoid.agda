------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Algebra.Definitions using (LeftInvertible; RightInvertible; Invertible)
open import Data.Product.Base using (_,_; proj₂)

module Algebra.Properties.CommutativeMonoid
  {g₁ g₂} (M : CommutativeMonoid g₁ g₂) where

open CommutativeMonoid M
  renaming
  ( ε         to 0#
  ; _∙_       to _+_
  ; ∙-cong    to +-cong
  ; ∙-congˡ   to +-congˡ
  ; ∙-congʳ   to +-congʳ
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; comm      to +-comm
  )

private variable
  x : Carrier

invertibleˡ⇒invertibleʳ : LeftInvertible _≈_ 0# _+_ x → RightInvertible _≈_ 0# _+_ x
invertibleˡ⇒invertibleʳ {x} (-x , -x+x≈1) = -x , trans (+-comm x -x) -x+x≈1

invertibleʳ⇒invertibleˡ : RightInvertible _≈_ 0# _+_ x → LeftInvertible _≈_ 0# _+_ x
invertibleʳ⇒invertibleˡ {x} (-x , x+-x≈1) = -x , trans (+-comm -x x) x+-x≈1

invertibleˡ⇒invertible : LeftInvertible _≈_ 0# _+_ x → Invertible _≈_ 0# _+_ x
invertibleˡ⇒invertible left@(-x , -x+x≈1) = -x , -x+x≈1 , invertibleˡ⇒invertibleʳ left .proj₂

invertibleʳ⇒invertible : RightInvertible _≈_ 0# _+_ x → Invertible _≈_ 0# _+_ x
invertibleʳ⇒invertible right@(-x , x+-x≈1) = -x , invertibleʳ⇒invertibleˡ right .proj₂ , x+-x≈1
