------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
open import Algebra.Definitions
open import Data.Product using (_,_; proj₂)

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

leftInv→rightInv : LeftInvertible _≈_ 0# _+_ x → RightInvertible _≈_ 0# _+_ x
leftInv→rightInv {x} (-x , -x+x≈1) = -x , trans (+-comm x -x) -x+x≈1

rightInv→leftInv : RightInvertible _≈_ 0# _+_ x → LeftInvertible _≈_ 0# _+_ x
rightInv→leftInv {x} (-x , x+-x≈1) = -x , trans (+-comm -x x) x+-x≈1

leftInv→Inv : LeftInvertible _≈_ 0# _+_ x → Invertible _≈_ 0# _+_ x
leftInv→Inv left@(-x , -x+x≈1) = -x , -x+x≈1 , leftInv→rightInv left .proj₂

rightInv→Inv : RightInvertible _≈_ 0# _+_ x → Invertible _≈_ 0# _+_ x
rightInv→Inv right@(-x , x+-x≈1) = -x , rightInv→leftInv right .proj₂ , x+-x≈1
