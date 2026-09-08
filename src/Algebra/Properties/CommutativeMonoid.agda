------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)

module Algebra.Properties.CommutativeMonoid
  {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ)
  where

open import Data.Product.Base using (_,_; proj₂)

open CommutativeMonoid commutativeMonoid
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

open import Algebra.Definitions _≈_
  using (LeftInvertible; RightInvertible; Invertible)

private variable
  x : Carrier


------------------------------------------------------------------------
-- Re-export properties of commutative semigroups

open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup public

------------------------------------------------------------------------
-- Additional properties

invertibleˡ⇒invertibleʳ : LeftInvertible 0# _+_ x → RightInvertible 0# _+_ x
invertibleˡ⇒invertibleʳ {x} (-x , -x+x≈1) = -x , trans (+-comm x -x) -x+x≈1

invertibleʳ⇒invertibleˡ : RightInvertible 0# _+_ x → LeftInvertible 0# _+_ x
invertibleʳ⇒invertibleˡ {x} (-x , x+-x≈1) = -x , trans (+-comm -x x) x+-x≈1

invertibleˡ⇒invertible : LeftInvertible 0# _+_ x → Invertible 0# _+_ x
invertibleˡ⇒invertible left@(-x , -x+x≈1) = -x , -x+x≈1 , invertibleˡ⇒invertibleʳ left .proj₂

invertibleʳ⇒invertible : RightInvertible 0# _+_ x → Invertible 0# _+_ x
invertibleʳ⇒invertible right@(-x , x+-x≈1) = -x , invertibleʳ⇒invertibleˡ right .proj₂ , x+-x≈1
