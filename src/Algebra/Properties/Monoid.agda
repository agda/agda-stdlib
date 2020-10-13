------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Monoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid)
import Algebra.Properties.Magma
open import Data.Product using (_,_)
open import Relation.Binary using (Reflexive) 


module Algebra.Properties.Monoid {a ℓ} (M : Monoid a ℓ) where

open Monoid M
open Algebra.Properties.Magma magma using (_∣_)

------------------------------------------------------------------------------
-- Properties of divisibility
------------------------------------------------------------------------------

ε∣ : ∀ x → ε ∣ x 
ε∣ x = (x , sym (identityʳ x))   
                                                                                    
∣refl : Reflexive _∣_                                                               
∣refl {x} =  (ε , sym (identityˡ x)) 
                                                                                    
∣reflexive≈ : ∀ {x y} → x ≈ y → x ∣ y 
∣reflexive≈ {x} {y} x≈y =  (ε , sym (trans (identityˡ x) x≈y)) 
