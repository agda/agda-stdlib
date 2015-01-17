
module Data.Permutation.SymmetricGroup where

open import Algebra

open import Data.Nat 
open import Data.Product

open import Data.Permutation
open import Data.Permutation.Properties

open import Relation.Binary.PropositionalEquality

-- ``Symmetric group Sn on a finite set of n symbols is the group whose elements are all the permutations of the n symbols, and whose group operation is the composition of such permutations, which are treated as bijective functions from the set of symbols to itself'' 

SymmetricGroup : ℕ -> Group _ _
SymmetricGroup n = 
  record {
    Carrier = Permutation n;
    _≈_ = _≡_;
    _∙_ = _∘_;
    ε = id;
    _⁻¹ = _⁻¹;
    isGroup = 
            record { 
              isMonoid = 
              record { 
                isSemigroup = 
                record { 
                  isEquivalence = isEquivalence; 
                  assoc = assoc; 
                  ∙-cong = cong₂ _∘_ };
                identity = id-left , id-right }; 
              inverse = inv-left , inv-right; 
              ⁻¹-cong = cong _⁻¹ } }