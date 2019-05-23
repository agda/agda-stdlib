------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)

module Algebra.Properties.Semigroup {ℓ ℓ=} (H : Semigroup ℓ ℓ=) where

open import Algebra.FunctionProperties using (Commutative)
import      Relation.Binary.Properties.Setoid as OfSetoid
open import Function using (_$_)
import      Relation.Binary.EqReasoning as EqR

open Semigroup H using (_≈_; refl; sym; trans; _∙_; assoc; ∙-congˡ; ∙-congʳ;
                                                                    setoid)
open OfSetoid setoid public

open EqR setoid


module _ (comm : Commutative _≈_ _∙_)
  where
  -- Several lemmata for a commutative _∙_.

  -- Permutation laws for _∙_ for three factors.

  ----------------------------------------------------------------------------
  -- Partitions (1,1).
  -- There are five nontrivial permutations.
  ----------------------------------------------------------------------------

  x∙yz≈y∙xz :  ∀ {x y z} → x ∙ (y ∙ z) ≈ y ∙ (x ∙ z)    -- x-y
  x∙yz≈y∙xz {x} {y} {z} = begin
    x ∙ (y ∙ z)    ≈⟨ sym (assoc x y z) ⟩
    (x ∙ y) ∙ z    ≈⟨ ∙-congʳ (comm x y) ⟩
    (y ∙ x) ∙ z    ≈⟨ assoc y x z ⟩
    y ∙ (x ∙ z)    ∎

  x∙yz≈z∙yx :  ∀ {x y z} → x ∙ (y ∙ z) ≈ z ∙ (y ∙ x)    -- x-z
  x∙yz≈z∙yx {x} {y} {z} = begin
    x ∙ (y ∙ z)    ≈⟨ ∙-congˡ (comm y z) ⟩
    x ∙ (z ∙ y)    ≈⟨ x∙yz≈y∙xz ⟩
    z ∙ (x ∙ y)    ≈⟨ ∙-congˡ (comm x y) ⟩
    z ∙ (y ∙ x)    ∎

  x∙yz≈x∙zy :  ∀ {x y z} → x ∙ (y ∙ z) ≈ x ∙ (z ∙ y)    -- y-z
  x∙yz≈x∙zy {_} {y} {z} =  ∙-congˡ (comm y z)

  x∙yz≈y∙zx :  ∀ {x y z} → x ∙ (y ∙ z) ≈ y ∙ (z ∙ x)    -- cycle
  x∙yz≈y∙zx {x} {y} {z} = begin
    x ∙ (y ∙ z)   ≈⟨ comm x _ ⟩
    (y ∙ z) ∙ x   ≈⟨ assoc y z x ⟩
    y ∙ (z ∙ x)   ∎

  x∙yz≈z∙xy :  ∀ {x y z} → x ∙ (y ∙ z) ≈ z ∙ (x ∙ y)
  x∙yz≈z∙xy {x} {y} {z} = begin
    x ∙ (y ∙ z)   ≈⟨ sym (assoc x y z) ⟩
    (x ∙ y) ∙ z   ≈⟨ comm _ z ⟩
    z ∙ (x ∙ y)   ∎

  ----------------------------------------------------------------------------
  -- Partitions (1,2).
  -- These permutation laws are proved by composing the proofs for
  -- partitions (1,1) with  \p → trans p (sym (assoc _ _ _)).
  ----------------------------------------------------------------------------
  x∙yz≈xy∙z =  \{x y z} → sym (assoc x y z)

  x∙yz≈yx∙z :  ∀ {x y z} → x ∙ (y ∙ z) ≈ (y ∙ x) ∙ z
  x∙yz≈yx∙z {x} {y} {z} =  trans x∙yz≈y∙xz (sym (assoc y x z))

  x∙yz≈zy∙x :  ∀ {x y z} → x ∙ (y ∙ z) ≈ (z ∙ y) ∙ x
  x∙yz≈zy∙x {x} {y} {z} =  trans x∙yz≈z∙yx (sym (assoc z y x))

  x∙yz≈xz∙y :  ∀ {x y z} → x ∙ (y ∙ z) ≈ (x ∙ z) ∙ y
  x∙yz≈xz∙y {x} {y} {z} =  trans x∙yz≈x∙zy (sym (assoc x z y))

  x∙yz≈yz∙x :  ∀ {x y z} → x ∙ (y ∙ z) ≈ (y ∙ z) ∙ x
  x∙yz≈yz∙x {x} {y} {z} =  trans x∙yz≈y∙zx (sym (assoc y z x))

  x∙yz≈zx∙y :  ∀ {x y z} → x ∙ (y ∙ z) ≈ (z ∙ x) ∙ y
  x∙yz≈zx∙y {x} {y} {z} =  trans x∙yz≈z∙xy (sym (assoc z x y))


  ----------------------------------------------------------------------------
  -- Partitions (2,1).
  -- Their laws are proved by composing proofs for partitions (1,1) with
  -- trans (assoc x y z).
  ----------------------------------------------------------------------------

  -- xy∙z≈x∙yz =  assoc _ _ _

  xy∙z≈y∙xz :  ∀ {x y z} → (x ∙ y) ∙ z ≈ y ∙ (x ∙ z)
  xy∙z≈y∙xz {x} {y} {z} =  trans (assoc x y z) x∙yz≈y∙xz

  xy∙z≈z∙yx :  ∀ {x y z} → (x ∙ y) ∙ z ≈ z ∙ (y ∙ x)
  xy∙z≈z∙yx {x} {y} {z} =  trans (assoc x y z) x∙yz≈z∙yx

  xy∙z≈x∙zy :  ∀ {x y z} → (x ∙ y) ∙ z ≈ x ∙ (z ∙ y)
  xy∙z≈x∙zy {x} {y} {z} =  trans (assoc x y z) x∙yz≈x∙zy

  xy∙z≈y∙zx =  \{x y z} → trans (assoc x y z) x∙yz≈y∙zx
  xy∙z≈z∙xy =  \{x y z} → trans (assoc x y z) x∙yz≈z∙xy

  ----------------------------------------------------------------------------
  -- Partitions (2,2).
  -- These proofs are by composing with the proofs for (2,1).
  ----------------------------------------------------------------------------

  xy∙z≈yx∙z =  \{x y z} → trans xy∙z≈y∙xz (sym (assoc y x z))

  xy∙z≈zy∙x :  ∀ {x y z} → (x ∙ y) ∙ z ≈ (z ∙ y) ∙ x
  xy∙z≈zy∙x {x} {y} {z} =  trans xy∙z≈z∙yx (sym (assoc z y x))

  xy∙z≈xz∙y :  ∀ {x y z} → (x ∙ y) ∙ z ≈ (x ∙ z) ∙ y
  xy∙z≈xz∙y {x} {y} {z} =  trans xy∙z≈x∙zy (sym (assoc x z y))

  xy∙z≈yz∙x :  ∀ {x y z} → (x ∙ y) ∙ z ≈ (y ∙ z) ∙ x
  xy∙z≈yz∙x {x} {y} {z} =  trans xy∙z≈y∙zx (sym (assoc y z x))

  xy∙z≈zx∙y :  ∀ {x y z} → (x ∙ y) ∙ z ≈ (z ∙ x) ∙ y
  xy∙z≈zx∙y {x} {y} {z} =  trans xy∙z≈z∙xy (sym (assoc z x y))
