------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for commutative semigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (CommutativeSemigroup)

module Algebra.Properties.CommutativeSemigroup
  {a ℓ} (CS : CommutativeSemigroup a ℓ)
  where

open CommutativeSemigroup CS

open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Data.Product.Base using (_,_)

------------------------------------------------------------------------------
-- Re-export the contents of semigroup

open import Algebra.Properties.Semigroup semigroup public

------------------------------------------------------------------------------
-- Properties

interchange : Interchangable _∙_ _∙_
interchange a b c d = begin
  (a ∙ b) ∙ (c ∙ d)  ≈⟨  assoc a b (c ∙ d) ⟩
  a ∙ (b ∙ (c ∙ d))  ≈˘⟨ ∙-congˡ (assoc b c d) ⟩
  a ∙ ((b ∙ c) ∙ d)  ≈⟨  ∙-congˡ (∙-congʳ (comm b c)) ⟩
  a ∙ ((c ∙ b) ∙ d)  ≈⟨  ∙-congˡ (assoc c b d) ⟩
  a ∙ (c ∙ (b ∙ d))  ≈˘⟨ assoc a c (b ∙ d) ⟩
  (a ∙ c) ∙ (b ∙ d)  ∎

------------------------------------------------------------------------------
-- Permutation laws for _∙_ for three factors.

-- There are five nontrivial permutations.

------------------------------------------------------------------------------
-- Partitions (1,1).

x∙yz≈y∙xz :  ∀ x y z → x ∙ (y ∙ z) ≈ y ∙ (x ∙ z)
x∙yz≈y∙xz x y z = begin
  x ∙ (y ∙ z)    ≈⟨ sym (assoc x y z) ⟩
  (x ∙ y) ∙ z    ≈⟨ ∙-congʳ (comm x y) ⟩
  (y ∙ x) ∙ z    ≈⟨ assoc y x z ⟩
  y ∙ (x ∙ z)    ∎

x∙yz≈z∙yx :  ∀ x y z → x ∙ (y ∙ z) ≈ z ∙ (y ∙ x)
x∙yz≈z∙yx x y z = begin
  x ∙ (y ∙ z)    ≈⟨ ∙-congˡ (comm y z) ⟩
  x ∙ (z ∙ y)    ≈⟨ x∙yz≈y∙xz x z y ⟩
  z ∙ (x ∙ y)    ≈⟨ ∙-congˡ (comm x y) ⟩
  z ∙ (y ∙ x)    ∎

x∙yz≈x∙zy :  ∀ x y z → x ∙ (y ∙ z) ≈ x ∙ (z ∙ y)
x∙yz≈x∙zy _ y z =  ∙-congˡ (comm y z)

x∙yz≈y∙zx :  ∀ x y z → x ∙ (y ∙ z) ≈ y ∙ (z ∙ x)
x∙yz≈y∙zx x y z = begin
  x ∙ (y ∙ z)   ≈⟨ comm x _ ⟩
  (y ∙ z) ∙ x   ≈⟨ assoc y z x ⟩
  y ∙ (z ∙ x)   ∎

x∙yz≈z∙xy :  ∀ x y z → x ∙ (y ∙ z) ≈ z ∙ (x ∙ y)
x∙yz≈z∙xy x y z = begin
  x ∙ (y ∙ z)   ≈⟨ sym (assoc x y z) ⟩
  (x ∙ y) ∙ z   ≈⟨ comm _ z ⟩
  z ∙ (x ∙ y)   ∎

------------------------------------------------------------------------------
-- Partitions (1,2).

-- These permutation laws are proved by composing the proofs for
-- partitions (1,1) with  \p → trans p (sym (assoc _ _ _)).

x∙yz≈yx∙z :  ∀ x y z → x ∙ (y ∙ z) ≈ (y ∙ x) ∙ z
x∙yz≈yx∙z x y z =  trans (x∙yz≈y∙xz x y z) (sym (assoc y x z))

x∙yz≈zy∙x :  ∀ x y z → x ∙ (y ∙ z) ≈ (z ∙ y) ∙ x
x∙yz≈zy∙x x y z =  trans (x∙yz≈z∙yx x y z) (sym (assoc z y x))

x∙yz≈xz∙y :  ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ z) ∙ y
x∙yz≈xz∙y x y z =  trans (x∙yz≈x∙zy x y z) (sym (assoc x z y))

x∙yz≈yz∙x :  ∀ x y z → x ∙ (y ∙ z) ≈ (y ∙ z) ∙ x
x∙yz≈yz∙x x y z =  trans (x∙yz≈y∙zx _ _ _) (sym (assoc y z x))

x∙yz≈zx∙y :  ∀ x y z → x ∙ (y ∙ z) ≈ (z ∙ x) ∙ y
x∙yz≈zx∙y x y z =  trans (x∙yz≈z∙xy x y z) (sym (assoc z x y))

------------------------------------------------------------------------------
-- Partitions (2,1).

-- Their laws are proved by composing proofs for partitions (1,1) with
-- trans (assoc x y z).

xy∙z≈y∙xz :  ∀ x y z → (x ∙ y) ∙ z ≈ y ∙ (x ∙ z)
xy∙z≈y∙xz x y z =  trans (assoc x y z) (x∙yz≈y∙xz x y z)

xy∙z≈z∙yx :  ∀ x y z → (x ∙ y) ∙ z ≈ z ∙ (y ∙ x)
xy∙z≈z∙yx x y z =  trans (assoc x y z) (x∙yz≈z∙yx x y z)

xy∙z≈x∙zy :  ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (z ∙ y)
xy∙z≈x∙zy x y z =  trans (assoc x y z) (x∙yz≈x∙zy x y z)

xy∙z≈y∙zx :  ∀ x y z → (x ∙ y) ∙ z ≈ y ∙ (z ∙ x)
xy∙z≈y∙zx x y z =  trans (assoc x y z) (x∙yz≈y∙zx x y z)

xy∙z≈z∙xy :  ∀ x y z → (x ∙ y) ∙ z ≈ z ∙ (x ∙ y)
xy∙z≈z∙xy x y z =  trans (assoc x y z) (x∙yz≈z∙xy x y z)

------------------------------------------------------------------------------
-- Partitions (2,2).

-- These proofs are by composing with the proofs for (2,1).

xy∙z≈yx∙z :  ∀ x y z → (x ∙ y) ∙ z ≈ (y ∙ x) ∙ z
xy∙z≈yx∙z x y z =  trans (xy∙z≈y∙xz _ _ _) (sym (assoc y x z))

xy∙z≈zy∙x :  ∀ x y z → (x ∙ y) ∙ z ≈ (z ∙ y) ∙ x
xy∙z≈zy∙x x y z =  trans (xy∙z≈z∙yx x y z) (sym (assoc z y x))

xy∙z≈xz∙y :  ∀ x y z → (x ∙ y) ∙ z ≈ (x ∙ z) ∙ y
xy∙z≈xz∙y x y z =  trans (xy∙z≈x∙zy x y z) (sym (assoc x z y))

xy∙z≈yz∙x :  ∀ x y z → (x ∙ y) ∙ z ≈ (y ∙ z) ∙ x
xy∙z≈yz∙x x y z =  trans (xy∙z≈y∙zx x y z) (sym (assoc y z x))

xy∙z≈zx∙y :  ∀ x y z → (x ∙ y) ∙ z ≈ (z ∙ x) ∙ y
xy∙z≈zx∙y x y z =  trans (xy∙z≈z∙xy x y z) (sym (assoc z x y))

------------------------------------------------------------------------------
-- commutative semigroup has Jordan identity

xy∙xx≈x∙yxx : ∀ x y → (x ∙ y) ∙ (x ∙ x) ≈ x ∙ (y ∙ (x ∙ x))
xy∙xx≈x∙yxx x y = assoc x y ((x ∙ x))

------------------------------------------------------------------------------
-- commutative semigroup is left/right/middle semiMedial

semimedialˡ : LeftSemimedial _∙_
semimedialˡ x y z = begin
  (x ∙ x) ∙ (y ∙ z) ≈⟨ assoc x x (y ∙ z) ⟩
  x ∙ (x ∙ (y ∙ z)) ≈⟨ ∙-congˡ (sym (assoc x y z)) ⟩
  x ∙ ((x ∙ y) ∙ z) ≈⟨ ∙-congˡ (∙-congʳ (comm x y)) ⟩
  x ∙ ((y ∙ x) ∙ z) ≈⟨ ∙-congˡ (assoc y x z) ⟩
  x ∙ (y ∙ (x ∙ z)) ≈⟨ sym (assoc x y ((x ∙ z))) ⟩
  (x ∙ y) ∙ (x ∙ z) ∎

semimedialʳ : RightSemimedial _∙_
semimedialʳ x y z = begin
  (y ∙ z) ∙ (x ∙ x) ≈⟨ assoc y z (x ∙ x) ⟩
  y ∙ (z ∙ (x ∙ x)) ≈⟨ ∙-congˡ (sym (assoc z x x)) ⟩
  y ∙ ((z ∙ x) ∙ x) ≈⟨ ∙-congˡ (∙-congʳ (comm z x)) ⟩
  y ∙ ((x ∙ z) ∙ x) ≈⟨ ∙-congˡ (assoc x z x) ⟩
  y ∙ (x ∙ (z ∙ x)) ≈⟨ sym (assoc y x ((z ∙ x))) ⟩
  (y ∙ x) ∙ (z ∙ x) ∎

middleSemimedial : ∀ x y z → (x ∙ y) ∙ (z ∙ x) ≈ (x ∙ z) ∙ (y ∙ x)
middleSemimedial x y z = begin
  (x ∙ y) ∙ (z ∙ x) ≈⟨ assoc x y ((z ∙ x)) ⟩
  x ∙ (y ∙ (z ∙ x)) ≈⟨ ∙-congˡ (sym (assoc y z x)) ⟩
  x ∙ ((y ∙ z) ∙ x) ≈⟨ ∙-congˡ (∙-congʳ (comm y z)) ⟩
  x ∙ ((z ∙ y) ∙ x) ≈⟨ ∙-congˡ ( assoc z y x) ⟩
  x ∙ (z ∙ (y ∙ x)) ≈⟨ sym (assoc x z ((y ∙ x))) ⟩
  (x ∙ z) ∙ (y ∙ x) ∎

semimedial : Semimedial _∙_
semimedial = semimedialˡ , semimedialʳ
