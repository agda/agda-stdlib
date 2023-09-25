------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for types of functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

-- Note that these bundles differ from those found elsewhere in other
-- library hierarchies as they take Setoids as parameters. This is
-- because a function is of no use without knowing what its domain and
-- codomain is, as well which equalities are being considered over them.
-- One consequence of this is that they are not built from the
-- definitions found in `Function.Structures` as is usually the case in
-- other library hierarchies, as this would duplicate the equality
-- axioms.

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Dependent.Bundles where

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid bundles
------------------------------------------------------------------------

module _
  (From : Setoid a ℓ₁)
  (To : IndexedSetoid (Setoid.Carrier From) b ℓ₂)
  where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open IndexedSetoid To using () renaming (Carrier to B; _≈_ to _≈₂_)

------------------------------------------------------------------------
-- Bundles with one element

  -- Called `Func` rather than `Function` in order to avoid clashing
  -- with the top-level module.
  record Func : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to   : (x : A) → B x
      cong : ∀ {x y} → x ≈₁ y → to x ≈₂ to y
