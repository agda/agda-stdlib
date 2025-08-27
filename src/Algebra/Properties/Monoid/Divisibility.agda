------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Properties.Monoid.Divisibility
  {a ℓ} (M : Monoid a ℓ) where

open import Data.Product.Base using (_,_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Structures using (IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive)

open Monoid M

------------------------------------------------------------------------
-- Re-export semigroup divisibility

open import Algebra.Properties.Semigroup.Divisibility semigroup public

------------------------------------------------------------------------
-- Additional properties for right divisibility

infix 4 ε∣ʳ_

ε∣ʳ_ : ∀ x → ε ∣ʳ x
ε∣ʳ x = x , identityʳ x

∣ʳ-refl : Reflexive _∣ʳ_
∣ʳ-refl {x} = ε , identityˡ x

∣ʳ-reflexive : _≈_ ⇒ _∣ʳ_
∣ʳ-reflexive x≈y = ε , trans (identityˡ _) x≈y

∣ʳ-isPreorder : IsPreorder _≈_ _∣ʳ_
∣ʳ-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ∣ʳ-reflexive
  ; trans         = ∣ʳ-trans
  }

∣ʳ-preorder : Preorder a ℓ _
∣ʳ-preorder = record
  { isPreorder = ∣ʳ-isPreorder
  }

------------------------------------------------------------------------
-- Additional properties for left divisibility

infix 4 ε∣ˡ_

ε∣ˡ_ : ∀ x → ε ∣ˡ x
ε∣ˡ x = x , identityˡ x

∣ˡ-refl : Reflexive _∣ˡ_
∣ˡ-refl {x} = ε , identityʳ x

∣ˡ-reflexive : _≈_ ⇒ _∣ˡ_
∣ˡ-reflexive x≈y = ε , trans (identityʳ _) x≈y

∣ˡ-isPreorder : IsPreorder _≈_ _∣ˡ_
∣ˡ-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ∣ˡ-reflexive
  ; trans         = ∣ˡ-trans
  }

∣ˡ-preorder : Preorder a ℓ _
∣ˡ-preorder = record
  { isPreorder = ∣ˡ-isPreorder
  }

------------------------------------------------------------------------
-- Properties of mutual divisibiity

∥-refl : Reflexive _∥_
∥-refl = ∣ʳ-refl , ∣ʳ-refl

∥-reflexive : _≈_ ⇒ _∥_
∥-reflexive x≈y = ∣ʳ-reflexive x≈y , ∣ʳ-reflexive (sym x≈y)

∥-isEquivalence : IsEquivalence _∥_
∥-isEquivalence = record
  { refl  = ∥-refl
  ; sym   = ∥-sym
  ; trans = ∥-trans
  }


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

∣∣-refl = ∥-refl
{-# WARNING_ON_USAGE ∣∣-refl
"Warning: ∣∣-refl was deprecated in v2.3.
Please use ∥-refl instead. "
#-}

∣∣-reflexive = ∥-reflexive
{-# WARNING_ON_USAGE ∣∣-reflexive
"Warning: ∣∣-reflexive was deprecated in v2.3.
Please use ∥-reflexive instead. "
#-}

∣∣-isEquivalence = ∥-isEquivalence
{-# WARNING_ON_USAGE ∣∣-isEquivalence
"Warning: ∣∣-isEquivalence was deprecated in v2.3.
Please use ∥-isEquivalence instead. "
#-}

infix 4 ε∣_
ε∣_ = ε∣ʳ_
{-# WARNING_ON_USAGE ε∣_
"Warning: ε∣_ was deprecated in v2.3.
Please use ε∣ʳ_ instead. "
#-}

∣-refl = ∣ʳ-refl
{-# WARNING_ON_USAGE ∣-refl
"Warning: ∣-refl was deprecated in v2.3.
Please use ∣ʳ-refl instead. "
#-}

∣-reflexive = ∣ʳ-reflexive
{-# WARNING_ON_USAGE ∣-reflexive
"Warning: ∣-reflexive was deprecated in v2.3.
Please use ∣ʳ-reflexive instead. "
#-}

∣-isPreorder = ∣ʳ-isPreorder
{-# WARNING_ON_USAGE ∣ʳ-isPreorder
"Warning: ∣-isPreorder was deprecated in v2.3.
Please use ∣ʳ-isPreorder instead. "
#-}

∣-preorder = ∣ʳ-preorder
{-# WARNING_ON_USAGE ∣-preorder
"Warning: ∣-preorder was deprecated in v2.3.
Please use ∣ʳ-preorder instead. "
#-}
