------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Consequences.Base
  {a} {A : Set a} where

open import Algebra.Core
open import Algebra.Definitions
open import Data.Sum.Base
open import Function.Base using (const)
open import Relation.Binary.Core
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Pred; Decidable)


module _ {ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) where

  sel⇒idem : Selective _≈_ _•_ → Idempotent _≈_ _•_
  sel⇒idem sel x = reduce (sel x x)

module _ {p ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) (P : Pred A p) where

  almost⇒exceptˡ : _-AlmostLeftCancellative_ _≈_ P _•_ →
                   Except_-LeftCancellative_ _≈_ P _•_
  almost⇒exceptˡ cancel = [ contradiction , const ]′ (cancel _)

  almost⇒exceptʳ : _-AlmostRightCancellative_ _≈_ P _•_ →
                   Except_-RightCancellative_ _≈_ P _•_
  almost⇒exceptʳ cancel = [ contradiction , const ]′ (cancel _)

module _ {p ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ)
         {P : Pred A p} (dec : Decidable P) where

  except⇒almostˡ : Except_-LeftCancellative_ _≈_ P _•_ →
                   _-AlmostLeftCancellative_ _≈_ P _•_
  except⇒almostˡ cancelˡ x with dec x
  ... | yes px = inj₁ px
  ... | no ¬px = inj₂ (cancelˡ ¬px)

  except⇒almostʳ : Except_-RightCancellative_ _≈_ P _•_ →
                   _-AlmostRightCancellative_ _≈_ P _•_
  except⇒almostʳ cancelʳ x with dec x
  ... | yes px = inj₁ px
  ... | no ¬px = inj₂ (cancelʳ ¬px)

module _ {ℓ} {f : Op₁ A} (_≈_ : Rel A ℓ) where

  reflexive∧selfInverse⇒involutive : Reflexive _≈_ →
                                     SelfInverse _≈_ f →
                                     Involutive _≈_ f
  reflexive∧selfInverse⇒involutive refl inv _ = inv refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

reflexive+selfInverse⇒involutive = reflexive∧selfInverse⇒involutive
{-# WARNING_ON_USAGE reflexive+selfInverse⇒involutive
"Warning: reflexive+selfInverse⇒involutive was deprecated in v2.0.
Please use reflexive∧selfInverse⇒involutive instead."
#-}
