------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Consequences.Base
  {a} {A : Set a} where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions
  using (Selective; Idempotent; SelfInverse; Involutive
        ; _-AlmostLeftCancellative_; Except_-LeftCancellative_
        ; _-AlmostRightCancellative_; Except_-RightCancellative_)
open import Data.Sum.Base using (inj₁; inj₂; reduce; [_,_]′)
open import Function.Base using (id; const; flip)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Nullary.Recomputable using (¬-recompute)
open import Relation.Unary using (Pred; Decidable)


module _ {ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) where

  sel⇒idem : Selective _≈_ _•_ → Idempotent _≈_ _•_
  sel⇒idem sel x = reduce (sel x x)

module _ {p ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ)
         {P : Pred A p} where

  almost⇒exceptˡ : _-AlmostLeftCancellative_ _≈_ P _•_ →
                   Except_-LeftCancellative_ _≈_ P _•_
  almost⇒exceptˡ cancel x y z {{¬px}} =
    [ flip contradiction (¬-recompute ¬px) , (λ cancel → cancel y z) ]′ (cancel x)

  almost⇒exceptʳ : _-AlmostRightCancellative_ _≈_ P _•_ →
                   Except_-RightCancellative_ _≈_ P _•_
  almost⇒exceptʳ cancel x y z {{¬px}} =
    [ flip contradiction (¬-recompute ¬px) , (λ cancel → cancel y z) ]′ (cancel x)

module _ {p ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ)
         {P : Pred A p} (dec : Decidable P) where

  except⇒almostˡ : Except_-LeftCancellative_ _≈_ P _•_ →
                   _-AlmostLeftCancellative_ _≈_ P _•_
  except⇒almostˡ cancel x with dec x
  ... | yes px = inj₁ px
  ... | no ¬px = inj₂ (λ y z → cancel x y z {{¬px}})

  except⇒almostʳ : Except_-RightCancellative_ _≈_ P _•_ →
                   _-AlmostRightCancellative_ _≈_ P _•_
  except⇒almostʳ cancel x with dec x
  ... | yes px = inj₁ px
  ... | no ¬px = inj₂ λ y z → cancel x y z {{¬px}}

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
