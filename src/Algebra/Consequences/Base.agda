------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Consequences.Base
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
  using (Congruent₂; LeftCongruent; RightCongruent
        ; Selective; Idempotent; SelfInverse; Involutive
        ; _AlmostLeftCancellative′_; Except_LeftCancellative_
        ; _AlmostRightCancellative′_; Except_RightCancellative_)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′; reduce)
open import Function.Base using (flip)
open import Level using (Level)
open import Relation.Binary.Consequences
  using (mono₂⇒monoˡ; mono₂⇒monoʳ)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Nullary.Recomputable using (¬-recompute)
open import Relation.Unary using (Pred; Decidable)


private
  variable
    f : Op₁ A
    _∙_ : Op₂ A


------------------------------------------------------------------------
-- Congruence

module Congruence (cong : Congruent₂ _∙_) (refl : Reflexive _≈_)
  where

  ∙-congˡ : LeftCongruent _∙_
  ∙-congˡ {x} = mono₂⇒monoˡ _ _≈_ _≈_ (refl {x = x}) cong x

  ∙-congʳ : RightCongruent _∙_
  ∙-congʳ {x} = mono₂⇒monoʳ _≈_ _ _≈_ (refl {x = x}) cong x

-------------------------------------------------------------------------
-- Selective

sel⇒idem : Selective _∙_ → Idempotent _∙_
sel⇒idem sel x = reduce (sel x x)

------------------------------------------------------------------------
-- SelfInverse

reflexive∧selfInverse⇒involutive : Reflexive _≈_ → SelfInverse f →
                                   Involutive f
reflexive∧selfInverse⇒involutive refl inv _ = inv refl

module _ {p} {P : Pred A p} where

  almost⇒exceptˡ : _AlmostLeftCancellative′_ P _∙_ →
                   Except_LeftCancellative_ P _∙_
  almost⇒exceptˡ cancel x y z {{¬px}} =
    [ flip contradiction (¬-recompute ¬px) , (λ cancel → cancel y z) ]′ (cancel x)

  almost⇒exceptʳ : _AlmostRightCancellative′_ P _∙_ →
                   Except_RightCancellative_ P _∙_
  almost⇒exceptʳ cancel x y z {{¬px}} =
    [ flip contradiction (¬-recompute ¬px) , (λ cancel → cancel y z) ]′ (cancel x)

module _ {p} {_∙_ : Op₂ A} (_≈_ : Rel A ℓ)
         {P : Pred A p} (dec : Decidable P) where

  except⇒almostˡ : Except_LeftCancellative_ P _∙_ →
                   _AlmostLeftCancellative′_ P _∙_
  except⇒almostˡ cancel x with dec x
  ... | yes px = inj₁ px
  ... | no ¬px = inj₂ (λ y z → cancel x y z {{¬px}})

  except⇒almostʳ : Except_RightCancellative_ P _∙_ →
                   _AlmostRightCancellative′_ P _∙_
  except⇒almostʳ cancel x with dec x
  ... | yes px = inj₁ px
  ... | no ¬px = inj₂ λ y z → cancel x y z {{¬px}}


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
