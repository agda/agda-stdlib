------------------------------------------------------------------------
-- The Agda standard library
--
-- More Induced structures
------------------------------------------------------------------------


module Relation.Binary.InducedStructures where

open import Relation.Binary
open import Data.Product
open import Function
open import Relation.Binary.NonStrictToStrict

-- Every reflexive and transitive binary relation induces
-- a setoid, a preorder, and a poset.

module _ {a r} {A     : Set a}
               (_R_   : A → A → Set r)
               (refl  : Reflexive _R_)
               (trans : Transitive _R_) where

  InducedSetoid : Setoid _ _
  InducedSetoid = record
    { _≈_           = λ x y → x R y × y R x
    ; isEquivalence = record
      { refl  = refl , refl
      ; sym   = swap
      ; trans = zip trans (flip trans)
      }
    }

  InducedPreorder : Preorder _ _ _
  InducedPreorder = record
    { _∼_        = _R_
    ; isPreorder = record
      { isEquivalence = Setoid.isEquivalence InducedSetoid
      ; reflexive     = proj₁
      ; trans         = trans
      }
    }

  InducedPoset : Poset _ _ _
  InducedPoset = record
    { _≤_            = _R_
    ; isPartialOrder = record
      { isPreorder = Preorder.isPreorder InducedPreorder
      ; antisym    = _,_
      }
    }

  InducedStrictPartialOrder : StrictPartialOrder _ _ _
  InducedStrictPartialOrder = record
   { isStrictPartialOrder = <-isStrictPartialOrder _≈_ _R_ isPartialOrder }
   where open Poset InducedPoset
