------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for M-types
------------------------------------------------------------------------

module Codata.M.Bisimilarity where

open import Level
open import Size
open import Codata.Thunk
open import Codata.M
open import Data.Container.Core
import Data.Container as C
open import Data.Product using (_,_)
open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

data Bisim {s p} (C : Container s p) (i : Size) : Rel (M C ∞) (s ⊔ p) where
  inf : ∀ {t u} → C.Eq C (Thunk^R (Bisim C) i) t u → Bisim C i (inf t) (inf u)

module _ {s p} {C : Container s p} where

  -- unfortunately the proofs are a lot nicer if we do not use the combinators
  -- C.refl, C.sym and C.trans

  refl : ∀ {i} → Reflexive (Bisim C i)
  refl {x = inf t} = inf (P.refl , λ where p .force → refl)

  sym : ∀ {i} → Symmetric (Bisim C i)
  sym  (inf (P.refl , f)) = inf (P.refl , λ where p .force → sym (f p .force))

  trans : ∀ {i} → Transitive (Bisim C i)
  trans (inf (P.refl , f)) (inf (P.refl , g)) =
    inf (P.refl , λ where p .force → trans (f p .force) (g p .force))

  isEquivalence : ∀ {i} → IsEquivalence (Bisim C i)
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : {i : Size} → Setoid (s ⊔ p) (s ⊔ p)
  setoid {i} = record { isEquivalence = isEquivalence {i} }
