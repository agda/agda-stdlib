------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for M-types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.M.Bisimilarity where

open import Level
open import Size
open import Codata.Sized.Thunk
open import Codata.Sized.M
open import Data.Container.Core
open import Data.Container.Relation.Binary.Pointwise using (Pointwise; _,_)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∋_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
import Relation.Binary.PropositionalEquality.Core as ≡

data Bisim {s p} (C : Container s p) (i : Size) : Rel (M C ∞) (s ⊔ p) where
  inf : ∀ {t u} → Pointwise C (Thunk^R (Bisim C) i) t u → Bisim C i (inf t) (inf u)

module _ {s p} {C : Container s p} where

  -- unfortunately the proofs are a lot nicer if we do not use the
  -- combinators C.refl, C.sym and C.trans

  refl : ∀ {i} → Reflexive (Bisim C i)
  refl {x = inf t} = inf (≡.refl , λ where p .force → refl)

  sym : ∀ {i} → Symmetric (Bisim C i)
  sym  (inf (≡.refl , f)) = inf (≡.refl , λ where p .force → sym (f p .force))

  trans : ∀ {i} → Transitive (Bisim C i)
  trans (inf (≡.refl , f)) (inf (≡.refl , g)) =
    inf (≡.refl , λ where p .force → trans (f p .force) (g p .force))

  isEquivalence : ∀ {i} → IsEquivalence (Bisim C i)
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : {i : Size} → Setoid (s ⊔ p) (s ⊔ p)
  setoid {i} = record
    { isEquivalence = isEquivalence {i}
    }
