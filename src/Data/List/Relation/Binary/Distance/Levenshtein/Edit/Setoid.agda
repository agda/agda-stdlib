------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: the Edit relation and its properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Silence user warnings because we import an internal module
{-# OPTIONS --warning=noUserWarning #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Distance.Levenshtein.Edit.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Nat.Base using (ℕ; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (0≢1+n; 1+n≰n; ≤-reflexive; ≤-trans; +-suc; n≤1+n; +-monoʳ-≤)
open import Data.Product.Base using (∃; _×_; _,_)

open import Level using (Level; _⊔_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary.Negation using (¬_)

private module S = Setoid S
open S
  renaming (Carrier to A)
  using (_≈_)

private
  variable
    x y : A
    xs ys zs : List A
    k l m : ℕ

------------------------------------------------------------------------
-- Re-exporting the core definitions

open import Data.List.Relation.Binary.Distance.Levenshtein.Edit.Heterogeneous
  as Het using
    ( done
    ; delL
    ; delR
    ; skip
    ; swap
    ; cast
    )
  public

Edit : (xs ys : List A) → ℕ → Set (c ⊔ ℓ)
Edit = Het.Edit _≈_

-- smart constructor
same : Edit xs ys k → Edit (x ∷ xs) (x ∷ ys) k
same = skip S.refl

-- specialised re-exports
fromPointwise = Het.fromPointwise {R = _≈_}
toPointwise = Het.toPointwise {R = _≈_}
edit-[]ˡ = Het.edit-[]ˡ {R = _≈_}
edit-[]ʳ = Het.edit-[]ʳ {R = _≈_}

------------------------------------------------------------------------
-- The relation is a pseudo-distance

reflexive : Edit xs xs 0
reflexive = Het.reflexive S.refl

symmetric : Edit xs ys k → Edit ys xs k
symmetric = Het.symmetric S.sym

-- The relation is sub-additive
compose : Edit xs ys k → Edit ys zs l →
  ∃ λ m → Edit xs zs m × m ≤ k + l
compose = Het.compose S.trans


------------------------------------------------------------------------
-- But (provided that A is inhabited) it is not a distance

open import Data.List.Relation.Binary.Distance.Levenshtein.Internal
  using (Unique; Triangle)

module _ (x : A) where

  -- the "distance" defined by the relation is not unique
  not-unique : ¬ Unique {A = List A} Edit
  not-unique unique =
    let xs = x ∷ []
        hyp = unique xs xs 0 1 reflexive (swap done)
    in 0≢1+n hyp

  -- the relation does not satisfy the triangle inequality
  not-triangle : ¬ (Triangle {A = List A} Edit)
  not-triangle triangle =
      let xs = x ∷ []
          hyp = triangle xs xs xs 0 0 1 reflexive reflexive (swap done)
      in 1+n≰n hyp
