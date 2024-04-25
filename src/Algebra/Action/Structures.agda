------------------------------------------------------------------------
-- The Agda standard library
--
-- Raw Actions of one (pre-)Setoid on another
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Action.Structures
  {c a ℓ r} {M : Set c} {A : Set a} (_≈ᴹ_ : Rel M ℓ) (_≈_ : Rel A r)
  where

open import Data.List.Base
  using (List; []; _∷_; _++_; foldl; foldr)
open import Data.List.NonEmpty.Base
  using (List⁺; _∷_)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Function.Base using (id)
open import Level using (Level; _⊔_)

private
  variable
    x y z : A
    m n p : M
    ms ns ps : List M

------------------------------------------------------------------------
-- Basic definitions: fix notation

record IsLeftAction : Set (a ⊔ r ⊔ c ⊔ ℓ) where
  infixr 5 _▷_ _▷⋆_ _▷⁺_

  field
    _▷_  : M → A → A
    ▷-cong : m ≈ᴹ n → x ≈ y → (m ▷ x) ≈ (n ▷ y)

-- derived form: iterated action, satisfying congruence

  _▷⋆_ : List M → A → A
  ms ▷⋆ a = foldr _▷_ a ms

  _▷⁺_ : List⁺ M → A → A
  (m ∷ ms) ▷⁺ a = m ▷ ms ▷⋆ a

  ▷⋆-cong : Pointwise _≈ᴹ_ ms ns → x ≈ y → (ms ▷⋆ x) ≈ (ns ▷⋆ y)
  ▷⋆-cong []            x≈y = x≈y
  ▷⋆-cong (m≈n ∷ ms≋ns) x≈y = ▷-cong m≈n (▷⋆-cong ms≋ns x≈y)
{-
  ▷⁺-cong : Pointwise _≈ᴹ_ ms ns → x ≈ y → (ms ▷⁺ x) ≈ (ns ▷⁺ y)
  ▷⁺-cong (m≈n ∷ ms≋ns) x≈y = ▷-cong m≈n (▷⋆-cong ms≋ns x≈y)
-}
  ▷⋆-act-cong : ∀ ms → Pointwise _≈ᴹ_ ps (ms ++ ns) →
                x ≈ y → (ps ▷⋆ x) ≈ (ms ▷⋆ ns ▷⋆ y)
  ▷⋆-act-cong []       ps≋ns             x≈y = ▷⋆-cong ps≋ns x≈y
  ▷⋆-act-cong (m ∷ ms) (p≈m ∷ ps≋ms++ns) x≈y = ▷-cong p≈m (▷⋆-act-cong ms ps≋ms++ns x≈y)

  []-act-cong : x ≈ y → ([] ▷⋆ x) ≈ y
  []-act-cong = id

record IsRightAction : Set (a ⊔ r ⊔ c ⊔ ℓ) where
  infixl 5 _◁_ _◁⋆_ _◁⁺_

  field
    _◁_  : A → M → A
    ◁-cong : x ≈ y → m ≈ᴹ n → (x ◁ m) ≈ (y ◁ n)

-- derived form: iterated action, satisfying congruence

  _◁⋆_ : A → List M → A
  a ◁⋆ ms = foldl _◁_ a ms

  _◁⁺_ : A → List⁺ M → A
  a ◁⁺ (m ∷ ms) = a ◁ m ◁⋆ ms

  ◁⋆-cong : x ≈ y → Pointwise _≈ᴹ_ ms ns → (x ◁⋆ ms) ≈ (y ◁⋆ ns)
  ◁⋆-cong x≈y []            = x≈y
  ◁⋆-cong x≈y (m≈n ∷ ms≋ns) = ◁⋆-cong (◁-cong x≈y m≈n) ms≋ns

  ◁⋆-act-cong : x ≈ y → ∀ ms → Pointwise _≈ᴹ_ ps (ms ++ ns) →
               (x ◁⋆ ps) ≈ (y ◁⋆ ms ◁⋆ ns)
  ◁⋆-act-cong x≈y []       ps≋ns             = ◁⋆-cong x≈y ps≋ns
  ◁⋆-act-cong x≈y (m ∷ ms) (p≈m ∷ ps≋ms++ns) = ◁⋆-act-cong (◁-cong x≈y p≈m) ms ps≋ms++ns

  []-act-cong : x ≈ y → (x ◁⋆ []) ≈ y
  []-act-cong = id
