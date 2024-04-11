------------------------------------------------------------------------
-- The Agda standard library
--
-- Raw Actions of one (pre-)Setoid on another
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Action.Structures.Raw
  {c a ℓ r} {M : Set c} {A : Set a} (_≈ᴹ_ : Rel M ℓ) (_≈_ : Rel A r)
  where

open import Data.List.Base
  using (List; []; _∷_; _++_; foldl; foldr)
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

record IsRawLeftAction : Set (a ⊔ r ⊔ c ⊔ ℓ) where
  infixr 5 _ᴹ∙ᴬ_ _ᴹ⋆ᴬ_

  field
    _ᴹ∙ᴬ_  : M → A → A
    ∙-cong : m ≈ᴹ n → x ≈ y → (m ᴹ∙ᴬ x) ≈ (n ᴹ∙ᴬ y)

-- derived form: iterated action, satisfying congruence

  _ᴹ⋆ᴬ_ : List M → A → A
  ms ᴹ⋆ᴬ a = foldr _ᴹ∙ᴬ_ a ms

  ⋆-cong : Pointwise _≈ᴹ_ ms ns → x ≈ y → (ms ᴹ⋆ᴬ x) ≈ (ns ᴹ⋆ᴬ y)
  ⋆-cong []            x≈y = x≈y
  ⋆-cong (m≈n ∷ ms≋ns) x≈y = ∙-cong m≈n (⋆-cong ms≋ns x≈y)

  ⋆-act-cong : ∀ ms → Pointwise _≈ᴹ_ ps (ms ++ ns) →
               x ≈ y → (ps ᴹ⋆ᴬ x) ≈ (ms ᴹ⋆ᴬ ns ᴹ⋆ᴬ y)
  ⋆-act-cong []       ps≋ns             x≈y = ⋆-cong ps≋ns x≈y
  ⋆-act-cong (m ∷ ms) (p≈m ∷ ps≋ms++ns) x≈y = ∙-cong p≈m (⋆-act-cong ms ps≋ms++ns x≈y)

  []-act-cong : x ≈ y → ([] ᴹ⋆ᴬ x) ≈ y
  []-act-cong = id

record IsRawRightAction : Set (a ⊔ r ⊔ c ⊔ ℓ) where
  infixl 5 _ᴬ∙ᴹ_ _ᴬ⋆ᴹ_

  field
    _ᴬ∙ᴹ_  : A → M → A
    ∙-cong : x ≈ y → m ≈ᴹ n → (x ᴬ∙ᴹ m) ≈ (y ᴬ∙ᴹ n)

-- derived form: iterated action, satisfying congruence

  _ᴬ⋆ᴹ_ : A → List M → A
  a ᴬ⋆ᴹ ms = foldl _ᴬ∙ᴹ_ a ms

  ⋆-cong : x ≈ y → Pointwise _≈ᴹ_ ms ns → (x ᴬ⋆ᴹ ms) ≈ (y ᴬ⋆ᴹ ns)
  ⋆-cong x≈y []            = x≈y
  ⋆-cong x≈y (m≈n ∷ ms≋ns) = ⋆-cong (∙-cong x≈y m≈n) ms≋ns

  ⋆-act-cong : x ≈ y → ∀ ms → Pointwise _≈ᴹ_ ps (ms ++ ns) →
               (x ᴬ⋆ᴹ ps) ≈ (y ᴬ⋆ᴹ ms ᴬ⋆ᴹ ns)
  ⋆-act-cong x≈y []       ps≋ns             = ⋆-cong x≈y ps≋ns
  ⋆-act-cong x≈y (m ∷ ms) (p≈m ∷ ps≋ms++ns) = ⋆-act-cong (∙-cong x≈y p≈m) ms ps≋ms++ns

  []-act-cong : x ≈ y → (x ᴬ⋆ᴹ []) ≈ y
  []-act-cong = id
