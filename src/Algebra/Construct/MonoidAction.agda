------------------------------------------------------------------------
-- The Agda standard library
--
-- Monoid Actions and the free Monoid Action on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Construct.MonoidAction where

open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid)

open import Data.List.Base
  using (List; []; _∷_; _++_; foldl; foldr)
import Data.List.Properties as List
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (_,_)

open import Function.Base using (id; _∘_; flip)

open import Level using (Level; suc; _⊔_)

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions

private
  variable
    a c r ℓ : Level
    A : Set a
    M : Set c


------------------------------------------------------------------------
-- Basic definitions: fix notation for underlying 'raw' actions

module _ {c a ℓ r} {M : Set c} {A : Set a}
         (_≈ᴹ_ : Rel M ℓ) (_≈_ : Rel A r)
  where

  private
    variable
      x y z : A
      m n p q : M
      ms ns ps qs : List M

  record RawLeftAction : Set (a ⊔ r ⊔ c ⊔ ℓ)  where
    infixr 5 _ᴹ∙ᴬ_ _ᴹ⋆ᴬ_

    field
      _ᴹ∙ᴬ_ : M → A → A
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

  record RawRightAction : Set (a ⊔ r ⊔ c ⊔ ℓ)  where
    infixl 5 _ᴬ∙ᴹ_ _ᴬ⋆ᴹ_

    field
      _ᴬ∙ᴹ_ : A → M → A
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


------------------------------------------------------------------------
-- Definition: indexed over an underlying raw action

module _ (M : Monoid c ℓ) (A : Setoid a r) where

  private

    open module M = Monoid M using () renaming (Carrier to M)
    open module A = Setoid A using (_≈_) renaming (Carrier to A)
    open ≋ M.setoid using (_≋_; [] ; _∷_; ≋-refl)

    variable
      x y z : A.Carrier
      m n p q : M.Carrier
      ms ns ps qs : List M.Carrier

  record LeftAction (rawLeftAction : RawLeftAction M._≈_ _≈_) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open RawLeftAction rawLeftAction public
      renaming (_ᴹ∙ᴬ_ to _∙_; _ᴹ⋆ᴬ_ to _⋆_)

    field
      ∙-act  : ∀ m n x → m M.∙ n ∙ x ≈ m ∙ n ∙ x
      ε-act  : ∀ x → M.ε ∙ x ≈ x

    ∙-congˡ : x ≈ y → m ∙ x ≈ m ∙ y
    ∙-congˡ x≈y = ∙-cong M.refl x≈y

    ∙-congʳ : m M.≈ n → m ∙ x ≈ n ∙ x
    ∙-congʳ m≈n = ∙-cong m≈n A.refl

    ⋆-act : ∀ ms ns x → (ms ++ ns) ⋆ x ≈ ms ⋆ ns ⋆ x
    ⋆-act ms ns x = ⋆-act-cong ms ≋-refl A.refl

    []-act : ∀ x → [] ⋆ x ≈ x
    []-act _ = []-act-cong A.refl

  record RightAction (rawRightAction : RawRightAction M._≈_ _≈_) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open RawRightAction rawRightAction public
      renaming (_ᴬ∙ᴹ_ to _∙_; _ᴬ⋆ᴹ_ to _⋆_)

    field
      ∙-act  : ∀ x m n → x ∙ m M.∙ n ≈ x ∙ m ∙ n
      ε-act  : ∀ x → x ∙ M.ε ≈ x

    ∙-congˡ : x ≈ y → x ∙ m ≈ y ∙ m
    ∙-congˡ x≈y = ∙-cong x≈y M.refl

    ∙-congʳ : m M.≈ n → x ∙ m ≈ x ∙ n
    ∙-congʳ m≈n = ∙-cong A.refl m≈n

    ⋆-act : ∀ x ms ns → x ⋆ (ms ++ ns) ≈ x ⋆ ms ⋆ ns
    ⋆-act x ms ns = ⋆-act-cong A.refl ms ≋-refl

    []-act : ∀ x → x ⋆ [] ≈ x
    []-act x = []-act-cong A.refl

------------------------------------------------------------------------
-- Distinguished actions: of a module over itself

module Regular (M : Monoid c ℓ) where

  open Monoid M

  private
    rawLeftAction : RawLeftAction _≈_ _≈_
    rawLeftAction = record { _ᴹ∙ᴬ_ = _∙_ ; ∙-cong = ∙-cong }

    rawRightAction : RawRightAction _≈_ _≈_
    rawRightAction = record { _ᴬ∙ᴹ_ = _∙_ ; ∙-cong = ∙-cong }

  leftAction : LeftAction M setoid rawLeftAction
  leftAction = record
    { ∙-act = assoc
    ; ε-act = identityˡ
    }

  rightAction : RightAction M setoid rawRightAction
  rightAction = record
    { ∙-act = λ x m n → sym (assoc x m n)
    ; ε-act = identityʳ
    }

------------------------------------------------------------------------
-- Distinguished *free* action: lifting a raw action to a List action

module Free (M : Setoid c ℓ) (S : Setoid a r) where

  private

    open ≋ M using (_≋_; ≋-refl; ≋-reflexive; ≋-isEquivalence; ++⁺)
    open module M = Setoid M using () renaming (Carrier to M)
    open module A = Setoid S using (_≈_) renaming (Carrier to A)

    isMonoid : IsMonoid _≋_ _++_ []
    isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≋-isEquivalence
          ; ∙-cong = ++⁺
          }
        ; assoc = λ xs ys zs → ≋-reflexive (List.++-assoc xs ys zs)
        }
      ; identity = (λ _ → ≋-refl) , ≋-reflexive ∘ List.++-identityʳ }

    monoid : Monoid _ _
    monoid = record { isMonoid = isMonoid }

  leftAction : (rawLeftAction : RawLeftAction M._≈_ _≈_) →
               (open RawLeftAction rawLeftAction) →
               LeftAction monoid S (record { _ᴹ∙ᴬ_ = _ᴹ⋆ᴬ_  ; ∙-cong = ⋆-cong })
  leftAction rawLeftAction = record
    { ∙-act = λ ms ns x → ⋆-act-cong ms ≋-refl A.refl
    ; ε-act = λ _ → []-act-cong A.refl
    }
    where open RawLeftAction rawLeftAction

  rightAction : (rawRightAction : RawRightAction M._≈_ _≈_) →
                (open RawRightAction rawRightAction) →
                RightAction monoid S (record { _ᴬ∙ᴹ_ = _ᴬ⋆ᴹ_  ; ∙-cong = ⋆-cong })
  rightAction rawRightAction = record
    { ∙-act = λ x ms ns → ⋆-act-cong A.refl ms ≋-refl
    ; ε-act = λ _ → []-act-cong A.refl
    }
    where open RawRightAction rawRightAction
