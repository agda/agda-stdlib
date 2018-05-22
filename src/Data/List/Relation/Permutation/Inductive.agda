------------------------------------------------------------------------
-- The Agda standard library
--
-- A term lanague for permutation
------------------------------------------------------------------------

module Data.List.Relation.Permutation.Inductive where

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; _≢_)
open import Relation.Binary
open import Data.List
open import Function

module _ {a} {A : Set a} where

  infix 3 _⇿_

  -- an inductive definition of permutation

  data _⇿_ : Rel (List A) a where
    refl  : ∀ {l} → l ⇿ l
    prep  : ∀ {l₁ l₂} x → l₁ ⇿ l₂ → x ∷ l₁ ⇿ x ∷ l₂
    swap  : ∀ {l₁ l₂} x y → l₁ ⇿ l₂ → x ∷ y ∷ l₁ ⇿ y ∷ x ∷ l₂
    trans : ∀ {l₁ l₂ l₃} → l₁ ⇿ l₂ → l₂ ⇿ l₃ → l₁ ⇿ l₃

  sym : ∀ {l₁ l₂} → l₁ ⇿ l₂ → l₂ ⇿ l₁
  sym refl         = refl
  sym (prep x p)   = prep x (sym p)
  sym (swap x y p) = swap y x (sym p)
  sym (trans p p₁) = trans (sym p₁) (sym p)

  isEquivalence : IsEquivalence _⇿_
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

  -- A reasoning API to manipulate permutation based on the setoid we just defined.

  module PReasoning where
    open import Relation.Binary.EqReasoning setoid
      using (begin_ ; _∎ ; _≡⟨⟩_ ; _IsRelatedTo_ ; relTo)
      renaming (_≈⟨_⟩_ to _p⟨_⟩_)
      public

    infixr 2 _∷_<⟨_⟩_  _∷_∷_<<⟨_⟩_

    -- following APIs allow to "zoom in" to localize reasoning

    _∷_<⟨_⟩_ : ∀ x (l : List A) {l₁ l₂ : List A} → l ⇿ l₁ →
                 (x ∷ l₁) IsRelatedTo l₂ → (x ∷ l) IsRelatedTo l₂
    x ∷ l <⟨ r ⟩ rel = relTo (trans (prep x r) $ begin rel)

    _∷_∷_<<⟨_⟩_ : ∀ x y (l : List A) {l₁ l₂ : List A} → l ⇿ l₁ →
                    (y ∷ x ∷ l₁) IsRelatedTo l₂ → (x ∷ y ∷ l) IsRelatedTo l₂
    x ∷ y ∷ l <<⟨ r ⟩ rel = relTo (trans (swap x y r) $ begin rel)
