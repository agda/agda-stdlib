------------------------------------------------------------------------
-- The Agda standard library
--
-- Permutation
------------------------------------------------------------------------

module Data.List.Permutation where

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; setoid ; _≢_ ; isEquivalence)
  renaming (trans to ≡-trans)
open import Relation.Binary

open import Data.List
open import Data.List.Any

open import Function

open import Data.Empty
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; ∃ ; ∃₂)

open import Data.List.Properties

module _ {a} {A : Set a} where

  -- an inductive definition of permutation

  data perm : Rel (List A) a where
    unit  : ∀ {l} → perm l l
    prep  : ∀ {l₁ l₂} x → perm l₁ l₂ → perm (x ∷ l₁) (x ∷ l₂)
    swap  : ∀ {l₁ l₂} x y → perm l₁ l₂ → perm (x ∷ y ∷ l₁) (y ∷ x ∷ l₂)
    trans : ∀ {l₁ l₂ l₃} → perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

  perm-sym : ∀ {l₁ l₂} → perm l₁ l₂ → perm l₂ l₁
  perm-sym unit         = unit
  perm-sym (prep x p)   = prep x (perm-sym p)
  perm-sym (swap x y p) = swap y x (perm-sym p)
  perm-sym (trans p p₁) = trans (perm-sym p₁) (perm-sym p)

  perm-isEquivalence : IsEquivalence perm
  perm-isEquivalence = record
    { refl  = unit
    ; sym   = perm-sym
    ; trans = trans
    }

  perm-setoid : Setoid _ _
  perm-setoid = record { isEquivalence = perm-isEquivalence }

  -- A reasoning API to manipulate permutation based on the setoid we just defined.
  -- for mperm, we can simply deligate the reasoning portion to ℕ, which is way richer.

  module PReasoning where
    open import Relation.Binary.EqReasoning perm-setoid
      using (begin_ ; _∎ ; _≡⟨⟩_ ; _IsRelatedTo_ ; relTo)
      renaming (_≈⟨_⟩_ to _p⟨_⟩_)
      public

    infixr 2 _∷_<⟨_⟩_  _∷_∷_<<⟨_⟩_

    -- following APIs allow to "zoom in" to localize reasoning

    _∷_<⟨_⟩_ : ∀ x (l : List A) {l₁ l₂ : List A} → perm l l₁ →
                 (x ∷ l₁) IsRelatedTo l₂ → (x ∷ l) IsRelatedTo l₂
    x ∷ l <⟨ r ⟩ rel = relTo (trans (prep x r) $ begin rel)

    _∷_∷_<<⟨_⟩_ : ∀ x y (l : List A) {l₁ l₂ : List A} → perm l l₁ →
                    (y ∷ x ∷ l₁) IsRelatedTo l₂ → (x ∷ y ∷ l) IsRelatedTo l₂
    x ∷ y ∷ l <<⟨ r ⟩ rel = relTo (trans (swap x y r) $ begin rel)


  -- properties for `perm`

  perm-++ʳ : ∀ {l₁ l₂} l → perm l₁ l₂ → perm (l₁ ++ l) (l₂ ++ l)
  perm-++ʳ l unit         = unit
  perm-++ʳ l (prep x p)   = prep x (perm-++ʳ l p)
  perm-++ʳ l (swap x y p) = swap x y (perm-++ʳ l p)
  perm-++ʳ l (trans p p₁) = trans (perm-++ʳ l p) (perm-++ʳ l p₁)

  perm-++ˡ : ∀ {l₁ l₂} l → perm l₁ l₂ → perm (l ++ l₁) (l ++ l₂)
  perm-++ˡ [] p      = p
  perm-++ˡ (x ∷ l) p = prep x (perm-++ˡ l p)

  perm-++ : ∀ {l₁ l₂ j₁ j₂} → perm l₁ l₂ → perm j₁ j₂ → perm (l₁ ++ j₁) (l₂ ++ j₂)
  perm-++ {l₁} {l₂} {j₁} {j₂} pl pj = begin
    l₁ ++ j₁ p⟨ perm-++ˡ l₁ pj ⟩
    l₁ ++ j₂ p⟨ perm-++ʳ _ pl ⟩
    l₂ ++ j₂ ∎
    where open PReasoning

  -- this lemma allows focusing on a small portion of the lists
  perm-zoom : ∀ {h t l₁ l₂} → perm l₁ l₂ → perm (h ++ l₁ ++ t) (h ++ l₂ ++ t)
  perm-zoom {h} {t} = perm-++ˡ h ∘ perm-++ʳ t

  perm-inject : ∀ {l₁ l₂ j₁ j₂} x → perm l₁ l₂ → perm j₁ j₂ → perm (l₁ ++ x ∷ j₁) (l₂ ++ x ∷ j₂)
  perm-inject {l₁} x pl pj = trans (perm-++ˡ l₁ (prep x pj)) (perm-++ʳ _ pl)

  perm-swap-head : ∀ x l → perm (x ∷ l) (l ++ [ x ])
  perm-swap-head x []       = unit
  perm-swap-head x (x₁ ∷ l) = begin
    x ∷ x₁ ∷ l      <<⟨ unit ⟩
    x₁ ∷ (x ∷ l)    <⟨ perm-swap-head x l ⟩
    x₁ ∷ l ++ [ x ] ∎
    where open PReasoning

  perm-swap : ∀ l₁ l₂ → perm (l₁ ++ l₂) (l₂ ++ l₁)
  perm-swap [] l₂ rewrite ++-identityʳ l₂ = unit
  perm-swap (x ∷ l₁) l₂ with perm-++ʳ l₁ $ perm-swap-head x l₂
  ... | res rewrite ++-assoc l₂ [ x ] l₁  = trans (prep x (perm-swap l₁ l₂)) res

  perm-shift : ∀ l₁ l₂ x → perm (l₁ ++ x ∷ l₂) (x ∷ l₁ ++ l₂)
  perm-shift [] l₂ x        = unit
  perm-shift (x₁ ∷ l₁) l₂ x = begin
    x₁ ∷ (l₁ ++ x ∷ l₂) <⟨ perm-shift l₁ l₂ x ⟩
    x₁ ∷ x ∷ l₁ ++ l₂   <<⟨ unit ⟩
    x ∷ x₁ ∷ l₁ ++ l₂   ∎
    where open PReasoning

  Any-resp-perm : ∀ {ℓ} (P : A → Set ℓ) → (Any P) Respects perm
  Any-resp-perm P unit wit                         = wit
  Any-resp-perm P (prep x p) (here px)             = here px
  Any-resp-perm P (prep x p) (there wit)           = there (Any-resp-perm P p wit)
  Any-resp-perm P (swap x y p) (here px)           = there (here px)
  Any-resp-perm P (swap x y p) (there (here px))   = here px
  Any-resp-perm P (swap x y p) (there (there wit)) = there (there (Any-resp-perm P p wit))
  Any-resp-perm P (trans p p₁) wit                 = Any-resp-perm P p₁ (Any-resp-perm P p wit)

  open import Data.List.All

  All-resp-perm : ∀ {ℓ} (P : A → Set ℓ) → (All P) Respects perm
  All-resp-perm P unit wit                     = wit
  All-resp-perm P (prep x p) (px ∷ wit)        = px ∷ All-resp-perm P p wit
  All-resp-perm P (swap x y p) (px ∷ py ∷ wit) = py ∷ px ∷ All-resp-perm P p wit
  All-resp-perm P (trans p₁ p₂) wit            = All-resp-perm P p₂ (All-resp-perm P p₁ wit)
