------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty where

open import Level using (Level)
open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Bool.Properties
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Nat.Base as ℕ
open import Data.Product as Prod using (∃; _×_; proj₁; proj₂; _,_; -,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using () renaming (module Equivalence to Eq)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (isYes)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Re-export basic type and operations

open import Data.List.NonEmpty.Base public

------------------------------------------------------------------------
-- More operations

-- Groups all contiguous elements for which the predicate returns the
-- same result into lists.

split : (p : A → Bool) → List A →
        List (List⁺ (∃ (T ∘ p)) ⊎ List⁺ (∃ (T ∘ not ∘ p)))
split p []       = []
split p (x ∷ xs) with p x | P.inspect p x | split p xs
... | true  | P.[ px≡t ] | inj₁ xs′ ∷ xss = inj₁ ((x , Eq.from T-≡     ⟨$⟩ px≡t) ∷⁺ xs′) ∷ xss
... | true  | P.[ px≡t ] | xss            = inj₁ [ x , Eq.from T-≡     ⟨$⟩ px≡t ]        ∷ xss
... | false | P.[ px≡f ] | inj₂ xs′ ∷ xss = inj₂ ((x , Eq.from T-not-≡ ⟨$⟩ px≡f) ∷⁺ xs′) ∷ xss
... | false | P.[ px≡f ] | xss            = inj₂ [ x , Eq.from T-not-≡ ⟨$⟩ px≡f ]        ∷ xss

-- If we flatten the list returned by split, then we get the list we
-- started with.

flatten : ∀ {p q} {P : A → Set p} {Q : A → Set q} →
          List (List⁺ (∃ P) ⊎ List⁺ (∃ Q)) → List A
flatten = List.concat ∘
          List.map Sum.[ toList ∘ map proj₁ , toList ∘ map proj₁ ]

flatten-split : (p : A → Bool) (xs : List A) → flatten (split p xs) ≡ xs
flatten-split p []       = refl
flatten-split p (x ∷ xs)
  with p x | P.inspect p x | split p xs | flatten-split p xs
... | true  | P.[ _ ] | []         | hyp = P.cong (_∷_ x) hyp
... | true  | P.[ _ ] | inj₁ _ ∷ _ | hyp = P.cong (_∷_ x) hyp
... | true  | P.[ _ ] | inj₂ _ ∷ _ | hyp = P.cong (_∷_ x) hyp
... | false | P.[ _ ] | []         | hyp = P.cong (_∷_ x) hyp
... | false | P.[ _ ] | inj₁ _ ∷ _ | hyp = P.cong (_∷_ x) hyp
... | false | P.[ _ ] | inj₂ _ ∷ _ | hyp = P.cong (_∷_ x) hyp

-- Groups all contiguous elements /not/ satisfying the predicate into
-- lists. Elements satisfying the predicate are dropped.

wordsBy : (A → Bool) → List A → List (List⁺ A)
wordsBy p =
  List.mapMaybe Sum.[ const nothing , just ∘′ map proj₁ ] ∘ split p

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
 module Examples {A B : Set}
                 (_⊕_ : A → B → B)
                 (_⊗_ : B → A → B)
                 (_⊙_ : A → A → A)
                 (f : A → B)
                 (a b c : A)
                 where

  hd : head (a ∷⁺ b ∷⁺ [ c ]) ≡ a
  hd = refl

  tl : tail (a ∷⁺ b ∷⁺ [ c ]) ≡ b ∷ c ∷ []
  tl = refl

  mp : map f (a ∷⁺ b ∷⁺ [ c ]) ≡ f a ∷⁺ f b ∷⁺ [ f c ]
  mp = refl

  right : foldr _⊕_ f (a ∷⁺ b ∷⁺ [ c ]) ≡ (a ⊕ (b ⊕ f c))
  right = refl

  right₁ : foldr₁ _⊙_ (a ∷⁺ b ∷⁺ [ c ]) ≡ (a ⊙ (b ⊙ c))
  right₁ = refl

  left : foldl _⊗_ f (a ∷⁺ b ∷⁺ [ c ]) ≡ ((f a ⊗ b) ⊗ c)
  left = refl

  left₁ : foldl₁ _⊙_ (a ∷⁺ b ∷⁺ [ c ]) ≡ ((a ⊙ b) ⊙ c)
  left₁ = refl

  ⁺app⁺ : (a ∷⁺ b ∷⁺ [ c ]) ⁺++⁺ (b ∷⁺ [ c ]) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  ⁺app⁺ = refl

  ⁺app : (a ∷⁺ b ∷⁺ [ c ]) ⁺++ (b ∷ c ∷ []) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  ⁺app = refl

  app⁺ : (a ∷ b ∷ c ∷ []) ++⁺ (b ∷⁺ [ c ]) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  app⁺ = refl

  conc : concat ((a ∷⁺ b ∷⁺ [ c ]) ∷⁺ [ b ∷⁺ [ c ] ]) ≡
         a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  conc = refl

  rev : reverse (a ∷⁺ b ∷⁺ [ c ]) ≡ c ∷⁺ b ∷⁺ [ a ]
  rev = refl

  snoc : (a ∷ b ∷ c ∷ []) ∷ʳ a ≡ a ∷⁺ b ∷⁺ c ∷⁺ [ a ]
  snoc = refl

  snoc⁺ : (a ∷⁺ b ∷⁺ [ c ]) ⁺∷ʳ a ≡ a ∷⁺ b ∷⁺ c ∷⁺ [ a ]
  snoc⁺ = refl

  split-true : split (const true) (a ∷ b ∷ c ∷ []) ≡
               inj₁ ((a , tt) ∷⁺ (b , tt) ∷⁺ [ c , tt ]) ∷ []
  split-true = refl

  split-false : split (const false) (a ∷ b ∷ c ∷ []) ≡
                inj₂ ((a , tt) ∷⁺ (b , tt) ∷⁺ [ c , tt ]) ∷ []
  split-false = refl

  split-≡1 :
    split (ℕ._≡ᵇ 1) (1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ []) ≡
    inj₁ [ 1 , tt ] ∷ inj₂ ((2 , tt) ∷⁺ [ 3 , tt ]) ∷
    inj₁ ((1 , tt) ∷⁺ [ 1 , tt ]) ∷ inj₂ [ 2 , tt ] ∷ inj₁ [ 1 , tt ] ∷
    []
  split-≡1 = refl

  wordsBy-true : wordsBy (const true) (a ∷ b ∷ c ∷ []) ≡ []
  wordsBy-true = refl

  wordsBy-false : wordsBy (const false) (a ∷ b ∷ c ∷ []) ≡
                  (a ∷⁺ b ∷⁺ [ c ]) ∷ []
  wordsBy-false = refl

  wordsBy-≡1 :
    wordsBy (ℕ._≡ᵇ 1) (1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ []) ≡
    (2 ∷⁺ [ 3 ]) ∷ [ 2 ] ∷ []
  wordsBy-≡1 = refl

  ------------------------------------------------------------------------
  -- DEPRECATED
  ------------------------------------------------------------------------
  -- Please use the new names as continuing support for the old names is
  -- not guaranteed.

  -- Version 1.4

  infixl 5 _∷ʳ'_

  _∷ʳ'_ : (xs : List A) (x : A) → SnocView (xs ∷ʳ x)
  _∷ʳ'_ = SnocView._∷ʳ′_
  {-# WARNING_ON_USAGE _∷ʳ'_
  "Warning: _∷ʳ'_ (ending in an apostrophe) was deprecated in v1.4.
  Please use _∷ʳ′_ (ending in a prime) instead."
  #-}
