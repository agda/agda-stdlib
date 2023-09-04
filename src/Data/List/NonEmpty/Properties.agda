------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Properties where

open import Effect.Monad
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Effectful using () renaming (monad to listMonad)
open import Data.List.NonEmpty.Effectful using () renaming (monad to list⁺Monad)
open import Data.List.NonEmpty
open import Data.List.NonEmpty.Relation.Unary.All
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to ListAll)
import Data.List.Properties as List
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Relation.Unary.All using (inj₁; inj₂)
import Data.Sum.Relation.Unary.All as Sum using (All; inj₁; inj₂)
open import Level using (Level)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred; Decidable; ∁)
open import Relation.Nullary using (¬_; does; yes; no)

open ≡-Reasoning

private
  variable
    a p : Level
    A B C : Set a

  open module LMo {a} = RawMonad {f = a} listMonad
    using () renaming (_>>=_ to _⋆>>=_)
  open module L⁺Mo {a} = RawMonad {f = a} list⁺Monad

------------------------------------------------------------------------
-- toList

η : ∀ (xs : List⁺ A) → head xs ∷ tail xs ≡ toList xs
η _ = refl

toList-fromList : ∀ x (xs : List A) → x ∷ xs ≡ toList (x ∷ xs)
toList-fromList _ _ = refl

toList-⁺++ : ∀ (xs : List⁺ A) ys → toList xs ++ ys ≡ toList (xs ⁺++ ys)
toList-⁺++ _ _ = refl

toList-⁺++⁺ : ∀ (xs ys : List⁺ A) →
              toList xs ++ toList ys ≡ toList (xs ⁺++⁺ ys)
toList-⁺++⁺ _ _ = refl

toList->>= : ∀ (f : A → List⁺ B) (xs : List⁺ A) →
             (toList xs ⋆>>= toList ∘ f) ≡ toList (xs >>= f)
toList->>= f (x ∷ xs) = begin
  List.concat (List.map (toList ∘ f) (x ∷ xs))
    ≡⟨ cong List.concat $ List.map-∘ {g = toList} (x ∷ xs) ⟩
  List.concat (List.map toList (List.map f (x ∷ xs)))
    ∎

------------------------------------------------------------------------
-- _++⁺_

length-++⁺ : (xs : List A) (ys : List⁺ A) →
             length (xs ++⁺ ys) ≡ List.length xs + length ys
length-++⁺ [] ys                                = refl
length-++⁺ (x ∷ xs) ys rewrite length-++⁺ xs ys = refl

length-++⁺-tail : (xs : List A) (ys : List⁺ A) →
                  length (xs ++⁺ ys) ≡ suc (List.length xs + List.length (List⁺.tail ys))
length-++⁺-tail [] ys                                     = refl
length-++⁺-tail (x ∷ xs) ys rewrite length-++⁺-tail xs ys = refl

++-++⁺ : (xs : List A) → ∀ {ys zs} → (xs ++ ys) ++⁺ zs ≡ xs ++⁺ ys ++⁺ zs
++-++⁺ []      = refl
++-++⁺ (x ∷ l) = cong (x ∷_) (cong toList (++-++⁺ l))

++⁺-cancelˡ′ : ∀ xs ys {zs zs′ : List⁺ A} →
               xs ++⁺ zs ≡ ys ++⁺ zs′ →
               List.length xs ≡ List.length ys → zs ≡ zs′
++⁺-cancelˡ′ [] [] eq eqxs            = eq
++⁺-cancelˡ′ (x ∷ xs) (y ∷ ys) eq eql = ++⁺-cancelˡ′ xs ys
  (just-injective (cong fromList (cong List⁺.tail eq)))
  (suc-injective eql)

++⁺-cancelˡ : ∀ xs {ys zs : List⁺ A} → xs ++⁺ ys ≡ xs ++⁺ zs → ys ≡ zs
++⁺-cancelˡ xs eq = ++⁺-cancelˡ′ xs xs eq refl

drop-+-++⁺ : ∀ (xs : List A) ys → drop+ (List.length xs) (xs ++⁺ ys) ≡ ys
drop-+-++⁺ []       ys = refl
drop-+-++⁺ (x ∷ xs) ys = drop-+-++⁺ xs ys

map-++⁺ : ∀ (f : A → B) xs ys →
                  map f (xs ++⁺ ys) ≡ List.map f xs ++⁺ map f ys
map-++⁺ f [] ys       = refl
map-++⁺ f (x ∷ xs) ys = cong (λ zs → f x ∷ toList zs) (map-++⁺ f xs ys)

------------------------------------------------------------------------
-- map

length-map : ∀ (f : A → B) xs → length (map f xs) ≡ length xs
length-map f (_ ∷ xs) = cong suc (List.length-map f xs)

map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g
map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (List.map-cong f≗g xs)

map-∘ : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
map-∘ (x ∷ xs) = cong (_ ∷_) (List.map-∘ xs)

------------------------------------------------------------------------
-- groupSeqs

-- Groups all contiguous elements for which the predicate returns the
-- same result into lists.

module _ {P : Pred A p} (P? : Decidable P) where

  groupSeqs-groups : ∀ xs → ListAll (Sum.All (All P) (All (∁ P))) (groupSeqs P? xs)
  groupSeqs-groups []       = []
  groupSeqs-groups (x ∷ xs) with P? x | groupSeqs P? xs | groupSeqs-groups xs
  ... | yes px | []             | hyp             = inj₁ (px  ∷ []) ∷ hyp
  ... | yes px | inj₁ xs′ ∷ xss | inj₁ pxs ∷ pxss = inj₁ (px  ∷ toList⁺ pxs) ∷ pxss
  ... | yes px | inj₂ xs′ ∷ xss | inj₂ pxs ∷ pxss = inj₁ (px  ∷ []) ∷ inj₂ pxs ∷ pxss
  ... | no ¬px | []             | hyp             = inj₂ (¬px ∷ []) ∷ hyp
  ... | no ¬px | inj₂ xs′ ∷ xss | inj₂ pxs ∷ pxss = inj₂ (¬px ∷ toList⁺ pxs) ∷ pxss
  ... | no ¬px | inj₁ xs′ ∷ xss | inj₁ pxs ∷ pxss = inj₂ (¬px ∷ []) ∷ inj₁ pxs ∷ pxss

  ungroupSeqs-groupSeqs : ∀ xs → ungroupSeqs (groupSeqs P? xs) ≡ xs
  ungroupSeqs-groupSeqs []       = refl
  ungroupSeqs-groupSeqs (x ∷ xs)
    with does (P? x) | groupSeqs P? xs | ungroupSeqs-groupSeqs xs
  ... | true  | []         | hyp = cong (x ∷_) hyp
  ... | true  | inj₁ _ ∷ _ | hyp = cong (x ∷_) hyp
  ... | true  | inj₂ _ ∷ _ | hyp = cong (x ∷_) hyp
  ... | false | []         | hyp = cong (x ∷_) hyp
  ... | false | inj₁ _ ∷ _ | hyp = cong (x ∷_) hyp
  ... | false | inj₂ _ ∷ _ | hyp = cong (x ∷_) hyp

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-compose = map-∘
{-# WARNING_ON_USAGE map-compose
"Warning: map-compose was deprecated in v2.0.
Please use map-∘ instead."
#-}

map-++⁺-commute = map-++⁺
{-# WARNING_ON_USAGE map-++⁺-commute
"Warning: map-++⁺-commute was deprecated in v2.0.
Please use map-++⁺ instead."
#-}
