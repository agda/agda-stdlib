------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the sublist relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary hiding (Decidable)

module Data.List.Relation.Binary.Subset.Propositional.Properties
  where

open import Category.Monad
open import Data.Bool.Base using (Bool; true; false; T)
open import Data.List.Base
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any hiding (filter⁺)
open import Data.List.Categorical
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
import Data.List.Relation.Binary.Subset.Setoid.Properties as Setoidₚ
open import Data.List.Relation.Binary.Subset.Propositional
import Data.Product as Prod
import Data.Sum.Base as Sum
open import Function.Base using (_∘_; _∘′_; id; _$_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equivalence using (module Equivalence)
open import Level using (Level)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable; Pred)
open import Relation.Binary using (_⇒_; _Respects_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≗_; isEquivalence; refl; setoid; module ≡-Reasoning)
import Relation.Binary.Reasoning.Preorder as PreorderReasoning

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

  variable
    a b p : Level
    A : Set a
    B : Set b
    ws xs ys zs : List A

------------------------------------------------------------------------
-- Relational properties
------------------------------------------------------------------------

⊆-reflexive : _≡_ {A = List A} ⇒ _⊆_
⊆-reflexive refl = id

⊆-refl : Reflexive {A = List A} _⊆_
⊆-refl x∈xs = x∈xs

⊆-trans : Transitive {A = List A} _⊆_
⊆-trans xs⊆ys ys⊆zs = ys⊆zs ∘ xs⊆ys

module _ (A : Set a) where

  ⊆-isPreorder : IsPreorder {A = List A} _≡_ _⊆_
  ⊆-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ⊆-reflexive
    ; trans         = ⊆-trans
    }

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = record
    { isPreorder = ⊆-isPreorder
    }

------------------------------------------------------------------------
-- Reasoning over subsets
------------------------------------------------------------------------

module ⊆-Reasoning (A : Set a) where
  open Setoidₚ.⊆-Reasoning (setoid A) public
    hiding (step-≋; step-≋˘; _≋⟨⟩_)

------------------------------------------------------------------------
-- Properties relating _⊆_ to various list functions
------------------------------------------------------------------------
-- Any

Any-resp-⊆ : ∀ {P : Pred A p} → (Any P) Respects _⊆_
Any-resp-⊆ xs⊆ys =
  _⟨$⟩_ (Inverse.to Any↔) ∘′
  Prod.map₂ (Prod.map₁ xs⊆ys) ∘
  _⟨$⟩_ (Inverse.from Any↔)

------------------------------------------------------------------------
-- map

map⁺ : ∀ (f : A → B) → xs ⊆ ys → map f xs ⊆ map f ys
map⁺ f xs⊆ys =
  _⟨$⟩_ (Inverse.to (map-∈↔ f)) ∘
  Prod.map₂ (Prod.map₁ xs⊆ys) ∘
  _⟨$⟩_ (Inverse.from (map-∈↔ f))

------------------------------------------------------------------------
-- _++_

++⁺ : ws ⊆ xs → ys ⊆ zs → ws ++ ys ⊆ xs ++ zs
++⁺ ws⊆xs ys⊆zs =
  _⟨$⟩_ (Inverse.to Any.++↔) ∘
  Sum.map ws⊆xs ys⊆zs ∘
  _⟨$⟩_ (Inverse.from Any.++↔)

------------------------------------------------------------------------
-- concat

module _ {xss yss : List (List A)} where

  concat⁺ : xss ⊆ yss → concat xss ⊆ concat yss
  concat⁺ xss⊆yss =
    _⟨$⟩_ (Inverse.to concat-∈↔) ∘
    Prod.map₂ (Prod.map₂ xss⊆yss) ∘
    _⟨$⟩_ (Inverse.from concat-∈↔)

------------------------------------------------------------------------
-- _>>=_

module _ {A B : Set a} (f g : A → List B) where

  >>=⁺ : xs ⊆ ys → (∀ {x} → f x ⊆ g x) → (xs >>= f) ⊆ (ys >>= g)
  >>=⁺ xs⊆ys f⊆g =
    _⟨$⟩_ (Inverse.to >>=-∈↔) ∘
    Prod.map₂ (Prod.map xs⊆ys f⊆g) ∘
    _⟨$⟩_ (Inverse.from >>=-∈↔)

------------------------------------------------------------------------
-- _⊛_

module _ {A B : Set a} {fs gs : List (A → B)} where

  ⊛⁺ : fs ⊆ gs → xs ⊆ ys → (fs ⊛ xs) ⊆ (gs ⊛ ys)
  ⊛⁺ fs⊆gs xs⊆ys =
    _⟨$⟩_ (Inverse.to $ ⊛-∈↔ gs) ∘
    Prod.map₂ (Prod.map₂ (Prod.map fs⊆gs (Prod.map₁ xs⊆ys))) ∘
    _⟨$⟩_ (Inverse.from $ ⊛-∈↔ fs)

------------------------------------------------------------------------
-- _⊗_

module _ {A B : Set a} {ws xs : List A} {ys zs : List B} where

  ⊗⁺ : ws ⊆ xs → ys ⊆ zs → (ws ⊗ ys) ⊆ (xs ⊗ zs)
  ⊗⁺ ws⊆xs ys⊆zs =
    _⟨$⟩_ (Inverse.to ⊗-∈↔) ∘
    Prod.map ws⊆xs ys⊆zs ∘
    _⟨$⟩_ (Inverse.from ⊗-∈↔)

------------------------------------------------------------------------
-- any

module _ (p : A → Bool) {xs ys} where

  any⁺ : xs ⊆ ys → T (any p xs) → T (any p ys)
  any⁺ xs⊆ys =
    _⟨$⟩_ (Equivalence.to Any.any⇔) ∘
    Any-resp-⊆ xs⊆ys ∘
    _⟨$⟩_ (Equivalence.from Any.any⇔)

------------------------------------------------------------------------
-- map-with-∈

module _ {xs : List A} {f : ∀ {x} → x ∈ xs → B}
         {ys : List A} {g : ∀ {x} → x ∈ ys → B}
         where

  map-with-∈⁺ : (xs⊆ys : xs ⊆ ys) → (∀ {x} → f {x} ≗ g ∘ xs⊆ys) →
                map-with-∈ xs f ⊆ map-with-∈ ys g
  map-with-∈⁺ xs⊆ys f≈g {x} =
    _⟨$⟩_ (Inverse.to Any.map-with-∈↔) ∘
    Prod.map₂ (Prod.map xs⊆ys (λ {x∈xs} x≡fx∈xs → begin
      x               ≡⟨ x≡fx∈xs ⟩
      f x∈xs          ≡⟨ f≈g x∈xs ⟩
      g (xs⊆ys x∈xs)  ∎)) ∘
    _⟨$⟩_ (Inverse.from Any.map-with-∈↔)
    where open ≡-Reasoning

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : Decidable P) where

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ = Setoidₚ.filter-⊆ (setoid A) P?



------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------

-- Version 0.16

boolFilter-⊆ : ∀ (p : A → Bool) →
               (xs : List A) → boolFilter p xs ⊆ xs
boolFilter-⊆ p (x ∷ xs) with p x | boolFilter-⊆ p xs
... | false | hyp = there ∘ hyp
... | true  | hyp =
  λ { (here  eq)          → here eq
    ; (there ∈boolFilter) → there (hyp ∈boolFilter)
    }
{-# WARNING_ON_USAGE boolFilter-⊆
"Warning: boolFilter was deprecated in v0.16.
Please use filter instead."
#-}

-- Version 1.5

mono = Any-resp-⊆
{-# WARNING_ON_USAGE mono
"Warning: mono was deprecated in v1.5.
Please use Any-resp-⊆ instead."
#-}
map-mono = map⁺
{-# WARNING_ON_USAGE map-mono
"Warning: map-mono was deprecated in v1.5.
Please use map⁺ instead."
#-}
infix 4 _++-mono_
_++-mono_ = ++⁺
{-# WARNING_ON_USAGE _++-mono_
"Warning: _++-mono_ was deprecated in v1.5.
Please use ++⁺ instead."
#-}
concat-mono = concat⁺
{-# WARNING_ON_USAGE concat-mono
"Warning: concat-mono was deprecated in v1.5.
Please use concat⁺ instead."
#-}
>>=-mono = >>=⁺
{-# WARNING_ON_USAGE >>=-mono
"Warning: >>=-mono was deprecated in v1.5.
Please use >>=⁺ instead."
#-}
infix 4  _⊛-mono_
_⊛-mono_ = ⊛⁺
{-# WARNING_ON_USAGE _⊛-mono_
"Warning: _⊛-mono_ was deprecated in v1.5.
Please use ⊛⁺ instead."
#-}
infix 4  _⊗-mono_
_⊗-mono_ = ⊗⁺
{-# WARNING_ON_USAGE _⊗-mono_
"Warning: _⊗-mono_ was deprecated in v1.5.
Please use ⊗⁺ instead."
#-}
any-mono = any⁺
{-# WARNING_ON_USAGE any-mono
"Warning: any-mono was deprecated in v1.5.
Please use any⁺ instead."
#-}
map-with-∈-mono = map-with-∈⁺
{-# WARNING_ON_USAGE map-with-∈-mono
"Warning: map-with-∈-mono was deprecated in v1.5.
Please use map-with-∈⁺ instead."
#-}
filter⁺ = filter-⊆
{-# WARNING_ON_USAGE filter⁺
"Warning: filter⁺ was deprecated in v1.5.
Please use filter-⊆ instead."
#-}
