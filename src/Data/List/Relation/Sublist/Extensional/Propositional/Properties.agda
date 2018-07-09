------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the sublist relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary hiding (Decidable)

module Data.List.Relation.Sublist.Extensional.Propositional.Properties
  where

open import Category.Monad
open import Data.Bool.Base using (Bool; true; false; T)
open import Data.List
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Properties as AnyP
open import Data.List.Categorical
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
import Data.List.Relation.Sublist.Extensional.Setoid.Properties as Setoidₚ
open import Data.List.Relation.Sublist.Extensional.Propositional
import Data.Product as Prod
import Data.Sum as Sum
open import Function using (_∘_; _∘′_; id; _$_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Equivalence using (module Equivalence)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (_⇒_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≗_; isEquivalence; refl; setoid; module ≡-Reasoning)
import Relation.Binary.PreorderReasoning as PreorderReasoning

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

------------------------------------------------------------------------
-- Relational properties

module _ {a} {A : Set a} where

  ⊆-reflexive : _≡_ ⇒ (_⊆_ {A = A})
  ⊆-reflexive refl = id

  ⊆-refl : Reflexive (_⊆_ {A = A})
  ⊆-refl x∈xs = x∈xs

  ⊆-trans : Transitive (_⊆_ {A = A})
  ⊆-trans xs⊆ys ys⊆zs x∈xs = ys⊆zs (xs⊆ys x∈xs)

module _ {a} (A : Set a) where

  ⊆-isPreorder : IsPreorder _≡_ (_⊆_ {A = A})
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

module ⊆-Reasoning {a} (A : Set a) where

  open PreorderReasoning (⊆-preorder A) public
    renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

  infix 1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

------------------------------------------------------------------------
-- Properties relating _⊆_ to various list functions
------------------------------------------------------------------------
-- Any

module _ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} where

  mono : xs ⊆ ys → Any P xs → Any P ys
  mono xs⊆ys =
    _⟨$⟩_ (Inverse.to Any↔) ∘′
    Prod.map id (Prod.map xs⊆ys id) ∘
    _⟨$⟩_ (Inverse.from Any↔)

------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} (f : A → B) {xs ys} where

  map-mono : xs ⊆ ys → map f xs ⊆ map f ys
  map-mono xs⊆ys =
    _⟨$⟩_ (Inverse.to map-∈↔) ∘
    Prod.map id (Prod.map xs⊆ys id) ∘
    _⟨$⟩_ (Inverse.from map-∈↔)

------------------------------------------------------------------------
-- _++_

module _ {a} {A : Set a} {xs₁ xs₂ ys₁ ys₂ : List A} where

  _++-mono_ : xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → xs₁ ++ xs₂ ⊆ ys₁ ++ ys₂
  _++-mono_ xs₁⊆ys₁ xs₂⊆ys₂ =
    _⟨$⟩_ (Inverse.to ++↔) ∘
    Sum.map xs₁⊆ys₁ xs₂⊆ys₂ ∘
    _⟨$⟩_ (Inverse.from ++↔)

------------------------------------------------------------------------
-- concat

module _ {a} {A : Set a} {xss yss : List (List A)} where

  concat-mono : xss ⊆ yss → concat xss ⊆ concat yss
  concat-mono xss⊆yss =
    _⟨$⟩_ (Inverse.to $ concat-∈↔ {a = a}) ∘
    Prod.map id (Prod.map id xss⊆yss) ∘
    _⟨$⟩_ (Inverse.from $ concat-∈↔ {a = a})

------------------------------------------------------------------------
-- _>>=_

module _ {ℓ} {A B : Set ℓ} (f g : A → List B) {xs ys} where

  >>=-mono : xs ⊆ ys → (∀ {x} → f x ⊆ g x) → (xs >>= f) ⊆ (ys >>= g)
  >>=-mono xs⊆ys f⊆g =
    _⟨$⟩_ (Inverse.to $ >>=-∈↔ {ℓ = ℓ}) ∘
    Prod.map id (Prod.map xs⊆ys f⊆g) ∘
    _⟨$⟩_ (Inverse.from $ >>=-∈↔ {ℓ = ℓ})

------------------------------------------------------------------------
-- _⊛_

module _ {ℓ} {A B : Set ℓ} {fs gs : List (A → B)} {xs ys : List A} where

  _⊛-mono_ : fs ⊆ gs → xs ⊆ ys → (fs ⊛ xs) ⊆ (gs ⊛ ys)
  _⊛-mono_ fs⊆gs xs⊆ys =
    _⟨$⟩_ (Inverse.to $ ⊛-∈↔ gs) ∘
    Prod.map id (Prod.map id (Prod.map fs⊆gs (Prod.map xs⊆ys id))) ∘
    _⟨$⟩_ (Inverse.from $ ⊛-∈↔ fs)

------------------------------------------------------------------------
-- _⊗_

module _ {ℓ} {A B : Set ℓ} {xs₁ ys₁ : List A} {xs₂ ys₂ : List B} where

  _⊗-mono_ : xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → (xs₁ ⊗ xs₂) ⊆ (ys₁ ⊗ ys₂)
  xs₁⊆ys₁ ⊗-mono xs₂⊆ys₂ =
    _⟨$⟩_ (Inverse.to $ ⊗-∈↔ {ℓ = ℓ}) ∘
    Prod.map xs₁⊆ys₁ xs₂⊆ys₂ ∘
    _⟨$⟩_ (Inverse.from $ ⊗-∈↔ {ℓ = ℓ})

------------------------------------------------------------------------
-- any

module _ {a} {A : Set a} (p : A → Bool) {xs ys} where

  any-mono : xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono xs⊆ys =
    _⟨$⟩_ (Equivalence.to any⇔) ∘
    mono xs⊆ys ∘
    _⟨$⟩_ (Equivalence.from any⇔)

------------------------------------------------------------------------
-- map-with-∈

module _ {a b} {A : Set a} {B : Set b}
         {xs : List A} {f : ∀ {x} → x ∈ xs → B}
         {ys : List A} {g : ∀ {x} → x ∈ ys → B} where

  map-with-∈-mono : (xs⊆ys : xs ⊆ ys) → (∀ {x} → f {x} ≗ g ∘ xs⊆ys) →
                    map-with-∈ xs f ⊆ map-with-∈ ys g
  map-with-∈-mono xs⊆ys f≈g {x} =
    _⟨$⟩_ (Inverse.to map-with-∈↔) ∘
    Prod.map id (Prod.map xs⊆ys (λ {x∈xs} x≡fx∈xs → begin
      x               ≡⟨ x≡fx∈xs ⟩
      f x∈xs          ≡⟨ f≈g x∈xs ⟩
      g (xs⊆ys x∈xs)  ∎)) ∘
    _⟨$⟩_ (Inverse.from map-with-∈↔)
    where open ≡-Reasoning

------------------------------------------------------------------------
-- filter

module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

  filter⁺ : ∀ xs → filter P? xs ⊆ xs
  filter⁺ = Setoidₚ.filter⁺ (setoid A) P?

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use `filter` instead of `boolFilter`

boolFilter-⊆ : ∀ {a} {A : Set a} (p : A → Bool) →
               (xs : List A) → boolFilter p xs ⊆ xs
boolFilter-⊆ _ []       = λ ()
boolFilter-⊆ p (x ∷ xs) with p x | boolFilter-⊆ p xs
... | false | hyp = there ∘ hyp
... | true  | hyp =
  λ { (here  eq)      → here eq
    ; (there ∈boolFilter) → there (hyp ∈boolFilter)
    }
