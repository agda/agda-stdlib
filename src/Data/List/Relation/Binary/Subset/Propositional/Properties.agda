------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the sublist relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Subset.Propositional.Properties
  where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.List.Base using (List; map; _∷_; _++_; concat; applyUpTo;
  any; filter)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.Any.Properties as Any hiding (filter⁺)
open import Data.List.Effectful using (monad)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties
  using (map-∈↔; concat-∈↔; >>=-∈↔; ⊛-∈↔; ⊗-∈↔)
import Data.List.Relation.Binary.Subset.Setoid.Properties as Subset
open import Data.List.Relation.Binary.Subset.Propositional
  using (_⊆_; _⊇_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-sym; ↭-isEquivalence)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Permutation
open import Data.Nat.Base using (ℕ; _≤_)
import Data.Product.Base as Product
import Data.Sum.Base as Sum
open import Effect.Monad
open import Function.Base using (_∘_; _∘′_; id; _$_)
open import Function.Bundles using (_↔_; Inverse; Equivalence)
open import Level using (Level)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable; Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Definitions hiding (Decidable)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; subst; resp; refl)
open import Relation.Binary.PropositionalEquality.Properties
  using (isEquivalence; setoid; module ≡-Reasoning)
open import Relation.Binary.Structures using (IsPreorder)
import Relation.Binary.Reasoning.Preorder as ≲-Reasoning

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

  variable
    a b p q : Level
    A : Set a
    B : Set b
    ws xs ys zs : List A

------------------------------------------------------------------------
-- Relational properties with _≋_ (pointwise equality)
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
-- Relational properties with _↭_ (permutation)
------------------------------------------------------------------------
-- See issue #1354 for why these proofs can't be taken from `Subset`

⊆-reflexive-↭ : _↭_ {A = A} ⇒ _⊆_
⊆-reflexive-↭ xs↭ys = Permutation.∈-resp-↭ xs↭ys

⊆-respʳ-↭ : _⊆_ {A = A} Respectsʳ _↭_
⊆-respʳ-↭ xs↭ys = Permutation.∈-resp-↭ xs↭ys ∘_

⊆-respˡ-↭ : _⊆_ {A = A} Respectsˡ _↭_
⊆-respˡ-↭ xs↭ys = _∘ Permutation.∈-resp-↭ (↭-sym xs↭ys)

module _ (A : Set a) where

  ⊆-↭-isPreorder : IsPreorder {A = List A} _↭_ _⊆_
  ⊆-↭-isPreorder = record
    { isEquivalence = ↭-isEquivalence
    ; reflexive     = ⊆-reflexive-↭
    ; trans         = ⊆-trans
    }

  ⊆-↭-preorder : Preorder _ _ _
  ⊆-↭-preorder = record
    { isPreorder = ⊆-↭-isPreorder
    }

------------------------------------------------------------------------
-- Reasoning over subsets
------------------------------------------------------------------------

module ⊆-Reasoning (A : Set a) where
  open Subset.⊆-Reasoning (setoid A) public
    hiding (step-≋; step-≋˘)

------------------------------------------------------------------------
-- Properties of _⊆_ and various list predicates
------------------------------------------------------------------------

Any-resp-⊆ : ∀ {P : Pred A p} → (Any P) Respects _⊆_
Any-resp-⊆ = Subset.Any-resp-⊆ (setoid _) (subst _)

All-resp-⊇ : ∀ {P : Pred A p} → (All P) Respects _⊇_
All-resp-⊇ = Subset.All-resp-⊇ (setoid _) (subst _)

------------------------------------------------------------------------
-- Properties relating _⊆_ to various list functions
------------------------------------------------------------------------
-- map

map⁺ : ∀ (f : A → B) → xs ⊆ ys → map f xs ⊆ map f ys
map⁺ f xs⊆ys =
  Inverse.to (map-∈↔ f) ∘
  Product.map₂ (Product.map₁ xs⊆ys) ∘
  Inverse.from (map-∈↔ f)

------------------------------------------------------------------------
-- ∷

xs⊆x∷xs : ∀ (xs : List A) x → xs ⊆ x ∷ xs
xs⊆x∷xs = Subset.xs⊆x∷xs (setoid _)

∷⁺ʳ : ∀ x → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
∷⁺ʳ = Subset.∷⁺ʳ (setoid _)

∈-∷⁺ʳ : ∀ {x} → x ∈ ys → xs ⊆ ys → x ∷ xs ⊆ ys
∈-∷⁺ʳ = Subset.∈-∷⁺ʳ (setoid _)

------------------------------------------------------------------------
-- _++_

xs⊆xs++ys : ∀ (xs ys : List A) → xs ⊆ xs ++ ys
xs⊆xs++ys = Subset.xs⊆xs++ys (setoid _)

xs⊆ys++xs : ∀ (xs ys : List A) → xs ⊆ ys ++ xs
xs⊆ys++xs = Subset.xs⊆ys++xs (setoid _)

++⁺ʳ : ∀ zs → xs ⊆ ys → zs ++ xs ⊆ zs ++ ys
++⁺ʳ = Subset.++⁺ʳ (setoid _)

++⁺ˡ : ∀ zs → xs ⊆ ys → xs ++ zs ⊆ ys ++ zs
++⁺ˡ = Subset.++⁺ˡ (setoid _)

++⁺ : ws ⊆ xs → ys ⊆ zs → ws ++ ys ⊆ xs ++ zs
++⁺ = Subset.++⁺ (setoid _)

------------------------------------------------------------------------
-- concat

module _ {xss yss : List (List A)} where

  concat⁺ : xss ⊆ yss → concat xss ⊆ concat yss
  concat⁺ xss⊆yss =
    Inverse.to concat-∈↔ ∘
    Product.map₂ (Product.map₂ xss⊆yss) ∘
    Inverse.from concat-∈↔

------------------------------------------------------------------------
-- applyUpTo

applyUpTo⁺ : ∀ (f : ℕ → A) {m n} → m ≤ n → applyUpTo f m ⊆ applyUpTo f n
applyUpTo⁺ = Subset.applyUpTo⁺ (setoid _)

------------------------------------------------------------------------
-- _>>=_

module _ {A B : Set a} (f g : A → List B) where

  >>=⁺ : xs ⊆ ys → (∀ {x} → f x ⊆ g x) → (xs >>= f) ⊆ (ys >>= g)
  >>=⁺ xs⊆ys f⊆g =
    Inverse.to >>=-∈↔ ∘
    Product.map₂ (Product.map xs⊆ys f⊆g) ∘
    Inverse.from >>=-∈↔

------------------------------------------------------------------------
-- _⊛_

module _ {A B : Set a} {fs gs : List (A → B)} where

  ⊛⁺ : fs ⊆ gs → xs ⊆ ys → (fs ⊛ xs) ⊆ (gs ⊛ ys)
  ⊛⁺ fs⊆gs xs⊆ys =
    (Inverse.to $ ⊛-∈↔ gs) ∘
    Product.map₂ (Product.map₂ (Product.map fs⊆gs (Product.map₁ xs⊆ys))) ∘
    (Inverse.from $ ⊛-∈↔ fs)

------------------------------------------------------------------------
-- _⊗_

module _ {A B : Set a} {ws xs : List A} {ys zs : List B} where

  ⊗⁺ : ws ⊆ xs → ys ⊆ zs → (ws ⊗ ys) ⊆ (xs ⊗ zs)
  ⊗⁺ ws⊆xs ys⊆zs =
    Inverse.to ⊗-∈↔ ∘
    Product.map ws⊆xs ys⊆zs ∘
    Inverse.from ⊗-∈↔

------------------------------------------------------------------------
-- any

module _ (p : A → Bool) {xs ys} where

  any⁺ : xs ⊆ ys → T (any p xs) → T (any p ys)
  any⁺ xs⊆ys =
    Equivalence.to Any.any⇔ ∘
    Any-resp-⊆ xs⊆ys ∘
    Equivalence.from Any.any⇔

------------------------------------------------------------------------
-- mapWith∈

module _ {xs : List A} {f : ∀ {x} → x ∈ xs → B}
         {ys : List A} {g : ∀ {x} → x ∈ ys → B}
         where

  mapWith∈⁺ : (xs⊆ys : xs ⊆ ys) → (∀ {x} → f {x} ≗ g ∘ xs⊆ys) →
                mapWith∈ xs f ⊆ mapWith∈ ys g
  mapWith∈⁺ xs⊆ys f≈g {x} =
    Inverse.to Any.mapWith∈↔ ∘
    Product.map₂ (Product.map xs⊆ys (λ {x∈xs} x≡fx∈xs → begin
      x               ≡⟨ x≡fx∈xs ⟩
      f x∈xs          ≡⟨ f≈g x∈xs ⟩
      g (xs⊆ys x∈xs)  ∎)) ∘
    Inverse.from Any.mapWith∈↔
    where open ≡-Reasoning

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : Decidable P) where

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ = Subset.filter-⊆ (setoid A) P?

  module _ {Q : Pred A q} (Q? : Decidable Q) where

    filter⁺′ : P ⋐ Q → ∀ {xs ys} → xs ⊆ ys → filter P? xs ⊆ filter Q? ys
    filter⁺′ = Subset.filter⁺′ (setoid A) P? (resp P) Q? (resp Q)


------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------

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
map-with-∈-mono = mapWith∈⁺
{-# WARNING_ON_USAGE map-with-∈-mono
"Warning: map-with-∈-mono was deprecated in v1.5.
Please use mapWith∈⁺ instead."
#-}
map-with-∈⁺ = mapWith∈⁺
{-# WARNING_ON_USAGE map-with-∈⁺
"Warning: map-with-∈⁺ was deprecated in v2.0.
Please use mapWith∈⁺ instead."
#-}
filter⁺ = filter-⊆
{-# WARNING_ON_USAGE filter⁺
"Warning: filter⁺ was deprecated in v1.5.
Please use filter-⊆ instead."
#-}
