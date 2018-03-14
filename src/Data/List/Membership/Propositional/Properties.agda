------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership
------------------------------------------------------------------------

-- This module does not  treat the general variant of list membership,
-- parametrised on a setoid, only the variant where the equality is
-- fixed to be propositional equality.

module Data.List.Membership.Propositional.Properties where

open import Algebra using (CommutativeSemiring)
open import Category.Monad using (RawMonad)
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Empty using (⊥-elim)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalence)
open import Function.Injection as Inj using (_↣_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Data.List as List
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Any.Properties
open import Data.List.Membership.Propositional
import Data.List.Membership.Setoid.Properties as Membershipₚ
open import Data.List.Categorical using (monad)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
import Data.Product.Relation.Pointwise.Dependent as Σ
open import Data.Sum as Sum hiding (map)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; _≗_)
import Relation.Binary.Properties.DecTotalOrder as DTOProperties
open import Relation.Unary using (_⟨×⟩_; Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation

private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

------------------------------------------------------------------------
-- Properties relating _∈_ to various list functions
------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} {f : A → B} where

  ∈-map⁺ : ∀ {x xs} → x ∈ xs → f x ∈ map f xs
  ∈-map⁺ = Membershipₚ.∈-map⁺ (P.setoid _) (P.setoid _) (P.cong f)

  ∈-map⁻ : ∀ {y xs} → y ∈ map f xs → ∃ λ x → x ∈ xs × y ≡ f x
  ∈-map⁻ = Membershipₚ.∈-map⁻ (P.setoid _) (P.setoid _)

  map-∈↔ : ∀ {y xs} → (∃ λ x → x ∈ xs × y ≡ f x) ↔ y ∈ map f xs
  map-∈↔ {y} {xs} =
    (∃ λ x → x ∈ xs × y ≡ f x)   ↔⟨ Any↔ ⟩
    Any (λ x → y ≡ f x) xs       ↔⟨ map↔ ⟩
    y ∈ List.map f xs            ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- concat

module _ {a} {A : Set a} {x : A} {xss : List (List A)} where

  concat-∈↔ : (∃ λ xs → x ∈ xs × xs ∈ xss) ↔ x ∈ concat xss
  concat-∈↔ =
    (∃ λ xs → x ∈ xs × xs ∈ xss)  ↔⟨ Σ.cong Inv.id $ ×⊎.*-comm _ _ ⟩
    (∃ λ xs → xs ∈ xss × x ∈ xs)  ↔⟨ Any↔ ⟩
    Any (Any (x ≡_)) xss          ↔⟨ concat↔ ⟩
    x ∈ concat xss                ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- filter

filter-∈ : ∀ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) →
           ∀ {x xs} → x ∈ xs → P x → x ∈ filter P? xs
filter-∈ P? {xs = []}      ()          _
filter-∈ P? {xs = x ∷ xs} (here refl) Px with P? x
... | yes _  = here refl
... | no ¬Px = contradiction Px ¬Px
filter-∈ P? {xs = y ∷ xs} (there x∈xs) Px with P? y
... | yes _ = there (filter-∈ P? x∈xs Px)
... | no  _ = filter-∈ P? x∈xs Px

------------------------------------------------------------------------
-- Other monad functions

>>=-∈↔ : ∀ {ℓ} {A B : Set ℓ} {xs} {f : A → List B} {y} →
         (∃ λ x → x ∈ xs × y ∈ f x) ↔ y ∈ (xs >>= f)
>>=-∈↔ {ℓ} {xs = xs} {f} {y} =
  (∃ λ x → x ∈ xs × y ∈ f x)  ↔⟨ Any↔ ⟩
  Any (Any (y ≡_) ∘ f) xs     ↔⟨ >>=↔ ⟩
  y ∈ (xs >>= f)              ∎
  where open Related.EquationalReasoning

⊛-∈↔ : ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) {xs y} →
       (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x) ↔ y ∈ (fs ⊛ xs)
⊛-∈↔ {ℓ} fs {xs} {y} =
  (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x)       ↔⟨ Σ.cong Inv.id (∃∃↔∃∃ _) ⟩
  (∃ λ f → f ∈ fs × ∃ λ x → x ∈ xs × y ≡ f x)  ↔⟨ Σ.cong Inv.id ((_ ∎) ⟨ ×⊎.*-cong ⟩ Any↔) ⟩
  (∃ λ f → f ∈ fs × Any (_≡_ y ∘ f) xs)        ↔⟨ Any↔ ⟩
  Any (λ f → Any (_≡_ y ∘ f) xs) fs            ↔⟨ ⊛↔ ⟩
  y ∈ (fs ⊛ xs)                                ∎
  where open Related.EquationalReasoning

⊗-∈↔ : ∀ {A B : Set} {xs ys} {x : A} {y : B} →
       (x ∈ xs × y ∈ ys) ↔ (x , y) ∈ (xs ⊗ ys)
⊗-∈↔ {A} {B} {xs} {ys} {x} {y} =
  (x ∈ xs × y ∈ ys)                ↔⟨ ⊗↔′ ⟩
  Any (_≡_ x ⟨×⟩ _≡_ y) (xs ⊗ ys)  ↔⟨ Any-cong helper (_ ∎) ⟩
  (x , y) ∈ (xs ⊗ ys)              ∎
  where
  open Related.EquationalReasoning

  helper : (p : A × B) → (x ≡ proj₁ p × y ≡ proj₂ p) ↔ (x , y) ≡ p
  helper (x′ , y′) = record
    { to         = P.→-to-⟶ (uncurry $ P.cong₂ _,_)
    ; from       = P.→-to-⟶ < P.cong proj₁ , P.cong proj₂ >
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.cong₂ _,_ (P.≡-irrelevance _ _)
                                             (P.≡-irrelevance _ _)
      ; right-inverse-of = λ _ → P.≡-irrelevance _ _
      }
    }

------------------------------------------------------------------------
-- Other properties

-- Only a finite number of distinct elements can be members of a
-- given list.

finite : ∀ {a} {A : Set a} (f : ℕ ↣ A) →
         ∀ xs → ¬ (∀ i → Inj.Injection.to f ⟨$⟩ i ∈ xs)
finite         inj []       ∈[]   with ∈[] zero
... | ()
finite {A = A} inj (x ∷ xs) ∈x∷xs = excluded-middle helper
  where
  open Inj.Injection inj

  module STO = StrictTotalOrder
                 (DTOProperties.strictTotalOrder ≤-decTotalOrder)

  not-x : ∀ {i} → ¬ (to ⟨$⟩ i ≡ x) → to ⟨$⟩ i ∈ xs
  not-x {i} ≢x with ∈x∷xs i
  ... | here  ≡x  = ⊥-elim (≢x ≡x)
  ... | there ∈xs = ∈xs

  helper : ¬ Dec (∃ λ i → to ⟨$⟩ i ≡ x)
  helper (no ≢x)        = finite inj  xs (λ i → not-x (≢x ∘ _,_ i))
  helper (yes (i , ≡x)) = finite inj′ xs ∈xs
    where
    open P

    f : ℕ → A
    f j with STO.compare i j
    f j | tri< _ _ _ = to ⟨$⟩ suc j
    f j | tri≈ _ _ _ = to ⟨$⟩ suc j
    f j | tri> _ _ _ = to ⟨$⟩ j

    ∈-if-not-i : ∀ {j} → i ≢ j → to ⟨$⟩ j ∈ xs
    ∈-if-not-i i≢j = not-x (i≢j ∘ injective ∘ trans ≡x ∘ sym)

    lemma : ∀ {k j} → k ≤ j → suc j ≢ k
    lemma 1+j≤j refl = 1+n≰n 1+j≤j

    ∈xs : ∀ j → f j ∈ xs
    ∈xs j with STO.compare i j
    ∈xs j  | tri< (i≤j , _) _ _ = ∈-if-not-i (lemma i≤j ∘ sym)
    ∈xs j  | tri> _ i≢j _       = ∈-if-not-i i≢j
    ∈xs .i | tri≈ _ refl _      =
      ∈-if-not-i (m≢1+m+n i ∘
                  subst (_≡_ i ∘ suc) (sym (+-identityʳ i)))

    injective′ : Inj.Injective {B = P.setoid A} (→-to-⟶ f)
    injective′ {j} {k} eq with STO.compare i j | STO.compare i k
    ... | tri< _ _ _         | tri< _ _ _         = cong pred                                   $ injective eq
    ... | tri< _ _ _         | tri≈ _ _ _         = cong pred                                   $ injective eq
    ... | tri< (i≤j , _) _ _ | tri> _ _ (k≤i , _) = ⊥-elim (lemma (≤-trans k≤i i≤j)           $ injective eq)
    ... | tri≈ _ _ _         | tri< _ _ _         = cong pred                                   $ injective eq
    ... | tri≈ _ _ _         | tri≈ _ _ _         = cong pred                                   $ injective eq
    ... | tri≈ _ i≡j _       | tri> _ _ (k≤i , _) = ⊥-elim (lemma (subst (_≤_ k) i≡j k≤i)       $ injective eq)
    ... | tri> _ _ (j≤i , _) | tri< (i≤k , _) _ _ = ⊥-elim (lemma (≤-trans j≤i i≤k)     $ sym $ injective eq)
    ... | tri> _ _ (j≤i , _) | tri≈ _ i≡k _       = ⊥-elim (lemma (subst (_≤_ j) i≡k j≤i) $ sym $ injective eq)
    ... | tri> _ _ (j≤i , _) | tri> _ _ (k≤i , _) =                                               injective eq

    inj′ = record
      { to        = →-to-⟶ {B = P.setoid A} f
      ; injective = injective′
      }

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use `filter` instead of `boolFilter`

boolFilter-∈ : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) {x} →
           x ∈ xs → p x ≡ true → x ∈ boolFilter p xs
boolFilter-∈ p []       ()          _
boolFilter-∈ p (x ∷ xs) (here refl) px≡true rewrite px≡true = here refl
boolFilter-∈ p (y ∷ xs) (there pxs) px≡true with p y
... | true  = there (boolFilter-∈ p xs pxs px≡true)
... | false =        boolFilter-∈ p xs pxs px≡true
