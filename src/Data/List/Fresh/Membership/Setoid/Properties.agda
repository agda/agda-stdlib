------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the membership predicate for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Fresh.Membership.Setoid.Properties {c ℓ} (S : Setoid c ℓ)
  where

open import Level using (Level)
open import Data.List.Fresh
open import Data.List.Fresh.Properties using (fresh-respectsˡ)
open import Data.List.Fresh.Membership.Setoid S using (_∈_; _∉_)
open import Data.List.Fresh.Relation.Unary.Any using (Any; here; there; _─_)
open import Data.List.Fresh.Relation.Unary.Any.Properties as List#
  using (length-remove)
open import Data.Nat.Base using (ℕ; suc; zero; _≤_; _<_; z≤n; s≤s; z<s; s<s)
open import Data.Nat.Properties using (module ≤-Reasoning)
open import Data.Product.Base using (∃; _×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; fromInj₂)
open import Function.Base using (id; _∘′_; _$_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions as Binary using (_Respectsˡ_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (cong)
open import Relation.Nary using (∀[_]; _⇒_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction; contradiction′)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Unary as Unary using (Pred)

open Setoid S renaming (Carrier to A)

private
  variable
    r : Level
    R : Rel A r
    x y : A
    xs : List# A R


------------------------------------------------------------------------
-- transport

≈-subst-∈ : x ≈ y → x ∈ xs → y ∈ xs
≈-subst-∈ x≈y (here x≈x′)  = here (trans (sym x≈y) x≈x′)
≈-subst-∈ x≈y (there x∈xs) = there (≈-subst-∈ x≈y x∈xs)

------------------------------------------------------------------------
-- relationship to fresh

module _ (R⇒≉ : ∀[ R ⇒ _≉_ ]) where

  fresh⇒∉ : x #[ R ] xs → x ∉ xs
  fresh⇒∉ (r , _)    (here x≈y)   = R⇒≉ r x≈y
  fresh⇒∉ (_ , x#xs) (there x∈xs) = fresh⇒∉ x#xs x∈xs

------------------------------------------------------------------------
-- disjointness

distinct : x ∈ xs → y ∉ xs → x ≉ y
distinct x∈xs y∉xs x≈y = y∉xs (≈-subst-∈ x≈y x∈xs)

------------------------------------------------------------------------
-- remove

remove-inv : (x∈xs : x ∈ xs) → y ∈ xs → x ≈ y ⊎ y ∈ (xs ─ x∈xs)
remove-inv (here x≈z)   (here y≈z)   = inj₁ (trans x≈z (sym y≈z))
remove-inv (here _)     (there y∈xs) = inj₂ y∈xs
remove-inv (there _)    (here y≈z)   = inj₂ (here y≈z)
remove-inv (there x∈xs) (there y∈xs) = Sum.map₂ there (remove-inv x∈xs y∈xs)

∈-remove : (x∈xs : x ∈ xs) → y ∈ xs → x ≉ y → y ∈ (xs ─ x∈xs)
∈-remove x∈xs y∈xs x≉y = fromInj₂ (contradiction′ x≉y) (remove-inv x∈xs y∈xs)

module _ (R⇒≉ : ∀[ R ⇒ _≉_ ]) (≉⇒R : ∀[ _≉_ ⇒ R ]) where

  private
    R≈ : R Binary.Respectsˡ _≈_
    R≈ x≈y Rxz = ≉⇒R (R⇒≉ Rxz ∘′ trans x≈y)

  fresh-remove : ∀ (x∈xs : x ∈ xs) → x #[ R ] (xs ─ x∈xs)
  fresh-remove {xs = cons x xs pr} (here x≈y)   = fresh-respectsˡ R≈ (sym x≈y) pr
  fresh-remove {xs = cons x xs pr} (there x∈xs) =
    ≉⇒R (distinct x∈xs (fresh⇒∉ R⇒≉ pr)) , fresh-remove x∈xs

  ∉-remove : ∀ {xs} (x∈xs : x ∈ xs) → x ∉ (xs ─ x∈xs)
  ∉-remove x∈xs = fresh⇒∉ R⇒≉ (fresh-remove x∈xs)

------------------------------------------------------------------------
-- injection

module _ (R⇒≉ : ∀[ R ⇒ _≉_ ]) where

  injection : ∀ {xs ys : List# A R} (inj : ∀ {x} → x ∈ xs → x ∈ ys) →
              length xs ≤ length ys
  injection {[]}                 {ys} inj = z≤n
  injection {xxs@(cons x xs pr)} {ys} inj = begin
    length xxs               ≤⟨ s≤s (injection step) ⟩
    suc (length (ys ─ x∈ys)) ≡⟨ length-remove x∈ys ⟨
    length ys                ∎

    where

    open ≤-Reasoning

    x∉xs : x ∉ xs
    x∉xs = fresh⇒∉ R⇒≉ pr

    x∈ys : x ∈ ys
    x∈ys = inj (here refl)

    step : y ∈ xs → y ∈ (ys ─ x∈ys)
    step y∈xs = ∈-remove x∈ys (inj (there y∈xs)) (distinct y∈xs x∉xs ∘′ sym)

  strict-injection : ∀ {xs ys : List# A R} (inj : ∀ {x} → x ∈ xs → x ∈ ys) →
   (∃ λ x → x ∈ ys × x ∉ xs) → length xs < length ys
  strict-injection {xs} {ys} inj (x , x∈ys , x∉xs) = begin
    suc (length xs)          ≤⟨ s≤s (injection step) ⟩
    suc (length (ys ─ x∈ys)) ≡⟨ length-remove x∈ys ⟨
    length ys                ∎

    where

    open ≤-Reasoning

    step : y ∈ xs → y ∈ (ys ─ x∈ys)
    step y∈xs = fromInj₂ (λ x≈y → contradiction ((≈-subst-∈ (sym x≈y) y∈xs)) x∉xs)
                $ remove-inv x∈ys (inj y∈xs)


------------------------------------------------------------------------
-- proof irrelevance

module _ (R⇒≉ : ∀[ R ⇒ _≉_ ]) (≈-irrelevant : Binary.Irrelevant _≈_) where

  ∈-irrelevant : ∀ {xs : List# A R} → Irrelevant (x ∈ xs)
  -- positive cases
  ∈-irrelevant (here x≈y₁)   (here x≈y₂)   = cong here (≈-irrelevant x≈y₁ x≈y₂)
  ∈-irrelevant (there x∈xs₁) (there x∈xs₂) = cong there (∈-irrelevant x∈xs₁ x∈xs₂)
  -- absurd cases
  ∈-irrelevant {xs = cons x xs pr} (here x≈y)    (there x∈xs₂) =
    contradiction x≈y (distinct x∈xs₂ (fresh⇒∉ R⇒≉ pr))
  ∈-irrelevant {xs = cons x xs pr} (there x∈xs₁) (here x≈y)    =
    contradiction x≈y (distinct x∈xs₁ (fresh⇒∉ R⇒≉ pr))
