------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the membership predicate for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid)

module Data.List.Fresh.Membership.Setoid.Properties {c ℓ} (S : Setoid c ℓ) where

open import Level using (Level; _⊔_)
open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; fromInj₂)

open import Function using (id; _∘′_; _$_)
open import Relation.Nullary
open import Relation.Unary as U using (Pred)
import Relation.Binary as B
import Relation.Binary.PropositionalEquality as P
open import Relation.Nary

open import Data.List.Fresh
open import Data.List.Fresh.Properties
open import Data.List.Fresh.Membership.Setoid S
open import Data.List.Fresh.Relation.Unary.Any using (Any; here; there; _─_)
import Data.List.Fresh.Relation.Unary.Any.Properties as Anyₚ
import Data.List.Fresh.Relation.Unary.All.Properties as Allₚ

open Setoid S renaming (Carrier to A)

private
  variable
    p r : Level

------------------------------------------------------------------------
-- transport

module _ {R : Rel A r} where

  ≈-subst-∈ : ∀ {x y} {xs : List# A R} → x ≈ y → x ∈ xs → y ∈ xs
  ≈-subst-∈ x≈y (here x≈x′)  = here (trans (sym x≈y) x≈x′)
  ≈-subst-∈ x≈y (there x∈xs) = there (≈-subst-∈ x≈y x∈xs)

------------------------------------------------------------------------
-- relationship to fresh

module _ {R : Rel A r} (R⇒≉ : ∀[ R ⇒ _≉_ ]) where

  fresh⇒∉ : ∀ {x} {xs : List# A R} → x # xs → x ∉ xs
  fresh⇒∉ (r , _)    (here x≈y)   = R⇒≉ r x≈y
  fresh⇒∉ (_ , x#xs) (there x∈xs) = fresh⇒∉ x#xs x∈xs

------------------------------------------------------------------------
-- disjointness

module _ {R : Rel A r} where

  distinct : ∀ {x y} {xs : List# A R} → x ∈ xs → y ∉ xs → x ≉ y
  distinct x∈xs y∉xs x≈y = y∉xs (≈-subst-∈ x≈y x∈xs)

------------------------------------------------------------------------
-- remove

module _ {R : Rel A r} where

  remove-inv : ∀ {x y} {xs : List# A R} (x∈xs : x ∈ xs) →
               y ∈ xs → x ≈ y ⊎ y ∈ (xs ─ x∈xs)
  remove-inv (here x≈z)   (here y≈z)   = inj₁ (trans x≈z (sym y≈z))
  remove-inv (here _)     (there y∈xs) = inj₂ y∈xs
  remove-inv (there _)    (here y≈z)   = inj₂ (here y≈z)
  remove-inv (there x∈xs) (there y∈xs) = Sum.map₂ there (remove-inv x∈xs y∈xs)

  ∈-remove : ∀ {x y} {xs : List# A R} (x∈xs : x ∈ xs) → y ∈ xs → x ≉ y → y ∈ (xs ─ x∈xs)
  ∈-remove x∈xs y∈xs x≉y = fromInj₂ (⊥-elim ∘′ x≉y) (remove-inv x∈xs y∈xs)

module _ {R : Rel A r} (R⇒≉ : ∀[ R ⇒ _≉_ ]) (≉⇒R : ∀[ _≉_ ⇒ R ]) where

  private
    R≈ : R B.Respectsˡ _≈_
    R≈ x≈y Rxz = ≉⇒R (R⇒≉ Rxz ∘′ trans x≈y)

  fresh-remove : ∀ {x} {xs : List# A R} (x∈xs : x ∈ xs) → x # (xs ─ x∈xs)
  fresh-remove {xs = cons x xs pr} (here x≈y)   = fresh-respectsˡ R≈ (sym x≈y) pr
  fresh-remove {xs = cons x xs pr} (there x∈xs) =
    ≉⇒R (distinct x∈xs (fresh⇒∉ R⇒≉ pr)) , fresh-remove x∈xs

  ∉-remove : ∀ {x} {xs : List# A R} (x∈xs : x ∈ xs) → x ∉ (xs ─ x∈xs)
  ∉-remove x∈xs = fresh⇒∉ R⇒≉ (fresh-remove x∈xs)

------------------------------------------------------------------------
-- injection

module _ {R : Rel A r} (R⇒≉ : ∀[ R ⇒ _≉_ ]) where

  injection : ∀ {xs ys : List# A R} (inj : ∀ {x} → x ∈ xs → x ∈ ys) →
              length xs ≤ length ys
  injection {[]}                 {ys} inj = z≤n
  injection {xxs@(cons x xs pr)} {ys} inj = begin
    length xxs               ≤⟨ s≤s (injection step) ⟩
    suc (length (ys ─ x∈ys)) ≡⟨ P.sym (Anyₚ.length-remove x∈ys) ⟩
    length ys                ∎

    where

    open ≤-Reasoning

    x∉xs : x ∉ xs
    x∉xs = fresh⇒∉ R⇒≉ pr

    x∈ys : x ∈ ys
    x∈ys = inj (here refl)

    step : ∀ {y} → y ∈ xs → y ∈ (ys ─ x∈ys)
    step {y} y∈xs = ∈-remove x∈ys (inj (there y∈xs)) (distinct y∈xs x∉xs ∘′ sym)

  strict-injection : ∀ {xs ys : List# A R} (inj : ∀ {x} → x ∈ xs → x ∈ ys) →
   (∃ λ x → x ∈ ys × x ∉ xs) → length xs < length ys
  strict-injection {xs} {ys} inj (x , x∈ys , x∉xs) = begin
    suc (length xs)          ≤⟨ s≤s (injection step) ⟩
    suc (length (ys ─ x∈ys)) ≡⟨ P.sym (Anyₚ.length-remove x∈ys) ⟩
    length ys                ∎

    where

    open ≤-Reasoning

    step : ∀ {y} → y ∈ xs → y ∈ (ys ─ x∈ys)
    step {y} y∈xs = fromInj₂ (λ x≈y → ⊥-elim (x∉xs (≈-subst-∈ (sym x≈y) y∈xs)))
                  $ remove-inv x∈ys (inj y∈xs)


------------------------------------------------------------------------
-- proof irrelevance

module _ {R : Rel A r} (R⇒≉ : ∀[ R ⇒ _≉_ ]) (≈-irrelevant : B.Irrelevant _≈_) where

  ∈-irrelevant : ∀ {x} {xs : List# A R} → Irrelevant (x ∈ xs)
  -- positive cases
  ∈-irrelevant (here x≈y₁)   (here x≈y₂)   = P.cong here (≈-irrelevant x≈y₁ x≈y₂)
  ∈-irrelevant (there x∈xs₁) (there x∈xs₂) = P.cong there (∈-irrelevant x∈xs₁ x∈xs₂)
  -- absurd cases
  ∈-irrelevant {xs = cons x xs pr} (here x≈y)    (there x∈xs₂) =
    ⊥-elim (distinct x∈xs₂ (fresh⇒∉ R⇒≉ pr) x≈y)
  ∈-irrelevant {xs = cons x xs pr} (there x∈xs₁) (here x≈y)    =
    ⊥-elim (distinct x∈xs₁ (fresh⇒∉ R⇒≉ pr) x≈y)
