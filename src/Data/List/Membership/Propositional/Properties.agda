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
open import Algebra.FunctionProperties using (Op₂; Selective)
open import Category.Monad using (RawMonad)
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Fin using (Fin)
open import Data.List as List
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Any.Properties
open import Data.List.Membership.Propositional
import Data.List.Membership.Setoid.Properties as Membershipₛ
open import Data.List.Relation.Equality.Propositional
  using (_≋_; ≡⇒≋; ≋⇒≡)
open import Data.List.Categorical using (monad)
open import Data.Nat using (ℕ; zero; suc; pred; s≤s; _≤_; _<_; _≤?_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Product.Relation.Pointwise.NonDependent using (_×-cong_)
import Data.Product.Relation.Pointwise.Dependent as Σ
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalence)
open import Function.Injection using (Injection; Injective; _↣_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; subst; →-to-⟶; _≗_)
import Relation.Binary.Properties.DecTotalOrder as DTOProperties
open import Relation.Unary using (_⟨×⟩_; Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

------------------------------------------------------------------------
-- Publicly re-export properties from Core

open import Data.List.Membership.Propositional.Properties.Core public

------------------------------------------------------------------------
-- Equality

module _ {a} {A : Set a} where

  ∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
  ∈-resp-≋ = Membershipₛ.∈-resp-≋ (P.setoid A)

  ∉-resp-≋ : ∀ {x} → (x ∉_) Respects _≋_
  ∉-resp-≋ = Membershipₛ.∉-resp-≋ (P.setoid A)

------------------------------------------------------------------------
-- mapWith∈

module _ {a b} {A : Set a} {B : Set b} where

  mapWith∈-cong : ∀ (xs : List A) → (f g : ∀ {x} → x ∈ xs → B) →
                  (∀ {x} → (x∈xs : x ∈ xs) → f x∈xs ≡ g x∈xs) →
                  mapWith∈ xs f ≡ mapWith∈ xs g
  mapWith∈-cong []       f g cong = refl
  mapWith∈-cong (x ∷ xs) f g cong = P.cong₂ _∷_ (cong (here refl))
    (mapWith∈-cong xs (f ∘ there) (g ∘ there) (cong ∘ there))

  mapWith∈≗map : ∀ f xs → mapWith∈ xs (λ {x} _ → f x) ≡ map f xs
  mapWith∈≗map f xs =
    ≋⇒≡ (Membershipₛ.mapWith∈≗map (P.setoid A) (P.setoid B) f xs)

------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} {f : A → B} where

  ∈-map⁺ : ∀ {x xs} → x ∈ xs → f x ∈ map f xs
  ∈-map⁺ = Membershipₛ.∈-map⁺ (P.setoid A) (P.setoid B) (P.cong f)

  ∈-map⁻ : ∀ {y xs} → y ∈ map f xs → ∃ λ x → x ∈ xs × y ≡ f x
  ∈-map⁻ = Membershipₛ.∈-map⁻ (P.setoid A) (P.setoid B)

  map-∈↔ : ∀ {y xs} → (∃ λ x → x ∈ xs × y ≡ f x) ↔ y ∈ map f xs
  map-∈↔ {y} {xs} =
    (∃ λ x → x ∈ xs × y ≡ f x)   ↔⟨ Any↔ ⟩
    Any (λ x → y ≡ f x) xs       ↔⟨ map↔ ⟩
    y ∈ List.map f xs            ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _++_

module _ {a} (A : Set a) {v : A} where

  ∈-++⁺ˡ : ∀ {xs ys} → v ∈ xs → v ∈ xs ++ ys
  ∈-++⁺ˡ = Membershipₛ.∈-++⁺ˡ (P.setoid A)

  ∈-++⁺ʳ : ∀ xs {ys} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ = Membershipₛ.∈-++⁺ʳ (P.setoid A)

  ∈-++⁻ : ∀ xs {ys} → v ∈ xs ++ ys → (v ∈ xs) ⊎ (v ∈ ys)
  ∈-++⁻ = Membershipₛ.∈-++⁻ (P.setoid A)

  ∈-insert : ∀ xs {ys} → v ∈ xs ++ [ v ] ++ ys
  ∈-insert xs = Membershipₛ.∈-insert (P.setoid A) xs refl

  ∈-∃++ : ∀ {xs} → v ∈ xs → ∃₂ λ ys zs → xs ≡ ys ++ [ v ] ++ zs
  ∈-∃++ v∈xs with Membershipₛ.∈-∃++ (P.setoid A) v∈xs
  ... | ys , zs , _ , refl , eq = ys , zs , ≋⇒≡ eq

------------------------------------------------------------------------
-- concat

module _ {a} {A : Set a} {v : A} where

  ∈-concat⁺ : ∀ {xss} → Any (v ∈_) xss → v ∈ concat xss
  ∈-concat⁺ = Membershipₛ.∈-concat⁺ (P.setoid A)

  ∈-concat⁻ : ∀ xss → v ∈ concat xss → Any (v ∈_) xss
  ∈-concat⁻ = Membershipₛ.∈-concat⁻ (P.setoid A)

  ∈-concat⁺′ : ∀ {vs xss} → v ∈ vs → vs ∈ xss → v ∈ concat xss
  ∈-concat⁺′ v∈vs vs∈xss =
    Membershipₛ.∈-concat⁺′ (P.setoid A) v∈vs (Any.map ≡⇒≋ vs∈xss)

  ∈-concat⁻′ : ∀ xss → v ∈ concat xss → ∃ λ xs → v ∈ xs × xs ∈ xss
  ∈-concat⁻′ xss v∈c with Membershipₛ.∈-concat⁻′ (P.setoid A) xss v∈c
  ... | xs , v∈xs , xs∈xss = xs , v∈xs , Any.map ≋⇒≡ xs∈xss

  concat-∈↔ : ∀ {xss : List (List A)} →
              (∃ λ xs → v ∈ xs × xs ∈ xss) ↔ v ∈ concat xss
  concat-∈↔ {xss} =
    (∃ λ xs → v ∈ xs × xs ∈ xss)  ↔⟨ Σ.cong Inv.id $ ×-comm _ _ ⟩
    (∃ λ xs → xs ∈ xss × v ∈ xs)  ↔⟨ Any↔ ⟩
    Any (Any (v ≡_)) xss          ↔⟨ concat↔ ⟩
    v ∈ concat xss                ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- applyUpTo

module _ {a} {A : Set a} where

  ∈-applyUpTo⁺ : ∀ (f : ℕ → A) {i n} → i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo⁺ = Membershipₛ.∈-applyUpTo⁺ (P.setoid A)

  ∈-applyUpTo⁻ : ∀ {v} f {n} → v ∈ applyUpTo f n →
                 ∃ λ i → i < n × v ≡ f i
  ∈-applyUpTo⁻ = Membershipₛ.∈-applyUpTo⁻ (P.setoid A)

------------------------------------------------------------------------
-- tabulate

module _ {a} {A : Set a} where

  ∈-tabulate⁺ : ∀ {n} {f : Fin n → A} i → f i ∈ tabulate f
  ∈-tabulate⁺ = Membershipₛ.∈-tabulate⁺ (P.setoid A)

  ∈-tabulate⁻ : ∀ {n} {f : Fin n → A} {v} →
                v ∈ tabulate f → ∃ λ i → v ≡ f i
  ∈-tabulate⁻ = Membershipₛ.∈-tabulate⁻ (P.setoid A)

------------------------------------------------------------------------
-- filter

module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

  ∈-filter⁺ : ∀ {x xs} → x ∈ xs → P x → x ∈ filter P? xs
  ∈-filter⁺ = Membershipₛ.∈-filter⁺ (P.setoid A) P? (P.subst P)

  ∈-filter⁻ : ∀ {v xs} → v ∈ filter P? xs → v ∈ xs × P v
  ∈-filter⁻ = Membershipₛ.∈-filter⁻ (P.setoid A) P? (P.subst P)

------------------------------------------------------------------------
-- _>>=_

module _ {ℓ} {A B : Set ℓ} where

  >>=-∈↔ : ∀ {xs} {f : A → List B} {y} →
           (∃ λ x → x ∈ xs × y ∈ f x) ↔ y ∈ (xs >>= f)
  >>=-∈↔ {xs = xs} {f} {y} =
    (∃ λ x → x ∈ xs × y ∈ f x)  ↔⟨ Any↔ ⟩
    Any (Any (y ≡_) ∘ f) xs     ↔⟨ >>=↔ ⟩
    y ∈ (xs >>= f)              ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⊛_

module _ {ℓ} {A B : Set ℓ} where

  ⊛-∈↔ : ∀ (fs : List (A → B)) {xs y} →
         (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x) ↔ y ∈ (fs ⊛ xs)
  ⊛-∈↔ fs {xs} {y} =
    (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x)       ↔⟨ Σ.cong Inv.id (∃∃↔∃∃ _) ⟩
    (∃ λ f → f ∈ fs × ∃ λ x → x ∈ xs × y ≡ f x)  ↔⟨ Σ.cong Inv.id ((_ ∎) ⟨ _×-cong_ ⟩ Any↔) ⟩
    (∃ λ f → f ∈ fs × Any (_≡_ y ∘ f) xs)        ↔⟨ Any↔ ⟩
    Any (λ f → Any (_≡_ y ∘ f) xs) fs            ↔⟨ ⊛↔ ⟩
    y ∈ (fs ⊛ xs)                                ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⊗_

module _ {ℓ} {A B : Set ℓ} where

  ⊗-∈↔ : ∀ {xs ys} {x : A} {y : B} →
         (x ∈ xs × y ∈ ys) ↔ (x , y) ∈ (xs ⊗ ys)
  ⊗-∈↔ {xs} {ys} {x} {y} =
    (x ∈ xs × y ∈ ys)             ↔⟨ ⊗↔′ ⟩
    Any (x ≡_ ⟨×⟩ y ≡_) (xs ⊗ ys) ↔⟨ Any-cong ×-≡×≡↔≡,≡ (_ ∎) ⟩
    (x , y) ∈ (xs ⊗ ys)           ∎
    where
    open Related.EquationalReasoning

------------------------------------------------------------------------
-- length

module _ {a} {A : Set a} where

  ∈-length : ∀ {x xs} → x ∈ xs → 1 ≤ length xs
  ∈-length = Membershipₛ.∈-length (P.setoid A)

------------------------------------------------------------------------
-- lookup

module _ {a} {A : Set a} where

  ∈-lookup : ∀ xs i → lookup xs i ∈ xs
  ∈-lookup = Membershipₛ.∈-lookup (P.setoid A)

------------------------------------------------------------------------
-- foldr

module _ {a} {A : Set a} {_•_ : Op₂ A} where

  foldr-selective : Selective _≡_ _•_ → ∀ e xs →
                    (foldr _•_ e xs ≡ e) ⊎ (foldr _•_ e xs ∈ xs)
  foldr-selective = Membershipₛ.foldr-selective (P.setoid A)

------------------------------------------------------------------------
-- Other properties

-- Only a finite number of distinct elements can be members of a
-- given list.

module _ {a} {A : Set a} where

  finite : (f : ℕ ↣ A) → ∀ xs → ¬ (∀ i → Injection.to f ⟨$⟩ i ∈ xs)
  finite inj []       fᵢ∈[]   = ¬Any[] (fᵢ∈[] 0)
  finite inj (x ∷ xs) fᵢ∈x∷xs = excluded-middle helper
    where
    open Injection inj renaming (injective to f-inj)

    f : ℕ → A
    f = to ⟨$⟩_

    not-x : ∀ {i} → f i ≢ x → f i ∈ xs
    not-x {i} fᵢ≢x with fᵢ∈x∷xs i
    ... | here  fᵢ≡x  = contradiction fᵢ≡x fᵢ≢x
    ... | there fᵢ∈xs = fᵢ∈xs

    helper : ¬ Dec (∃ λ i → f i ≡ x)
    helper (no fᵢ≢x)        = finite inj  xs (λ i → not-x (fᵢ≢x ∘ _,_ i))
    helper (yes (i , fᵢ≡x)) = finite f′-inj xs f′ⱼ∈xs
      where
      f′ : ℕ → A
      f′ j with i ≤? j
      ... | yes i≤j = f (suc j)
      ... | no  i≰j = f j

      ∈-if-not-i : ∀ {j} → i ≢ j → f j ∈ xs
      ∈-if-not-i i≢j = not-x (i≢j ∘ f-inj ∘ trans fᵢ≡x ∘ sym)

      lemma : ∀ {k j} → i ≤ j → ¬ (i ≤ k) → suc j ≢ k
      lemma i≤j i≰1+j refl = i≰1+j (≤-step i≤j)

      f′ⱼ∈xs : ∀ j → f′ j ∈ xs
      f′ⱼ∈xs j with i ≤? j
      ... | yes i≤j = ∈-if-not-i (<⇒≢ (s≤s i≤j))
      ... | no  i≰j = ∈-if-not-i (<⇒≢ (≰⇒> i≰j) ∘ sym)

      f′-injective′ : Injective {B = P.setoid A} (→-to-⟶ f′)
      f′-injective′ {j} {k} eq with i ≤? j | i ≤? k
      ... | yes _   | yes _   = P.cong pred (f-inj eq)
      ... | yes i≤j | no  i≰k = contradiction (f-inj eq) (lemma i≤j i≰k)
      ... | no  i≰j | yes i≤k = contradiction (f-inj eq) (lemma i≤k i≰j ∘ sym)
      ... | no  _   | no  _   = f-inj eq

      f′-inj = record
        { to        = →-to-⟶ f′
        ; injective = f′-injective′
        }

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

filter-∈ = ∈-filter⁺

-- Please use `filter` instead of `boolFilter`
boolFilter-∈ : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) {x} →
           x ∈ xs → p x ≡ true → x ∈ boolFilter p xs
boolFilter-∈ p []       ()          _
boolFilter-∈ p (x ∷ xs) (here refl) px≡true rewrite px≡true = here refl
boolFilter-∈ p (y ∷ xs) (there pxs) px≡true with p y
... | true  = there (boolFilter-∈ p xs pxs px≡true)
... | false =        boolFilter-∈ p xs pxs px≡true
