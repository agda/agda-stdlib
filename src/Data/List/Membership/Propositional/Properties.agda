------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Membership.Propositional.Properties where

open import Algebra using (Op₂; Selective)
open import Category.Monad using (RawMonad)
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Fin.Base using (Fin)
open import Data.List.Base as List
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
import Data.List.Membership.Setoid.Properties as Membershipₛ
open import Data.List.Relation.Binary.Equality.Propositional
  using (_≋_; ≡⇒≋; ≋⇒≡)
open import Data.List.Categorical using (monad)
open import Data.Nat.Base using (ℕ; zero; suc; pred; s≤s; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Product.Function.NonDependent.Propositional using (_×-cong_)
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalence)
open import Function.Injection using (Injection; Injective; _↣_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Level using (Level)
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; subst; →-to-⟶; _≗_)
import Relation.Binary.Properties.DecTotalOrder as DTOProperties
open import Relation.Unary using (_⟨×⟩_; Decidable)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary using (¬_; Dec; does; yes; no; _because_)
open import Relation.Nullary.Negation

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

  variable
    ℓ : Level
    A B : Set ℓ

------------------------------------------------------------------------
-- Publicly re-export properties from Core

open import Data.List.Membership.Propositional.Properties.Core public

------------------------------------------------------------------------
-- Equality

∈-resp-≋ : ∀ {x : A} → (x ∈_) Respects _≋_
∈-resp-≋ = Membershipₛ.∈-resp-≋ (P.setoid _)

∉-resp-≋ : ∀ {x : A} → (x ∉_) Respects _≋_
∉-resp-≋ = Membershipₛ.∉-resp-≋ (P.setoid _)

------------------------------------------------------------------------
-- mapWith∈

mapWith∈-cong : ∀ (xs : List A) → (f g : ∀ {x} → x ∈ xs → B) →
                (∀ {x} → (x∈xs : x ∈ xs) → f x∈xs ≡ g x∈xs) →
                mapWith∈ xs f ≡ mapWith∈ xs g
mapWith∈-cong []       f g cong = refl
mapWith∈-cong (x ∷ xs) f g cong = P.cong₂ _∷_ (cong (here refl))
  (mapWith∈-cong xs (f ∘ there) (g ∘ there) (cong ∘ there))

mapWith∈≗map : ∀ (f : A → B) xs → mapWith∈ xs (λ {x} _ → f x) ≡ map f xs
mapWith∈≗map f xs =
  ≋⇒≡ (Membershipₛ.mapWith∈≗map (P.setoid _) (P.setoid _) f xs)

------------------------------------------------------------------------
-- map

module _ (f : A → B) where

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

module _ {v : A} where

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

module _ {v : A} where

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

module _ (f : ℕ → A) where

  ∈-applyUpTo⁺ : ∀ {i n} → i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo⁺ = Membershipₛ.∈-applyUpTo⁺ (P.setoid _) f

  ∈-applyUpTo⁻ : ∀ {v n} → v ∈ applyUpTo f n →
                 ∃ λ i → i < n × v ≡ f i
  ∈-applyUpTo⁻ = Membershipₛ.∈-applyUpTo⁻ (P.setoid _) f

------------------------------------------------------------------------
-- tabulate

module _ {n} {f : Fin n → A} where

  ∈-tabulate⁺ : ∀ i → f i ∈ tabulate f
  ∈-tabulate⁺ = Membershipₛ.∈-tabulate⁺ (P.setoid _)

  ∈-tabulate⁻ : ∀ {v} → v ∈ tabulate f → ∃ λ i → v ≡ f i
  ∈-tabulate⁻ = Membershipₛ.∈-tabulate⁻ (P.setoid _)

------------------------------------------------------------------------
-- filter

module _ {p} {P : A → Set p} (P? : Decidable P) where

  ∈-filter⁺ : ∀ {x xs} → x ∈ xs → P x → x ∈ filter P? xs
  ∈-filter⁺ = Membershipₛ.∈-filter⁺ (P.setoid A) P? (P.subst P)

  ∈-filter⁻ : ∀ {v xs} → v ∈ filter P? xs → v ∈ xs × P v
  ∈-filter⁻ = Membershipₛ.∈-filter⁻ (P.setoid A) P? (P.subst P)

------------------------------------------------------------------------
-- derun and deduplicate

module _ {r} {R : Rel A r} (R? : B.Decidable R) where

  ∈-derun⁻ : ∀ xs {z} → z ∈ derun R? xs → z ∈ xs
  ∈-derun⁻ xs z∈derun[R,xs] = Membershipₛ.∈-derun⁻ (P.setoid A) R? xs z∈derun[R,xs]

  ∈-deduplicate⁻ : ∀ xs {z} → z ∈ deduplicate R? xs → z ∈ xs
  ∈-deduplicate⁻ xs z∈dedup[R,xs] = Membershipₛ.∈-deduplicate⁻ (P.setoid A) R? xs z∈dedup[R,xs]

module _ (_≈?_ : B.Decidable {A = A} _≡_) where

  ∈-derun⁺ : ∀ {xs z} → z ∈ xs → z ∈ derun _≈?_ xs
  ∈-derun⁺ z∈xs = Membershipₛ.∈-derun⁺ (P.setoid A) _≈?_ (flip trans) z∈xs

  ∈-deduplicate⁺ : ∀ {xs z} → z ∈ xs → z ∈ deduplicate _≈?_ xs
  ∈-deduplicate⁺ z∈xs = Membershipₛ.∈-deduplicate⁺ (P.setoid A) _≈?_ (λ c≡b a≡b → trans a≡b (sym c≡b)) z∈xs

------------------------------------------------------------------------
-- _>>=_

>>=-∈↔ : ∀ {xs} {f : A → List B} {y} →
         (∃ λ x → x ∈ xs × y ∈ f x) ↔ y ∈ (xs >>= f)
>>=-∈↔ {xs = xs} {f} {y} =
  (∃ λ x → x ∈ xs × y ∈ f x)  ↔⟨ Any↔ ⟩
  Any (Any (y ≡_) ∘ f) xs     ↔⟨ >>=↔ ⟩
  y ∈ (xs >>= f)              ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⊛_

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

⊗-∈↔ : ∀ {xs ys} {x : A} {y : B} →
       (x ∈ xs × y ∈ ys) ↔ (x , y) ∈ (xs ⊗ ys)
⊗-∈↔ {xs = xs} {ys} {x} {y} =
  (x ∈ xs × y ∈ ys)             ↔⟨ ⊗↔′ ⟩
  Any (x ≡_ ⟨×⟩ y ≡_) (xs ⊗ ys) ↔⟨ Any-cong ×-≡×≡↔≡,≡ (_ ∎) ⟩
  (x , y) ∈ (xs ⊗ ys)           ∎
  where
  open Related.EquationalReasoning

------------------------------------------------------------------------
-- length

∈-length : ∀ {x : A} {xs} → x ∈ xs → 1 ≤ length xs
∈-length = Membershipₛ.∈-length (P.setoid _)

------------------------------------------------------------------------
-- lookup

∈-lookup : ∀ {xs : List A} i → lookup xs i ∈ xs
∈-lookup {xs = xs} i = Membershipₛ.∈-lookup (P.setoid _) xs i

------------------------------------------------------------------------
-- foldr

module _ {_•_ : Op₂ A} where

  foldr-selective : Selective _≡_ _•_ → ∀ e xs →
                    (foldr _•_ e xs ≡ e) ⊎ (foldr _•_ e xs ∈ xs)
  foldr-selective = Membershipₛ.foldr-selective (P.setoid A)

------------------------------------------------------------------------
-- allFin

∈-allFin : ∀ {n} (k : Fin n) → k ∈ allFin n
∈-allFin = ∈-tabulate⁺

------------------------------------------------------------------------
-- inits

[]∈inits : ∀ {a} {A : Set a} (as : List A) → [] ∈ inits as
[]∈inits []       = here refl
[]∈inits (a ∷ as) = here refl

------------------------------------------------------------------------
-- Other properties

-- Only a finite number of distinct elements can be members of a
-- given list.

finite : (f : ℕ ↣ A) → ∀ xs → ¬ (∀ i → Injection.to f ⟨$⟩ i ∈ xs)
finite inj []       fᵢ∈[]   = ¬Any[] (fᵢ∈[] 0)
finite inj (x ∷ xs) fᵢ∈x∷xs = excluded-middle helper
  where
  open Injection inj renaming (injective to f-inj)

  f : ℕ → _
  f = to ⟨$⟩_

  not-x : ∀ {i} → f i ≢ x → f i ∈ xs
  not-x {i} fᵢ≢x with fᵢ∈x∷xs i
  ... | here  fᵢ≡x  = contradiction fᵢ≡x fᵢ≢x
  ... | there fᵢ∈xs = fᵢ∈xs

  helper : ¬ Dec (∃ λ i → f i ≡ x)
  helper (no fᵢ≢x)        = finite inj  xs (λ i → not-x (fᵢ≢x ∘ _,_ i))
  helper (yes (i , fᵢ≡x)) = finite f′-inj xs f′ⱼ∈xs
    where
    f′ : ℕ → _
    f′ j with does (i ≤? j)
    ... | true  = f (suc j)
    ... | false = f j

    ∈-if-not-i : ∀ {j} → i ≢ j → f j ∈ xs
    ∈-if-not-i i≢j = not-x (i≢j ∘ f-inj ∘ trans fᵢ≡x ∘ sym)

    lemma : ∀ {k j} → i ≤ j → ¬ (i ≤ k) → suc j ≢ k
    lemma i≤j i≰1+j refl = i≰1+j (≤-step i≤j)

    f′ⱼ∈xs : ∀ j → f′ j ∈ xs
    f′ⱼ∈xs j with i ≤? j
    ... | yes i≤j = ∈-if-not-i (<⇒≢ (s≤s i≤j))
    ... | no  i≰j = ∈-if-not-i (<⇒≢ (≰⇒> i≰j) ∘ sym)

    f′-injective′ : Injective {B = P.setoid _} (→-to-⟶ f′)
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
-- Different members

there-injective-≢∈ : ∀ {xs} {x y z : A} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs} →
                     there {x = z} x∈xs ≢∈ there y∈xs →
                     x∈xs ≢∈ y∈xs
there-injective-≢∈ neq refl eq = neq refl (P.cong there eq)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

boolFilter-∈ : ∀ (p : A → Bool) (xs : List A) {x} →
           x ∈ xs → p x ≡ true → x ∈ boolFilter p xs
boolFilter-∈ p (x ∷ xs) (here refl) px≡true rewrite px≡true = here refl
boolFilter-∈ p (y ∷ xs) (there pxs) px≡true with p y
... | true  = there (boolFilter-∈ p xs pxs px≡true)
... | false =        boolFilter-∈ p xs pxs px≡true
{-# WARNING_ON_USAGE boolFilter-∈
"Warning: boolFilter was deprecated in v0.15.
Please use filter instead."
#-}

-- Version 0.16

filter-∈ = ∈-filter⁺
{-# WARNING_ON_USAGE filter-∈
"Warning: filter-∈ was deprecated in v0.16.
Please use ∈-filter⁺ instead."
#-}
