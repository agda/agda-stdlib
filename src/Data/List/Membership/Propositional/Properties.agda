------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Membership.Propositional.Properties where

open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Selective)
open import Data.Fin.Base using (Fin)
open import Data.List.Base as List
open import Data.List.Effectful using (monad)
open import Data.List.Membership.Propositional
  using (_∈_; _∉_; mapWith∈; _≢∈_)
import Data.List.Membership.Setoid.Properties as Membership
open import Data.List.Relation.Binary.Equality.Propositional
  using (_≋_; ≡⇒≋; ≋⇒≡)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties
  using (map↔; concat↔; >>=↔; ⊛↔; Any-cong; ⊗↔′; ¬Any[])
open import Data.Nat.Base using (ℕ; suc; s≤s; _≤_; _<_; _≰_)
open import Data.Nat.Properties
  using (suc-injective; m≤n⇒m≤1+n; _≤?_; <⇒≢; ≰⇒>)
open import Data.Product.Base using (∃; ∃₂; _×_; _,_)
open import Data.Product.Properties using (×-≡,≡↔≡)
open import Data.Product.Function.NonDependent.Propositional using (_×-cong_)
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Effect.Monad using (RawMonad)
open import Function.Base using (_∘_; _∘′_; _$_; id; flip; _⟨_⟩_)
open import Function.Definitions using (Injective)
import Function.Related.Propositional as Related
open import Function.Bundles using (_↔_; _↣_; Injection)
open import Function.Related.TypeIsomorphisms using (×-comm; ∃∃↔∃∃)
open import Function.Construct.Identity using (↔-id)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions as Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; resp; _≗_)
open import Relation.Binary.PropositionalEquality.Properties as ≡ using (setoid)
import Relation.Binary.Properties.DecTotalOrder as DTOProperties
open import Relation.Nullary.Decidable.Core
  using (Dec; yes; no; ¬¬-excluded-middle)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Unary using (_⟨×⟩_; Decidable)

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

  variable
    ℓ : Level
    A B C : Set ℓ

------------------------------------------------------------------------
-- Publicly re-export properties from Core

open import Data.List.Membership.Propositional.Properties.Core public

------------------------------------------------------------------------
-- Equality

∈-resp-≋ : ∀ {x : A} → (x ∈_) Respects _≋_
∈-resp-≋ = Membership.∈-resp-≋ (≡.setoid _)

∉-resp-≋ : ∀ {x : A} → (x ∉_) Respects _≋_
∉-resp-≋ = Membership.∉-resp-≋ (≡.setoid _)

------------------------------------------------------------------------
-- mapWith∈

mapWith∈-cong : ∀ (xs : List A) → (f g : ∀ {x} → x ∈ xs → B) →
                (∀ {x} → (x∈xs : x ∈ xs) → f x∈xs ≡ g x∈xs) →
                mapWith∈ xs f ≡ mapWith∈ xs g
mapWith∈-cong []       f g cong = refl
mapWith∈-cong (x ∷ xs) f g cong = cong₂ _∷_ (cong (here refl))
  (mapWith∈-cong xs (f ∘ there) (g ∘ there) (cong ∘ there))

mapWith∈≗map : ∀ (f : A → B) xs → mapWith∈ xs (λ {x} _ → f x) ≡ map f xs
mapWith∈≗map f xs =
  ≋⇒≡ (Membership.mapWith∈≗map (≡.setoid _) (≡.setoid _) f xs)

mapWith∈-id : (xs : List A) → mapWith∈ xs (λ {x} _ → x) ≡ xs
mapWith∈-id = Membership.mapWith∈-id (≡.setoid _)

map-mapWith∈ : (xs : List A) (f : ∀ {x} → x ∈ xs → B) (g : B → C) →
               map g (mapWith∈ xs f) ≡ mapWith∈ xs (g ∘′ f)
map-mapWith∈ = Membership.map-mapWith∈ (≡.setoid _)

------------------------------------------------------------------------
-- map

module _ (f : A → B) where

  ∈-map⁺ : ∀ {x xs} → x ∈ xs → f x ∈ map f xs
  ∈-map⁺ = Membership.∈-map⁺ (≡.setoid A) (≡.setoid B) (cong f)

  ∈-map⁻ : ∀ {y xs} → y ∈ map f xs → ∃ λ x → x ∈ xs × y ≡ f x
  ∈-map⁻ = Membership.∈-map⁻ (≡.setoid A) (≡.setoid B)

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
  ∈-++⁺ˡ = Membership.∈-++⁺ˡ (≡.setoid A)

  ∈-++⁺ʳ : ∀ xs {ys} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ = Membership.∈-++⁺ʳ (≡.setoid A)

  ∈-++⁻ : ∀ xs {ys} → v ∈ xs ++ ys → (v ∈ xs) ⊎ (v ∈ ys)
  ∈-++⁻ = Membership.∈-++⁻ (≡.setoid A)

  ∈-insert : ∀ xs {ys} → v ∈ xs ++ [ v ] ++ ys
  ∈-insert xs = Membership.∈-insert (≡.setoid A) xs refl

  ∈-∃++ : ∀ {xs} → v ∈ xs → ∃₂ λ ys zs → xs ≡ ys ++ [ v ] ++ zs
  ∈-∃++ v∈xs
    with ys , zs , _ , refl , eq ← Membership.∈-∃++ (≡.setoid A) v∈xs
    = ys , zs , ≋⇒≡ eq

------------------------------------------------------------------------
-- concat

module _ {v : A} where

  ∈-concat⁺ : ∀ {xss} → Any (v ∈_) xss → v ∈ concat xss
  ∈-concat⁺ = Membership.∈-concat⁺ (≡.setoid A)

  ∈-concat⁻ : ∀ xss → v ∈ concat xss → Any (v ∈_) xss
  ∈-concat⁻ = Membership.∈-concat⁻ (≡.setoid A)

  ∈-concat⁺′ : ∀ {vs xss} → v ∈ vs → vs ∈ xss → v ∈ concat xss
  ∈-concat⁺′ v∈vs vs∈xss =
    Membership.∈-concat⁺′ (≡.setoid A) v∈vs (Any.map ≡⇒≋ vs∈xss)

  ∈-concat⁻′ : ∀ xss → v ∈ concat xss → ∃ λ xs → v ∈ xs × xs ∈ xss
  ∈-concat⁻′ xss v∈c =
    let xs , v∈xs , xs∈xss = Membership.∈-concat⁻′ (≡.setoid A) xss v∈c
    in xs , v∈xs , Any.map ≋⇒≡ xs∈xss

  concat-∈↔ : ∀ {xss : List (List A)} →
              (∃ λ xs → v ∈ xs × xs ∈ xss) ↔ v ∈ concat xss
  concat-∈↔ {xss} =
    (∃ λ xs → v ∈ xs × xs ∈ xss)  ↔⟨ Σ.cong (↔-id _) $ ×-comm _ _ ⟩
    (∃ λ xs → xs ∈ xss × v ∈ xs)  ↔⟨ Any↔ ⟩
    Any (Any (v ≡_)) xss          ↔⟨ concat↔ ⟩
    v ∈ concat xss                ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- cartesianProductWith

module _ (f : A → B → C) where

  ∈-cartesianProductWith⁺ : ∀ {xs ys a b} → a ∈ xs → b ∈ ys →
                            f a b ∈ cartesianProductWith f xs ys
  ∈-cartesianProductWith⁺ = Membership.∈-cartesianProductWith⁺
    (≡.setoid A) (≡.setoid B) (≡.setoid C) (cong₂ f)

  ∈-cartesianProductWith⁻ : ∀ xs ys {v} → v ∈ cartesianProductWith f xs ys →
                            ∃₂ λ a b → a ∈ xs × b ∈ ys × v ≡ f a b
  ∈-cartesianProductWith⁻ = Membership.∈-cartesianProductWith⁻
    (≡.setoid A) (≡.setoid B) (≡.setoid C) f

------------------------------------------------------------------------
-- cartesianProduct

∈-cartesianProduct⁺ : ∀ {x : A} {y : B} {xs ys} → x ∈ xs → y ∈ ys →
                      (x , y) ∈ cartesianProduct xs ys
∈-cartesianProduct⁺ = ∈-cartesianProductWith⁺ _,_

∈-cartesianProduct⁻ : ∀ xs ys {xy@(x , y) : A × B} →
                      xy ∈ cartesianProduct xs ys → x ∈ xs × y ∈ ys
∈-cartesianProduct⁻ xs ys xy∈p[xs,ys]
  with _ , _ , x∈xs , y∈ys , refl ← ∈-cartesianProductWith⁻ _,_ xs ys xy∈p[xs,ys]
  = x∈xs , y∈ys

------------------------------------------------------------------------
-- applyUpTo

module _ (f : ℕ → A) where

  ∈-applyUpTo⁺ : ∀ {i n} → i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo⁺ = Membership.∈-applyUpTo⁺ (≡.setoid _) f

  ∈-applyUpTo⁻ : ∀ {v n} → v ∈ applyUpTo f n →
                 ∃ λ i → i < n × v ≡ f i
  ∈-applyUpTo⁻ = Membership.∈-applyUpTo⁻ (≡.setoid _) f

------------------------------------------------------------------------
-- upTo

∈-upTo⁺ : ∀ {n i} → i < n → i ∈ upTo n
∈-upTo⁺ = ∈-applyUpTo⁺ id

∈-upTo⁻ : ∀ {n i} → i ∈ upTo n → i < n
∈-upTo⁻ p with _ , i<n , refl ← ∈-applyUpTo⁻ id p = i<n

------------------------------------------------------------------------
-- applyDownFrom

module _ (f : ℕ → A) where

  ∈-applyDownFrom⁺ : ∀ {i n} → i < n → f i ∈ applyDownFrom f n
  ∈-applyDownFrom⁺ = Membership.∈-applyDownFrom⁺ (≡.setoid _) f

  ∈-applyDownFrom⁻ : ∀ {v n} → v ∈ applyDownFrom f n →
                     ∃ λ i → i < n × v ≡ f i
  ∈-applyDownFrom⁻ = Membership.∈-applyDownFrom⁻ (≡.setoid _) f

------------------------------------------------------------------------
-- downFrom

∈-downFrom⁺ : ∀ {n i} → i < n → i ∈ downFrom n
∈-downFrom⁺ i<n = ∈-applyDownFrom⁺ id i<n

∈-downFrom⁻ : ∀ {n i} → i ∈ downFrom n → i < n
∈-downFrom⁻ p with _ , i<n , refl ← ∈-applyDownFrom⁻ id p = i<n

------------------------------------------------------------------------
-- tabulate

module _ {n} {f : Fin n → A} where

  ∈-tabulate⁺ : ∀ i → f i ∈ tabulate f
  ∈-tabulate⁺ = Membership.∈-tabulate⁺ (≡.setoid _)

  ∈-tabulate⁻ : ∀ {v} → v ∈ tabulate f → ∃ λ i → v ≡ f i
  ∈-tabulate⁻ = Membership.∈-tabulate⁻ (≡.setoid _)

------------------------------------------------------------------------
-- filter

module _ {p} {P : A → Set p} (P? : Decidable P) where

  ∈-filter⁺ : ∀ {x xs} → x ∈ xs → P x → x ∈ filter P? xs
  ∈-filter⁺ = Membership.∈-filter⁺ (≡.setoid A) P? (≡.resp P)

  ∈-filter⁻ : ∀ {v xs} → v ∈ filter P? xs → v ∈ xs × P v
  ∈-filter⁻ = Membership.∈-filter⁻ (≡.setoid A) P? (≡.resp P)

------------------------------------------------------------------------
-- derun and deduplicate

module _ {r} {R : Rel A r} (R? : Binary.Decidable R) where

  ∈-derun⁻ : ∀ xs {z} → z ∈ derun R? xs → z ∈ xs
  ∈-derun⁻ xs z∈derun[R,xs] = Membership.∈-derun⁻ (≡.setoid A) R? xs z∈derun[R,xs]

  ∈-deduplicate⁻ : ∀ xs {z} → z ∈ deduplicate R? xs → z ∈ xs
  ∈-deduplicate⁻ xs z∈dedup[R,xs] = Membership.∈-deduplicate⁻ (≡.setoid A) R? xs z∈dedup[R,xs]

module _ (_≈?_ : DecidableEquality A) where

  ∈-derun⁺ : ∀ {xs z} → z ∈ xs → z ∈ derun _≈?_ xs
  ∈-derun⁺ z∈xs = Membership.∈-derun⁺ (≡.setoid A) _≈?_ (flip trans) z∈xs

  ∈-deduplicate⁺ : ∀ {xs z} → z ∈ xs → z ∈ deduplicate _≈?_ xs
  ∈-deduplicate⁺ z∈xs = Membership.∈-deduplicate⁺ (≡.setoid A) _≈?_ (λ c≡b a≡b → trans a≡b (sym c≡b)) z∈xs

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
  (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x)       ↔⟨ Σ.cong (↔-id _) (∃∃↔∃∃ _) ⟩
  (∃ λ f → f ∈ fs × ∃ λ x → x ∈ xs × y ≡ f x)  ↔⟨ Σ.cong (↔-id _) (↔-id _ ⟨ _×-cong_ ⟩ Any↔) ⟩
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
  Any (x ≡_ ⟨×⟩ y ≡_) (xs ⊗ ys) ↔⟨ Any-cong (λ _ → ×-≡,≡↔≡) (↔-id _) ⟩
  (x , y) ∈ (xs ⊗ ys)           ∎
  where
  open Related.EquationalReasoning

------------------------------------------------------------------------
-- length

∈-length : ∀ {x : A} {xs} → x ∈ xs → 0 < length xs
∈-length = Membership.∈-length (≡.setoid _)

------------------------------------------------------------------------
-- lookup

∈-lookup : ∀ {xs : List A} i → lookup xs i ∈ xs
∈-lookup {xs = xs} i = Membership.∈-lookup (≡.setoid _) xs i

------------------------------------------------------------------------
-- foldr

module _ {_•_ : Op₂ A} where

  foldr-selective : Selective _≡_ _•_ → ∀ e xs →
                    (foldr _•_ e xs ≡ e) ⊎ (foldr _•_ e xs ∈ xs)
  foldr-selective = Membership.foldr-selective (≡.setoid A)

------------------------------------------------------------------------
-- allFin

∈-allFin : ∀ {n} (k : Fin n) → k ∈ allFin n
∈-allFin = ∈-tabulate⁺

------------------------------------------------------------------------
-- inits

[]∈inits : ∀ {a} {A : Set a} (as : List A) → [] ∈ inits as
[]∈inits _ = here refl

------------------------------------------------------------------------
-- Other properties

-- Only a finite number of distinct elements can be members of a
-- given list.

finite : (inj : ℕ ↣ A) → ∀ xs → ¬ (∀ i → Injection.to inj i ∈ xs)
finite inj []       fᵢ∈[]   = ¬Any[] (fᵢ∈[] 0)
finite inj (x ∷ xs) fᵢ∈x∷xs = ¬¬-excluded-middle helper
  where
  open Injection inj renaming (injective to f-inj)

  f : ℕ → _
  f = to

  not-x : ∀ {i} → f i ≢ x → f i ∈ xs
  not-x {i} fᵢ≢x with fᵢ∈x∷xs i
  ... | here  fᵢ≡x  = contradiction fᵢ≡x fᵢ≢x
  ... | there fᵢ∈xs = fᵢ∈xs

  helper : ¬ Dec (∃ λ i → f i ≡ x)
  helper (no fᵢ≢x)        = finite inj  xs (λ i → not-x (fᵢ≢x ∘ _,_ i))
  helper (yes (i , fᵢ≡x)) = finite f′-inj xs f′ⱼ∈xs
    where
    f′ : ℕ → _
    f′ j with i ≤? j
    ... | yes _ = f (suc j)
    ... | no  _ = f j

    ∈-if-not-i : ∀ {j} → i ≢ j → f j ∈ xs
    ∈-if-not-i i≢j = not-x (i≢j ∘ f-inj ∘ trans fᵢ≡x ∘ sym)

    lemma : ∀ {k j} → i ≤ j → i ≰ k → suc j ≢ k
    lemma i≤j i≰1+j refl = i≰1+j (m≤n⇒m≤1+n i≤j)

    f′ⱼ∈xs : ∀ j → f′ j ∈ xs
    f′ⱼ∈xs j with i ≤? j
    ... | yes i≤j = ∈-if-not-i (<⇒≢ (s≤s i≤j))
    ... | no  i≰j = ∈-if-not-i (<⇒≢ (≰⇒> i≰j) ∘ sym)

    f′-injective′ : Injective _≡_ _≡_ f′
    f′-injective′ {j} {k} eq with i ≤? j | i ≤? k
    ... | yes i≤j | yes i≤k = suc-injective (f-inj eq)
    ... | yes i≤j | no  i≰k = contradiction (f-inj eq) (lemma i≤j i≰k)
    ... | no  i≰j | yes i≤k = contradiction (f-inj eq) (lemma i≤k i≰j ∘ sym)
    ... | no  i≰j | no  i≰k = f-inj eq

    f′-inj : ℕ ↣ _
    f′-inj = record
      { to        = f′
      ; cong      = ≡.cong f′
      ; injective = f′-injective′
      }

------------------------------------------------------------------------
-- Different members

there-injective-≢∈ : ∀ {xs} {x y z : A} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs} →
                     there {x = z} x∈xs ≢∈ there y∈xs →
                     x∈xs ≢∈ y∈xs
there-injective-≢∈ neq refl eq = neq refl (≡.cong there eq)
