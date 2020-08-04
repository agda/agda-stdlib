------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Delay type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Delay.Properties where

open import Size
import Data.Sum.Base as Sum
import Data.Nat as ℕ
open import Codata.Thunk using (Thunk; force)
open import Codata.Conat
open import Codata.Conat.Bisimilarity as Coℕ using (zero ; suc)
open import Codata.Delay
open import Codata.Delay.Bisimilarity
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module _ {a} {A : Set a} where

 length-never : ∀ {i} → i Coℕ.⊢ length (never {A = A}) ≈ infinity
 length-never = suc λ where .force → length-never

module _ {a b} {A : Set a} {B : Set b} where

 length-map : ∀ (f : A → B) da {i} → i Coℕ.⊢ length (map f da) ≈ length da
 length-map f (now a)    = zero
 length-map f (later da) = suc λ where .force → length-map f (da .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 length-zipWith : ∀ (f : A → B → C) da db {i} →
   i Coℕ.⊢ length (zipWith f da db) ≈ length da ⊔ length db
 length-zipWith f (now a)      db         = length-map (f a) db
 length-zipWith f da@(later _) (now b)    = length-map (λ a → f a b) da
 length-zipWith f (later da)   (later db) =
   suc λ where .force →  length-zipWith f (da .force) (db .force)

 map-map-fusion : ∀ (f : A → B) (g : B → C) da {i}  →
   i ⊢ map g (map f da) ≈ map (g ∘′ f) da
 map-map-fusion f g (now a)    = now Eq.refl
 map-map-fusion f g (later da) = later λ where .force → map-map-fusion f g (da .force)

 map-unfold-fusion : ∀ (f : B → C) n (s : A) {i} →
   i ⊢ map f (unfold n s) ≈ unfold (Sum.map id f ∘′ n) s
 map-unfold-fusion f n s with n s
 ... | Sum.inj₁ s′ = later λ where .force → map-unfold-fusion f n s′
 ... | Sum.inj₂ b  = now Eq.refl


⇓-unique : ∀ {a} → {A : Set a} →
           {d : Delay A ∞} →
           (d⇓₁ : d ⇓) → (d⇓₂ : d ⇓) →
           d⇓₁ ≡ d⇓₂
⇓-unique {d = now s} (now s) (now s) = Eq.refl
⇓-unique {d = later d'} (later l) (later r) =
  Eq.cong later (⇓-unique {d = force d'} l r)


bind⇓-injₗ : ∀ {a} {A B : Set a} →
             {d : Delay A ∞} {f : A → Delay B ∞} →
             bind d f ⇓ → d ⇓
bind⇓-injₗ {d = now s} foo = now s
bind⇓-injₗ {d = later s} (later foo) =
  later (bind⇓-injₗ foo)


bind⇓-injᵣ : ∀ {a} {A B : Set a}
             {d : Delay A ∞} {f : A → Delay B ∞} →
             (bind⇓ : bind d f ⇓) →
             f (extract (bind⇓-injₗ {d = d} {f = f} bind⇓)) ⇓
bind⇓-injᵣ {d = now s} foo = foo
bind⇓-injᵣ {d = later s} {f} (later foo) =
  bind⇓-injᵣ {d = force s} {f = f} foo


-- The extracted value of a bind is equivalent to the extracted value of its
-- second element
extract-bind-⇓ : ∀ {a} → {A B : Set a}
               {x : Delay A Size.∞} → {f : A → Delay B Size.∞} →
               (x⇓ : x ⇓) → (f⇓ : ((f (extract x⇓)) ⇓)) →
               extract (bind-⇓ x⇓ {f} f⇓) ≡ extract f⇓
extract-bind-⇓ (now a) f⇓ = Eq.refl
extract-bind-⇓ (later t) f⇓ = extract-bind-⇓ t f⇓

-- If the right element of a bind returns a certain value so does the entire
-- bind
extract[bind⇓-injᵣ[bind⇓]]≡extract[bind⇓] :
  ∀ {a} {A B : Set a} →
  {d : Delay A ∞} {f : A → Delay B ∞} →
  (bind⇓ : bind d f ⇓) →
  extract (bind⇓-injᵣ {d = d} bind⇓) ≡ extract bind⇓
extract[bind⇓-injᵣ[bind⇓]]≡extract[bind⇓] {d = now s} bind⇓ = Eq.refl
extract[bind⇓-injᵣ[bind⇓]]≡extract[bind⇓] {d = later s} {f} (later bind⇓) =
  extract[bind⇓-injᵣ[bind⇓]]≡extract[bind⇓] {d = force s} {f = f} bind⇓


-- Proof that the length of a bind-⇓ is equal to the sum of the length of its
-- components
bind⇓-length-add :
    ∀ {a} {A B : Set a} →
    {d : Delay A ∞} {f : A → Delay B ∞} →
    (bind⇓ : bind d f ⇓) →
    (d⇓ : d ⇓) → (f⇓ : f (extract d⇓) ⇓) →
    (toℕ (length-⇓ bind⇓)) ≡ ((toℕ (length-⇓ d⇓)) ℕ.+ (toℕ (length-⇓ f⇓)))
bind⇓-length-add {f = f} bind⇓ d⇓@(now s') f⇓ =
  Eq.cong (toℕ ∘ length-⇓) (⇓-unique bind⇓ f⇓)
bind⇓-length-add {d = d@(later dt)} {f = f} bind⇓@(later bind'⇓) d⇓@(later r) f⇓ =
  Eq.cong ℕ.suc (bind⇓-length-add bind'⇓ r f⇓)
