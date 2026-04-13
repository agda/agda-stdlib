------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Delay type
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Codata.Sized.Delay.Properties where

open import Size
import Data.Sum.Base as Sum
import Data.Nat.Base as ℕ
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Conat using (Conat; zero; suc; infinity; _⊔_; toℕ)
open import Codata.Sized.Conat.Bisimilarity as Coℕ using (zero ; suc)
open import Codata.Sized.Delay
open import Codata.Sized.Delay.Bisimilarity using (now; later; _⊢_≈_)
open import Function.Base using (id; _∘′_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

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

 map-id : ∀ da {i} → i ⊢ map (id {A = A}) da ≈ da
 map-id (now a)    = now ≡.refl
 map-id (later da) = later λ where .force → map-id (da .force)

 map-∘ : ∀ (f : A → B) (g : B → C) da {i}  →
   i ⊢ map g (map f da) ≈ map (g ∘′ f) da
 map-∘ f g (now a)    = now ≡.refl
 map-∘ f g (later da) = later λ where .force → map-∘ f g (da .force)

 map-unfold : ∀ (f : B → C) n (s : A) {i} →
   i ⊢ map f (unfold n s) ≈ unfold (Sum.map id f ∘′ n) s
 map-unfold f n s with n s
 ... | Sum.inj₁ s′ = later λ where .force → map-unfold f n s′
 ... | Sum.inj₂ b = now ≡.refl


------------------------------------------------------------------------
-- ⇓

⇓-unique : ∀ {a} {A : Set a} →
           {d : Delay A ∞} →
           (d⇓₁ : d ⇓) → (d⇓₂ : d ⇓) →
           d⇓₁ ≡ d⇓₂
⇓-unique {d = now s} (now s) (now s) = ≡.refl
⇓-unique {d = later d'} (later l) (later r) =
  ≡.cong later (⇓-unique {d = force d'} l r)

module _ {a} {A B : Set a} where

  bind̅₁ : (d : Delay A ∞) {f : A → Delay B ∞} → bind d f ⇓ → d ⇓
  bind̅₁ (now s) _ = now s
  bind̅₁ (later s) (later x) =
    later (bind̅₁ (force s) x)

  bind̅₂ : (d : Delay A ∞) {f : A → Delay B ∞} →
           (bind⇓ : bind d f ⇓) →
           f (extract (bind̅₁ d bind⇓)) ⇓
  bind̅₂ (now s) foo = foo
  bind̅₂ (later s) {f} (later foo) =
    bind̅₂ (force s) foo

  -- The extracted value of a bind is equivalent to the extracted value
  -- of its second element
  extract-bind-⇓ : {d : Delay A Size.∞} → {f : A → Delay B Size.∞} →
                   (d⇓ : d ⇓) → (f⇓ : f (extract d⇓) ⇓) →
                   extract (bind-⇓ d⇓ {f} f⇓) ≡ extract f⇓
  extract-bind-⇓ (now a) f⇓ = ≡.refl
  extract-bind-⇓ (later t) f⇓ = extract-bind-⇓ t f⇓

  -- If the right element of a bind returns a certain value so does the
  -- entire bind
  extract-bind̅₂-bind⇓ :
    (d : Delay A ∞) {f : A → Delay B ∞} →
    (bind⇓ : bind d f ⇓) →
    extract (bind̅₂ d bind⇓) ≡ extract bind⇓
  extract-bind̅₂-bind⇓ (now s) bind⇓ = ≡.refl
  extract-bind̅₂-bind⇓ (later s) (later bind⇓) =
    extract-bind̅₂-bind⇓ (force s) bind⇓

  -- Proof that the length of a bind-⇓ is equal to the sum of the length
  -- of its components.
  bind⇓-length :
      {d : Delay A ∞} {f : A → Delay B ∞} →
      (bind⇓ : bind d f ⇓) →
      (d⇓ : d ⇓) → (f⇓ : f (extract d⇓) ⇓) →
      toℕ (length-⇓ bind⇓) ≡ toℕ (length-⇓ d⇓) ℕ.+ toℕ (length-⇓ f⇓)
  bind⇓-length {f = f} bind⇓ d⇓@(now s') f⇓ =
    ≡.cong (toℕ ∘′ length-⇓) (⇓-unique bind⇓ f⇓)
  bind⇓-length {d = d@(later dt)} {f = f} bind⇓@(later bind'⇓) d⇓@(later r) f⇓ =
    ≡.cong ℕ.suc (bind⇓-length bind'⇓ r f⇓)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-identity = map-id
{-# WARNING_ON_USAGE map-identity
"Warning: map-identity was deprecated in v2.0.
Please use map-id instead."
#-}

map-map-fusion = map-∘
{-# WARNING_ON_USAGE map-map-fusion
"Warning: map-map-fusion was deprecated in v2.0.
Please use map-∘ instead."
#-}

map-unfold-fusion = map-unfold
{-# WARNING_ON_USAGE map-unfold-fusion
"Warning: map-unfold-fusion was deprecated in v2.0.
Please use map-unfold instead."
#-}
