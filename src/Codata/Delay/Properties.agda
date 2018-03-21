------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Delay type
------------------------------------------------------------------------

module Codata.Delay.Properties where

open import Size
import Data.Sum as Sum
open import Codata.Thunk
open import Codata.Conat
open import Codata.Conat.Bisimilarity as Coℕ using (zero ; suc)
open import Codata.Delay
open import Codata.Delay.Bisimilarity
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module _ {a} {A : Set a} where

 length-never : ∀ {i} → length (Delay A i ∋ never) Coℕ.≈ infinity
 length-never = suc λ where .force → length-never

module _ {a b} {A : Set a} {B : Set b} where

 length-map : ∀ (f : A → B) {i} (da : Delay A i) → length (map f da) Coℕ.≈ length da
 length-map f (now a)    = zero
 length-map f (later da) = suc λ where .force → length-map f (da .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 length-zipWith : ∀ (f : A → B → C) {i} (da : Delay A i) db →
   length (zipWith f da db) Coℕ.≈ length da ⊔ length db
 length-zipWith f (now a)      db         = length-map (f a) db
 length-zipWith f da@(later _) (now b)    = length-map (λ a → f a b) da
 length-zipWith f (later da)   (later db) =
   suc λ where .force →  length-zipWith f (da .force) (db .force)

 map-map-fusion : ∀ f (g : B → C) {i} (da : Delay A i) →
   map g (map f da) ≈ map (g ∘ f) da
 map-map-fusion f g (now a)    = now Eq.refl
 map-map-fusion f g (later da) = later λ where .force → map-map-fusion f g (da .force)

 map-unfold-fusion : ∀ (f : B → C) n (s : A) {i} →
   map f (Delay B i ∋ unfold n s) ≈ unfold (λ a → Sum.map id f (n a)) s
 map-unfold-fusion f n s with n s
 ... | Sum.inj₁ s′ = later λ where .force → map-unfold-fusion f n s′
 ... | Sum.inj₂ b  = now Eq.refl
