------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Delay type
------------------------------------------------------------------------

module Codata.Delay.Properties where

open import Size
open import Codata.Thunk
open import Codata.Conat
open import Codata.Conat.Bisimilarity as Coℕ
open import Codata.Delay
open import Codata.Delay.Bisimilarity
open import Function
open import Relation.Binary
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
