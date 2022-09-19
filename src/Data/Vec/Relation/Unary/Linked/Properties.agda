------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Linked
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.Linked.Properties where

open import Data.Bool.Base using (true; false)
open import Data.Vec.Base as Vec hiding (lookup)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All.Properties as Allₚ
open import Data.Vec.Relation.Unary.Linked as Linked
  using (Linked; []; [-]; _∷_)
open import Data.Fin.Base using (zero; suc; _<_)
--open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (ℕ; NonZero; zero; suc)
open import Data.Nat.Properties using (<-pred)
open import Level using (Level)
open import Function.Base using (_∘_; flip; _on_)
open import Relation.Binary using (Rel; Transitive; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no; does)

private
  variable
    a b p r ℓ : Level
    m n : ℕ
    A : Set a
    B : Set b
    R : Rel A r

------------------------------------------------------------------------
-- Relationship to other predicates
------------------------------------------------------------------------

module _ (trans : Transitive R) where

  Linked⇒All : ∀ {v} {xs : Vec _ (suc n)} → R v (head xs) →
               Linked R xs → All (R v) xs
  Linked⇒All Rvx [-]         = Rvx ∷ []
  Linked⇒All Rvx (Rxy ∷ Rxs) = Rvx ∷ Linked⇒All (trans Rvx Rxy) Rxs

  NZLinked⇒All : .{{nz : NonZero n}} →
                  ∀ {v} {xs : Vec _ n} → R v (NZhead {{nz}} xs) →
                  Linked R xs → All (R v) xs
  NZLinked⇒All {n = suc n} = Linked⇒All {n = n}

  lookup : ∀ {i j} {xs : Vec _ n} → i < j →
           Linked R xs → R (Vec.lookup xs i) (Vec.lookup xs j)
  lookup {i = zero}  {j = suc j} i<j (rx ∷ rxs) = Allₚ.lookup⁺ j (Linked⇒All rx rxs)
  lookup {i = suc i} {j = suc j} i<j (_  ∷ rxs) = lookup (<-pred i<j) rxs

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for vec operations
------------------------------------------------------------------------
-- map

map⁺ : ∀ {f : B → A} {xs} → Linked (R on f) {n} xs → Linked R (map f xs)
map⁺ []                  = []
map⁺ [-]                 = [-]
map⁺ (Rxy ∷ [-])         = Rxy ∷ [-]
map⁺ (Rxy ∷ Rxs@(_ ∷ _)) = Rxy ∷ map⁺ Rxs

map⁻ : ∀ {f : B → A} {xs} → Linked R {n} (map f xs) → Linked (R on f) xs
map⁻ {xs = []}        []           = []
map⁻ {xs = x ∷ []}    [-]          = [-]
map⁻ {xs = x ∷ _ ∷ _} (Rxy ∷ Rxs)  = Rxy ∷ map⁻ Rxs
