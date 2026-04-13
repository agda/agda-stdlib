------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Linked
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.Linked.Properties where

open import Data.Vec.Base as Vec
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All.Properties as All
open import Data.Vec.Relation.Unary.Linked as Linked
  using (Linked; []; [-]; _∷_)
open import Data.Fin.Base using (zero; suc; _<_)
open import Data.Nat.Base using (ℕ; zero; suc; s<s⁻¹)
open import Level using (Level)
open import Function.Base using (_on_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Unary using (Pred; Decidable)

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

  lookup⁺ : ∀ {i j} {xs : Vec _ n} →
           Linked R xs → i < j →
           R (lookup xs i) (lookup xs j)
  lookup⁺ {i = zero}  {j = suc j} (rx ∷ rxs) i<j = All.lookup⁺ (Linked⇒All rx rxs) j
  lookup⁺ {i = suc i} {j = suc j} (_  ∷ rxs) i<j = lookup⁺ rxs (s<s⁻¹ i<j)

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
