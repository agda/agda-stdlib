------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous infix relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Infix.Heterogeneous.Properties where

open import Level
open import Relation.Binary using (REL; _⇒_)
open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Binary using (Decidable)

open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Data.List.Relation.Binary.Prefix.Heterogeneous
  as Prefix using (Prefix; []; _∷_)
import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties as Prefixₚ
open import Data.List.Relation.Binary.Suffix.Heterogeneous
  as Suffix using (Suffix; here; there)

private
  variable
    a b r s : Level
    A : Set a
    B : Set b
    R : REL A B r
    S : REL A B s

------------------------------------------------------------------------
-- Conversion functions

fromPointwise : ∀ {as bs} → Pointwise R as bs → Infix R as bs
fromPointwise pw = here (Prefixₚ.fromPointwise pw)

fromSuffix : ∀ {as bs} → Suffix R as bs → Infix R as bs
fromSuffix (here pw) = fromPointwise pw
fromSuffix (there p) = there (fromSuffix p)

∷⁻ : ∀ {as b bs} → Infix R as (b ∷ bs) → Prefix R as (b ∷ bs) ⊎ Infix R as bs
∷⁻ (here pref) = inj₁ pref
∷⁻ (there inf) = inj₂ inf

------------------------------------------------------------------------
-- length

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  length-mono : ∀ {as bs} → Infix R as bs → length as ≤ length bs
  length-mono (here pref) = Prefixₚ.length-mono pref
  length-mono (there p)   = ℕₚ.≤-step (length-mono p)

------------------------------------------------------------------------
-- decidability

  infix? : Decidable R → Decidable (Infix R)
  infix? R? [] [] = yes (here [])
  infix? R? (a ∷ as) [] = no (λ where (here ()))
  infix? R? as bbs@(_ ∷ bs) =
    map′ [ here , there ]′ ∷⁻
    (Prefixₚ.prefix? R? as bbs ⊎-dec infix? R? as bs)
