------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation (with K)
------------------------------------------------------------------------

{-# OPTIONS --safe --with-K #-}

module Data.List.Relation.Binary.Permutation.Propositional.Properties.WithK where

open import Function.Base using (_$_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Related.Propositional using (SK-sym; module EquationalReasoning)

open import Data.List.Base using (deduplicate; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (++-∈⇔; deduplicate-∈⇔)
open import Data.List.Membership.Propositional.Properties.WithK using (unique∧set⇒bag)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Binary.Disjoint.Propositional.Properties
  using (deduplicate⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.List.Relation.Binary.BagAndSetEquality using (∼bag⇒↭)

open import Data.Sum as Sum using (_⊎_)
open import Data.Sum.Function.Propositional using (_⊎-cong_)

open import Relation.Binary.Definitions using (DecidableEquality)

------------------------------------------------------------------------
-- deduplicate

module _ {a} {A : Set a} (_≟_ : DecidableEquality A) where

  private
    dedup≡   = deduplicate    _≟_
    ∈-dedup≡ = deduplicate-∈⇔ _≟_

  open import Data.List.Relation.Unary.Unique.DecPropositional.Properties _≟_
    using (deduplicate-!)

  dedup-++-↭ : ∀ {xs ys} → Disjoint xs ys → dedup≡ (xs ++ ys) ↭ dedup≡ xs ++ dedup≡ ys
  dedup-++-↭ {xs} {ys} disj
    = ∼bag⇒↭
    $ unique∧set⇒bag
        (deduplicate-! _)
        (++⁺ (deduplicate-! _) (deduplicate-! _) (deduplicate⁺ _≟_ disj))
    λ {x} → begin
    x ∈ dedup≡ (xs ++ ys)           ∼⟨ SK-sym ∈-dedup≡ ⟩
    x ∈ xs ++ ys                    ∼⟨ ++-∈⇔ ⟩
    (x ∈ xs ⊎ x ∈ ys)               ∼⟨ ∈-dedup≡ ⊎-cong ∈-dedup≡ ⟩
    (x ∈ dedup≡ xs ⊎ x ∈ dedup≡ ys) ∼⟨ SK-sym ++-∈⇔ ⟩
    x ∈ dedup≡ xs ++ dedup≡ ys      ∎ where open EquationalReasoning
