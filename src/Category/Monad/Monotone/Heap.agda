import Relation.Unary.Closure.Preorder as Closure
open import Relation.Binary using (Preorder)

module Category.Monad.Monotone.Heap
  -- ordered heap types
  {ℓ}(pre : Preorder ℓ ℓ ℓ)
  -- types
  (T : Set ℓ)
  -- weakenable values
  (V : T → Preorder.Carrier pre → Set ℓ) ⦃ wkV : ∀ {a} → Closure.Closed pre (V a) ⦄
  -- heaps indexed by the heap type
  (H : Preorder.Carrier pre → Set ℓ)
  -- weakenable heap type membership
  (_∈_ : T → Preorder.Carrier pre → Set ℓ) ⦃ wk∈ : ∀ {a} → Closure.Closed pre (_∈_ a) ⦄ where

open Preorder pre renaming (Carrier to I)

open import Level
open import Data.Unit using (⊤; tt)
open import Data.Product

open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Closure.Preorder pre

open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.State pre H

open Closed ⦃...⦄

record HeapMonad (M : Pt I ℓ) : Set (suc ℓ) where
  field
    super : StateMonad M

  open StateMonad super public

  field
    store  : ∀ {a} → V a ⊆ M (λ W → a ∈ W)
    modify : ∀ {a} → _∈_ a ⊆ V a ⇒ M (V a)
    deref  : ∀ {a} → _∈_ a ⊆ M (V a)

  module HeapMonadOps (m : RawMPMonad M) where
    open RawMPMonad m
    open import Data.List.All as All

    storeₙ  : ∀ {W as} → All (λ a → V a W) as → M (λ W' → All (λ a → a ∈ W') as) W
    storeₙ vs = sequence (All.map (λ v {x} ext → store (next v ext)) vs)
