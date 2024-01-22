------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded natural numbers, and their equivalence to `Fin`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded where

open import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ)
import Data.Fin.Properties as Fin
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_; _$_; _on_)
open import Function.Bundles using (_⤖_; mk⤖)
open import Function.Consequences.Propositional
  using (inverseᵇ⇒bijective; strictlyInverseˡ⇒inverseˡ; strictlyInverseʳ⇒inverseʳ)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≗_)
open import Relation.Nullary.Decidable.Core using (recompute)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Definition

record ℕ< (n : ℕ) : Set where
  constructor ⟦_⟧<_
  field
    value : ℕ
    .bounded : value < n

open ℕ< public using () renaming (value to ⟦_⟧)

-- Constructor

⟦0⟧< : ∀ n → .{{ NonZero n }} → ℕ< n
⟦0⟧< (n@(suc _)) = ⟦ zero ⟧< z<s

-- Destructors

¬ℕ<[0] : ¬ ℕ< 0
¬ℕ<[0] ()

nonZeroIndex : ℕ< n → NonZero n
nonZeroIndex {n = suc _} _ = _

isBounded : (i : ℕ< n) → ⟦ i ⟧ < n
isBounded (⟦ _ ⟧< i<n) = recompute (_ ℕ.<? _) i<n

-- Equality on values is propositional equality

bounded≡⇒⟦⟧≡⟦⟧ : _≡_ {A = ℕ< n} ⇒ (_≡_ on ⟦_⟧)
bounded≡⇒⟦⟧≡⟦⟧ = cong ⟦_⟧

⟦⟧≡⟦⟧⇒bounded≡ :  (_≡_ on ⟦_⟧) ⇒ _≡_ {A = ℕ< n}
⟦⟧≡⟦⟧⇒bounded≡ refl = refl

------------------------------------------------------------------------
-- Conversion to and from `Fin n`

toFin : ℕ< n → Fin n
toFin (⟦ _ ⟧< i<n) = Fin.fromℕ< i<n

fromFin : Fin n → ℕ< n
fromFin i = ⟦ toℕ i ⟧< (Fin.toℕ<n i)

toFin∘fromFin≐id : toFin ∘ fromFin ≗ id {A = Fin n}
toFin∘fromFin≐id i = Fin.fromℕ<-toℕ i (Fin.toℕ<n i)

fromFin∘toFin≐id : fromFin ∘ toFin ≗ id {A = ℕ< n}
fromFin∘toFin≐id (⟦ _ ⟧< i<n) = ⟦⟧≡⟦⟧⇒bounded≡ (Fin.toℕ-fromℕ< i<n)

boundedNat⤖Fin : ℕ< n ⤖ Fin n
boundedNat⤖Fin = mk⤖ $ inverseᵇ⇒bijective $
  strictlyInverseˡ⇒inverseˡ {f⁻¹ = fromFin} toFin toFin∘fromFin≐id
  ,
  strictlyInverseʳ⇒inverseʳ {f⁻¹ = fromFin} toFin fromFin∘toFin≐id

