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
open import Function.Base using (id; _∘_; _on_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (recompute)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Definition

record BoundedNat (n : ℕ) : Set where
  constructor ⟦_⟧<
  field
    value : ℕ
    .{{bounded}} : value < n

open BoundedNat public using () renaming (value to ⟦_⟧)

-- Constructor

⟦0⟧< : ∀ n → .{{ NonZero n }} → BoundedNat n
⟦0⟧< (n@(suc _)) = ⟦ zero ⟧< where instance _ = z<s

-- Destructors

¬BoundedNat[0] : ¬ BoundedNat 0
¬BoundedNat[0] ()

isBounded : (i : BoundedNat n) → ⟦ i ⟧ < n
isBounded (⟦ _ ⟧< {{bounded}}) = recompute (_ ℕ.<? _) bounded

-- Equality on values is propositional equality

bounded≡⇒⟦⟧≡⟦⟧ : _≡_ {A = BoundedNat n} ⇒ (_≡_ on ⟦_⟧)
bounded≡⇒⟦⟧≡⟦⟧ = ≡.cong ⟦_⟧

⟦⟧≡⟦⟧⇒bounded≡ :  (_≡_ on ⟦_⟧) ⇒ _≡_ {A = BoundedNat n}
⟦⟧≡⟦⟧⇒bounded≡ refl = refl

------------------------------------------------------------------------
-- Conversion to and from `Fin n`

toFin : BoundedNat n → Fin n
toFin ⟦ i ⟧< = fromℕ< i
  where -- a better version of `Data.Fin.Base.fromℕ<`?
  fromℕ< : ∀ m → .{{ m < n }} → Fin n
  fromℕ< {n = suc _} zero            = zero
  fromℕ< {n = suc _} (suc m) {{m<n}} = suc (fromℕ< m {{s<s⁻¹ m<n}})

fromFin : Fin n → BoundedNat n
fromFin i = ⟦ toℕ i ⟧< where instance _ = Fin.toℕ<n i

