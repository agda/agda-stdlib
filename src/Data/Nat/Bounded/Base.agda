------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded natural numbers, and their equivalence to `Fin`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded.Base where

open import Data.Nat.Base as ℕ
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Fin.Base as Fin using (Fin)
import Data.Fin.Properties as Fin
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core using (recompute)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    m n o : ℕ

------------------------------------------------------------------------
-- Definition

record ℕ< (n : ℕ) : Set where
  constructor ⟦_⟧<_
  field
    ⟦_⟧ : ℕ
    .bounded : ⟦_⟧ < n

open ℕ< public using (⟦_⟧)

-- Constructors: 'n-1 mod n', '0 mod n', '1 mod n'

⟦-1⟧< ⟦0⟧< ⟦1⟧< : .{{ NonZero n }} → ℕ< n
⟦-1⟧< {n = suc m} = ⟦ m ⟧< ℕ.n<1+n m
⟦0⟧<              = ⟦ 0 ⟧< >-nonZero⁻¹ _
⟦1⟧<  {n = 1}     = ⟦0⟧<
⟦1⟧<  {n = 2+ _}  = ⟦ 1 ⟧< nonTrivial⇒n>1 _

-- Projection from ℕ

fromℕ : .{{ NonZero n }} → ℕ → ℕ< n
fromℕ {n} m = ⟦ m % n ⟧< ℕ.m%n<n m n

-- Destructors

¬ℕ<[0] : ¬ ℕ< 0
¬ℕ<[0] ()

nonZeroIndex : ℕ< n → NonZero n
nonZeroIndex {n = suc _} _ = _

isBounded : (i : ℕ< n) → ⟦ i ⟧ < n
isBounded (⟦ _ ⟧< i<n) = recompute (_ ℕ.<? _) i<n

-- Mapping to ℕ

toℕ : ℕ< n → ℕ
toℕ = ⟦_⟧

------------------------------------------------------------------------
-- Conversion to and from `Fin n`

toFin : ℕ< n → Fin n
toFin (⟦ _ ⟧< i<n) = Fin.fromℕ< i<n

fromFin : Fin n → ℕ< n
fromFin i = ⟦ Fin.toℕ i ⟧< Fin.toℕ<n i

------------------------------------------------------------------------
-- Inverting `fromℕ`: a graph view

data _/∼≡_ : ℕ → ℕ< n → Set where
  ‵fromℕ : ∀ m (i : ℕ< n) → (⟦ i ⟧ + m * n) /∼≡ i

------------------------------------------------------------------------
-- Quotient equivalence relation on ℕ induced by `fromℕ`

record _∼_ {n} (lhs rhs : ℕ) : Set where
  constructor _,_
  field
    {k}    : ℕ< n
    lhs/∼≡ : lhs /∼≡ k
    rhs/∼≡ : rhs /∼≡ k

≡-Mod : ℕ → Rel ℕ _
≡-Mod n = _∼_ {n}

syntax ≡-Mod n m o = m ≡ o modℕ n

nonZeroModulus : (m ≡ o modℕ n) → NonZero n
nonZeroModulus eq = nonZeroIndex k where open _∼_ eq
