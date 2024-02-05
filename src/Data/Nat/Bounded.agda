------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded natural numbers, and their equivalence to `Fin`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded where

open import Data.Bool.Base using (T)
open import Data.Nat.Base as ℕ
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ)
import Data.Fin.Properties as Fin
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_; _$_; _on_)
open import Function.Bundles using (_⤖_; mk⤖; _↔_; mk↔ₛ′)
open import Function.Consequences.Propositional
  using (inverseᵇ⇒bijective; strictlyInverseˡ⇒inverseˡ; strictlyInverseʳ⇒inverseʳ)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; _≗_)
open import Relation.Nullary.Decidable.Core using (recompute; map′)
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

------------------------------------------------------------------------
-- Equality on values is propositional equality

bounded≡⇒⟦⟧≡⟦⟧ : _≡_ {A = ℕ< n} ⇒ (_≡_ on ⟦_⟧)
bounded≡⇒⟦⟧≡⟦⟧ = cong ⟦_⟧

⟦⟧≡⟦⟧⇒bounded≡ :  (_≡_ on ⟦_⟧) ⇒ _≡_ {A = ℕ< n}
⟦⟧≡⟦⟧⇒bounded≡ refl = refl

infix 4 _≟_
_≟_ : DecidableEquality (ℕ< n)
i ≟ j = map′ ⟦⟧≡⟦⟧⇒bounded≡ bounded≡⇒⟦⟧≡⟦⟧ (⟦ i ⟧ ℕ.≟ ⟦ j ⟧)

------------------------------------------------------------------------
-- Conversion to and from `Fin n`

toFin : ℕ< n → Fin n
toFin (⟦ _ ⟧< i<n) = Fin.fromℕ< i<n

fromFin : Fin n → ℕ< n
fromFin i = ⟦ toℕ i ⟧< Fin.toℕ<n i

toFin∘fromFin≐id : toFin ∘ fromFin ≗ id {A = Fin n}
toFin∘fromFin≐id i = Fin.fromℕ<-toℕ i (Fin.toℕ<n i)

fromFin∘toFin≐id : fromFin ∘ toFin ≗ id {A = ℕ< n}
fromFin∘toFin≐id (⟦ _ ⟧< i<n) = ⟦⟧≡⟦⟧⇒bounded≡ (Fin.toℕ-fromℕ< i<n)

boundedNat⤖Fin : ℕ< n ⤖ Fin n
boundedNat⤖Fin = mk⤖ $ inverseᵇ⇒bijective $
  strictlyInverseˡ⇒inverseˡ {f⁻¹ = fromFin} toFin toFin∘fromFin≐id
  ,
  strictlyInverseʳ⇒inverseʳ {f⁻¹ = fromFin} toFin fromFin∘toFin≐id

boundedNat↔Fin : ℕ< n ↔ Fin n
boundedNat↔Fin = mk↔ₛ′ toFin fromFin toFin∘fromFin≐id fromFin∘toFin≐id

------------------------------------------------------------------------
-- Inverting `fromℕ`: a graph view

data _/∼≡_ : ℕ → ℕ< n → Set where
  ‵fromℕ : ∀ m (i : ℕ< n) → (⟦ i ⟧ + m * n) /∼≡ i

module _ {n} .{{_ : NonZero n}} {m} {i : ℕ< n} where

  _/∼≡fromℕ : fromℕ {n} m ≡ i → m /∼≡ i
  _/∼≡fromℕ refl = let i = fromℕ {n} m in
    subst (_/∼≡ i) (sym (ℕ.m≡m%n+[m/n]*n m n)) (‵fromℕ (m / n) i)

module _ {n} {m} {i : ℕ< n} where

  private instance _ = nonZeroIndex i

  _/∼≡fromℕ⁻¹ : m /∼≡ i → fromℕ m ≡ i
  (‵fromℕ {n = n} m i) /∼≡fromℕ⁻¹ = ⟦⟧≡⟦⟧⇒bounded≡ $
    trans (ℕ.[m+kn]%n≡m%n ⟦ i ⟧ m n) (ℕ.m<n⇒m%n≡m (isBounded i))

/∼≡-injective : ∀ {m} {i j : ℕ< n} → m /∼≡ i → m /∼≡ j → i ≡ j
/∼≡-injective m/∼≡i m/∼≡j = trans (sym (m/∼≡i /∼≡fromℕ⁻¹)) (m/∼≡j /∼≡fromℕ⁻¹)

------------------------------------------------------------------------
-- Quotient equivalence relation on ℕ induced by `fromℕ`

record _∼_ {n} (lhs rhs : ℕ) : Set where
  constructor _,_
  field
    {i}    : ℕ< n
    lhs/∼≡ : lhs /∼≡ i
    rhs/∼≡ : rhs /∼≡ i

≡-Mod : ℕ → Rel ℕ _
≡-Mod n i j = _∼_ {n} i j

syntax ≡-Mod n i j = i ≡ j mod n

≡-mod-refl : .{{NonZero n}} → Reflexive (≡-Mod n)
≡-mod-refl {n} {m} = let r = refl /∼≡fromℕ in r , r

≡-mod-sym : Symmetric (≡-Mod n)
≡-mod-sym (lhs , rhs) = rhs , lhs

≡-mod-trans : Transitive (≡-Mod n)
≡-mod-trans (lhs₁ , rhs₁) (lhs₂ , rhs₂)
  with refl ← /∼≡-injective rhs₁ lhs₂ = lhs₁ , rhs₂

≡-mod⇒fromℕ≡fromℕ : ∀ {x y} (p : x ≡ y mod n) →
                    let _,_ {i} _ _ = p ; instance _ = nonZeroIndex i
                    in fromℕ {n} x ≡ fromℕ y
≡-mod⇒fromℕ≡fromℕ (lhs/∼≡ , rhs/∼≡) = trans (lhs/∼≡ /∼≡fromℕ⁻¹) (sym (rhs/∼≡ /∼≡fromℕ⁻¹))

fromℕ≡fromℕ⇒≡-mod : .{{_ : NonZero n}} → (_≡_ on fromℕ {n}) ⇒ ≡-Mod n
fromℕ≡fromℕ⇒≡-mod fromℕ[x]≡fromℕ[y] = (fromℕ[x]≡fromℕ[y] /∼≡fromℕ) , (refl /∼≡fromℕ)

------------------------------------------------------------------------
-- Literals

module Literals n where

  Constraint : ℕ → Set
  Constraint m = T (m <ᵇ n)

  fromNat : ∀ m → {{Constraint m}} → ℕ< n
  fromNat m {{lt}} = ⟦ m ⟧< ℕ.<ᵇ⇒< m n lt

