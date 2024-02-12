------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of bounded natural numbers ℕ<
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded.Properties where

import Algebra.Definitions as Definitions
open import Data.Fin.Base as Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.Nat.Base as ℕ
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_; _$_; _on_)
open import Function.Bundles using (_⤖_; mk⤖; _↔_; mk↔ₛ′)
open import Function.Consequences.Propositional
  using (inverseᵇ⇒bijective; strictlyInverseˡ⇒inverseˡ; strictlyInverseʳ⇒inverseʳ)
open import Relation.Binary.Bundles using (PartialSetoid; Setoid)
open import Relation.Binary.Structures using (IsPartialEquivalence; IsEquivalence)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
  hiding (isEquivalence; setoid)
open import Relation.Nullary.Decidable.Core using (map′)

open import Data.Nat.Bounded.Base as ℕ<

private
  variable
    m n o : ℕ
    i j k : ℕ< n


------------------------------------------------------------------------
-- Equality on values is propositional equality

⟦0⟧≡0 : .{{_ : NonZero n}} → ⟦ ⟦0⟧< {n = n} ⟧ ≡ 0
⟦0⟧≡0 {n = suc _} = refl

⟦1⟧≡1 : .{{_ : NonTrivial n}} →
        let instance _ = nonTrivial⇒nonZero n in ⟦ ⟦1⟧< {n = n} ⟧ ≡ 1
⟦1⟧≡1 {n = 2+ _} = refl

≡⇒⟦⟧≡⟦⟧ : _≡_ {A = ℕ< n} ⇒ (_≡_ on ⟦_⟧)
≡⇒⟦⟧≡⟦⟧ = cong ⟦_⟧

⟦⟧≡⟦⟧⇒≡ :  (_≡_ on ⟦_⟧) ⇒ _≡_ {A = ℕ< n}
⟦⟧≡⟦⟧⇒≡ refl = refl

fromℕ[n]≡0 : .{{_ : NonZero n}} → fromℕ n ≡ ⟦0⟧<
fromℕ[n]≡0 {n} = ⟦⟧≡⟦⟧⇒≡ (ℕ.n%n≡0 n)

module _ (m<n : m < n) where

  private instance _ = ℕ.>-nonZero (ℕ.m<n⇒0<n m<n)

  +-inverseˡ : fromℕ (n ∸ m + m) ≡ ⟦0⟧<
  +-inverseˡ = trans (cong fromℕ (ℕ.m∸n+n≡m (ℕ.<⇒≤ m<n))) fromℕ[n]≡0

  +-inverseʳ : fromℕ (m + (n ∸ m)) ≡ ⟦0⟧<
  +-inverseʳ = trans (cong fromℕ (ℕ.m+[n∸m]≡n (ℕ.<⇒≤ m<n))) fromℕ[n]≡0

  fromℕ≐⟦⟧< : fromℕ m ≡ ⟦ m ⟧< m<n
  fromℕ≐⟦⟧< = ⟦⟧≡⟦⟧⇒≡ $ ℕ.m<n⇒m%n≡m m<n

fromℕ∘toℕ≐id : (i : ℕ< n) → let instance _ = nonZeroIndex i
               in fromℕ ⟦ i ⟧ ≡ i
fromℕ∘toℕ≐id i = fromℕ≐⟦⟧< (ℕ<.isBounded i)

infix 4 _≟_
_≟_ : DecidableEquality (ℕ< n)
i ≟ j = map′ ⟦⟧≡⟦⟧⇒≡ ≡⇒⟦⟧≡⟦⟧ (⟦ i ⟧ ℕ.≟ ⟦ j ⟧)

------------------------------------------------------------------------
-- Conversion to and from `Fin n`

toFin∘fromFin≐id : toFin ∘ fromFin ≗ id {A = Fin n}
toFin∘fromFin≐id i = Fin.fromℕ<-toℕ i (Fin.toℕ<n i)

fromFin∘toFin≐id : fromFin ∘ toFin ≗ id {A = ℕ< n}
fromFin∘toFin≐id (⟦ _ ⟧< i<n) = ⟦⟧≡⟦⟧⇒≡ (Fin.toℕ-fromℕ< i<n)

boundedNat⤖Fin : ℕ< n ⤖ Fin n
boundedNat⤖Fin = mk⤖ $ inverseᵇ⇒bijective $
  strictlyInverseˡ⇒inverseˡ {f⁻¹ = fromFin} toFin toFin∘fromFin≐id
  ,
  strictlyInverseʳ⇒inverseʳ {f⁻¹ = fromFin} toFin fromFin∘toFin≐id

boundedNat↔Fin : ℕ< n ↔ Fin n
boundedNat↔Fin = mk↔ₛ′ toFin fromFin toFin∘fromFin≐id fromFin∘toFin≐id

------------------------------------------------------------------------
-- Inversion properties of the graph view of `fromℕ`

module _ {m} {i : ℕ< n} where

  private instance _ = nonZeroIndex i

  _/∼≡fromℕ : fromℕ m ≡ i → m /∼≡ i
  _/∼≡fromℕ = _/∼≡fromℕ′
    where
    _/∼≡fromℕ′ : .{{_ : NonZero n}} → fromℕ m ≡ i → m /∼≡ i
    _/∼≡fromℕ′ refl = subst (_/∼≡ i) (sym (ℕ.m≡m%n+[m/n]*n m n)) (‵fromℕ (m / n) i)


  _/∼≡fromℕ⁻¹ : m /∼≡ i → fromℕ m ≡ i
  (‵fromℕ {n = n} m i) /∼≡fromℕ⁻¹ = ⟦⟧≡⟦⟧⇒≡ $
    trans (ℕ.[m+kn]%n≡m%n ⟦ i ⟧ m n) (ℕ.m<n⇒m%n≡m (isBounded i))

/∼≡-injective : m /∼≡ i → m /∼≡ j → i ≡ j
/∼≡-injective m/∼≡i m/∼≡j = trans (sym (m/∼≡i /∼≡fromℕ⁻¹)) (m/∼≡j /∼≡fromℕ⁻¹)

------------------------------------------------------------------------
-- Properties of the quotient on ℕ induced by `fromℕ`

n≡0-mod : .{{_ : NonZero n}} → n ≡ 0 modℕ n
n≡0-mod = let r = fromℕ[n]≡0 /∼≡fromℕ in r , ‵fromℕ 0 ⟦0⟧<

≡-mod-refl : .{{NonZero n}} → Reflexive (≡-Modℕ n)
≡-mod-refl {n} {m} = let r = erefl (fromℕ m) /∼≡fromℕ in r , r

≡-mod-sym : Symmetric (≡-Modℕ n)
≡-mod-sym (lhs , rhs) = rhs , lhs

≡-mod-trans : Transitive (≡-Modℕ n)
≡-mod-trans (lhs₁ , rhs₁) (lhs₂ , rhs₂)
  with refl ← /∼≡-injective rhs₁ lhs₂ = lhs₁ , rhs₂

isPartialEquivalence : IsPartialEquivalence (≡-Modℕ n)
isPartialEquivalence = record { sym = ≡-mod-sym ; trans = ≡-mod-trans }

partialSetoid : ℕ → PartialSetoid _ _
partialSetoid n = record { _≈_ = ≡-Modℕ n ; isPartialEquivalence = isPartialEquivalence }

isEquivalence : .{{NonZero n}} → IsEquivalence (≡-Modℕ n)
isEquivalence {n} = record
  { refl = ≡-mod-refl
  ; sym = ≡-mod-sym
  ; trans = ≡-mod-trans
  }

setoid : .{{NonZero n}} → Setoid _ _
setoid = record { isEquivalence = isEquivalence }

≡-mod⇒fromℕ≡fromℕ : (eq : m ≡ o modℕ n) →
                    let instance _ = nonZeroModulus eq
                    in fromℕ m ≡ fromℕ o
≡-mod⇒fromℕ≡fromℕ (lhs/∼≡ , rhs/∼≡) = trans (lhs/∼≡ /∼≡fromℕ⁻¹) (sym (rhs/∼≡ /∼≡fromℕ⁻¹))

≡-mod⇒%≡% : (eq : m ≡ o modℕ n) →
            let instance _ = nonZeroModulus eq
            in m % n ≡ o % n
≡-mod⇒%≡% = ≡⇒⟦⟧≡⟦⟧ ∘ ≡-mod⇒fromℕ≡fromℕ

fromℕ≡fromℕ⇒≡-mod : .{{_ : NonZero n}} → (_≡_ on fromℕ) ⇒ ≡-Modℕ n
fromℕ≡fromℕ⇒≡-mod eq = eq /∼≡fromℕ , refl /∼≡fromℕ

%≡%⇒≡-mod : .{{_ : NonZero n}} → (_≡_ on _% n) ⇒ ≡-Modℕ n
%≡%⇒≡-mod eq = fromℕ≡fromℕ⇒≡-mod (⟦⟧≡⟦⟧⇒≡ eq)

toℕ∘fromℕ≐id : .{{_ : NonZero n}} → (m : ℕ) → ⟦ fromℕ m ⟧ ≡ m modℕ n
toℕ∘fromℕ≐id m = fromℕ≡fromℕ⇒≡-mod (fromℕ∘toℕ≐id (fromℕ m))

------------------------------------------------------------------------
-- Arithmetic properties of bounded numbers

module _ (m<n : m < n) (o<n : o < n) where

  private
    instance
      n≢ₘ0 = ℕ.>-nonZero (ℕ.m<n⇒0<n m<n)
      n≢ₒ0 = ℕ.>-nonZero (ℕ.m<n⇒0<n o<n)

  open ≡-Reasoning

  ≡-mod⇒≡ : m ≡ o modℕ n → m ≡ o
  ≡-mod⇒≡ eq = ≡⇒⟦⟧≡⟦⟧ $ begin
    ⟦ m ⟧< m<n       ≡⟨ fromℕ≐⟦⟧< m<n ⟨
    fromℕ {{n≢ₘ0}} m ≡⟨ ≡-mod⇒fromℕ≡fromℕ eq ⟩
    fromℕ {{n≢ₒ0}} o ≡⟨ fromℕ≐⟦⟧< o<n ⟩
    ⟦ o ⟧< o<n       ∎

module _ .{{_ : NonZero n}} (m o : ℕ) where

  open ≡-Reasoning

  +-distribˡ-% : ((m % n) + o) ≡ (m + o) modℕ n
  +-distribˡ-% = %≡%⇒≡-mod $ begin
    (m % n + o) % n         ≡⟨ ℕ.%-distribˡ-+ (m % n) o n ⟩
    (m % n % n + o % n) % n ≡⟨ cong ((_% n) ∘ (_+ o % n)) (ℕ.m%n%n≡m%n m n) ⟩
    (m % n + o % n) % n     ≡⟨ ℕ.%-distribˡ-+ m o n ⟨
    (m + o) % n             ∎

  +-distribʳ-% : (m + (o % n)) ≡ (m + o) modℕ n
  +-distribʳ-% = %≡%⇒≡-mod $ begin
    (m + o % n) % n         ≡⟨ ℕ.%-distribˡ-+ m (o % n) n ⟩
    (m % n + o % n % n) % n ≡⟨ cong ((_% n) ∘ (m % n +_)) (ℕ.m%n%n≡m%n o n) ⟩
    (m % n + o % n) % n     ≡⟨ ℕ.%-distribˡ-+ m o n ⟨
    (m + o) % n             ∎

  *-distribˡ-% : ((m % n) * o) ≡ (m * o) modℕ n
  *-distribˡ-% = %≡%⇒≡-mod $ begin
    (m % n * o) % n           ≡⟨ ℕ.%-distribˡ-* (m % n) o n ⟩
    (m % n % n * (o % n)) % n ≡⟨ cong ((_% n) ∘ (_* (o % n))) (ℕ.m%n%n≡m%n m n) ⟩
    (m % n * (o % n)) % n     ≡⟨ ℕ.%-distribˡ-* m o n ⟨
    (m * o) % n               ∎

  *-distribʳ-% : (m * (o % n)) ≡ (m * o) modℕ n
  *-distribʳ-% = %≡%⇒≡-mod $ begin
    (m * (o % n)) % n         ≡⟨ ℕ.%-distribˡ-* m (o % n) n ⟩
    (m % n * (o % n % n)) % n ≡⟨ cong ((_% n) ∘ (m % n *_)) (ℕ.m%n%n≡m%n o n) ⟩
    (m % n * (o % n)) % n     ≡⟨ ℕ.%-distribˡ-* m o n ⟨
    (m * o) % n               ∎
