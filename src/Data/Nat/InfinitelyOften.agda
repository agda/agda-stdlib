------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of and lemmas related to "true infinitely often"
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.InfinitelyOften where

open import Data.Nat.Base using (ℕ; _≤_; _⊔_; _+_; suc; zero; s≤s)
open import Data.Nat.Properties
open import Data.Product.Base as Prod hiding (map)
open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
open import Effect.Monad using (RawMonad)
open import Function.Base using (_∘_; id)
open import Level using (Level; 0ℓ)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Relation.Nullary.Negation using (¬¬-Monad; call/cc)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Unary using (Pred; _∪_; _⊆_)
open import Relation.Nullary.Negation.Core using (contradiction)

open RawMonad (¬¬-Monad {a = 0ℓ})

private
  variable
    ℓ : Level

infixr 1 _∪-Fin_

-- Only true finitely often.

Fin : Pred ℕ ℓ → Set ℓ
Fin P = ∃ λ i → ∀ j → i ≤ j → ¬ P j

-- A non-constructive definition of "true infinitely often".

Inf : Pred ℕ ℓ → Set ℓ
Inf P = ¬ Fin P

-- Fin is preserved by binary sums.

_∪-Fin_ : ∀ {ℓp ℓq P Q} → Fin {ℓp} P → Fin {ℓq} Q → Fin (P ∪ Q)
_∪-Fin_ {P = P} {Q} (i , ¬p) (j , ¬q) = (i ⊔ j , helper)
  where
  open ≤-Reasoning

  helper : ∀ k → i ⊔ j ≤ k → ¬ (P ∪ Q) k
  helper k i⊔j≤k (inj₁ p) = ¬p k (begin
    i      ≤⟨ m≤m⊔n i j ⟩
    i ⊔ j  ≤⟨ i⊔j≤k ⟩
    k      ∎) p
  helper k i⊔j≤k (inj₂ q) = ¬q k (begin
    j      ≤⟨ m≤m⊔n j i ⟩
    j ⊔ i  ≡⟨ ⊔-comm j i ⟩
    i ⊔ j  ≤⟨ i⊔j≤k ⟩
    k      ∎) q

-- Inf commutes with binary sums (in the double-negation monad).

commutes-with-∪ : ∀ {P Q} → Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
commutes-with-∪ p∪q =
  call/cc λ ¬[p⊎q] →
  (λ ¬p ¬q → contradiction (¬p ∪-Fin ¬q) p∪q)
    <$> ¬[p⊎q] ∘ inj₁ ⊛ ¬[p⊎q] ∘ inj₂

-- Inf is functorial.

map : ∀ {ℓp ℓq P Q} → P ⊆ Q → Inf {ℓp} P → Inf {ℓq} Q
map P⊆Q ¬fin = ¬fin ∘ Prod.map id (λ fin j i≤j → fin j i≤j ∘ P⊆Q)

-- Inf is upwards closed.

up : ∀ {P} n → Inf {ℓ} P → Inf (P ∘ _+_ n)
up     zero    = id
up {P = P} (suc n) = up n ∘ up₁
  where
  up₁ : Inf P → Inf (P ∘ suc)
  up₁ ¬fin (i , fin) = ¬fin (suc i , helper)
    where
    helper : ∀ j → 1 + i ≤ j → ¬ P j
    helper ._ (s≤s i≤j) = fin _ i≤j

-- A witness.

witness : ∀ {P} → Inf {ℓ} P → ¬ ¬ ∃ P
witness ¬fin ¬p = ¬fin (0 , λ i _ Pi → ¬p (i , Pi))

-- Two different witnesses.

twoDifferentWitnesses
  : ∀ {P} → Inf P → ¬ ¬ ∃₂ λ m n → m ≢ n × P m × P n
twoDifferentWitnesses inf =
  witness inf                     >>= λ w₁ →
  witness (up (1 + proj₁ w₁) inf) >>= λ w₂ →
  pure (_ , _ , m≢1+m+n (proj₁ w₁) , proj₂ w₁ , proj₂ w₂)
