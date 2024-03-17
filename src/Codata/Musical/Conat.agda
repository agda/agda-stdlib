------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive "natural" numbers
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Codata.Musical.Conat where

open import Codata.Musical.Notation
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∋_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

------------------------------------------------------------------------
-- Re-exporting the type and basic operations

open import Codata.Musical.Conat.Base public

------------------------------------------------------------------------
-- Some properties

module Coℕ-injective where

 suc-injective : ∀ {m n} → (Coℕ ∋ suc m) ≡ suc n → m ≡ n
 suc-injective ≡.refl = ≡.refl

fromℕ-injective : ∀ {m n} → fromℕ m ≡ fromℕ n → m ≡ n
fromℕ-injective {zero}  {zero}  eq = ≡.refl
fromℕ-injective {suc m} {suc n} eq = ≡.cong suc (fromℕ-injective (≡.cong pred eq))

------------------------------------------------------------------------
-- Equality

infix 4 _≈_

data _≈_ : Coℕ → Coℕ → Set where
  zero :                                 zero  ≈ zero
  suc  : ∀ {m n} (m≈n : ∞ (♭ m ≈ ♭ n)) → suc m ≈ suc n

module ≈-injective where

 suc-injective : ∀ {m n p q} → (suc m ≈ suc n ∋ suc p) ≡ suc q → p ≡ q
 suc-injective ≡.refl = ≡.refl

setoid : Setoid _ _
setoid = record
  { Carrier       = Coℕ
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {zero}  = zero
  refl {suc n} = suc (♯ refl)

  sym : Symmetric _≈_
  sym zero      = zero
  sym (suc m≈n) = suc (♯ sym (♭ m≈n))

  trans : Transitive _≈_
  trans zero      zero      = zero
  trans (suc m≈n) (suc n≈k) = suc (♯ trans (♭ m≈n) (♭ n≈k))
