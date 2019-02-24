------------------------------------------------------------------------
-- The Agda standard library
--
-- Keys for AVL trees -- the original key type extended with a new
-- minimum and maximum.
-----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.AVL.Key
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Construct.Add.Extrema
  as AddExtremaToSet using (_±)
open import Relation.Binary.Construct.Add.Extrema.Strict
  as AddExtremaToOrder using ()

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

-----------------------------------------------------------------------
-- Keys are augmented with new extrema (i.e. an artificial minimum and
-- maximum)

Key⁺ : Set a
Key⁺ = Key ±

open AddExtremaToSet public
  using ([_]; [_]-injective)
  renaming
  ( ⊥± to ⊥⁺
  ; ⊤± to ⊤⁺
  )

-----------------------------------------------------------------------
-- The order is extended in a corresponding manner

open AddExtremaToOrder _<_ public
  using () renaming
  (_<±_    to _<⁺_
  ; [_]    to [_]<
  ; ⊥±<⊤±  to ⊥⁺<⊤⁺
  ; [_]<⊤± to [_]<⊤⁺
  ; ⊥±<[_] to ⊥⁺<[_]
  )

-- A pair of ordering constraints.

infix 4 _<_<_

_<_<_ : Key⁺ → Key → Key⁺ → Set ℓ₂
l < x < u = l <⁺ [ x ] × [ x ] <⁺ u

-- Properties

⊥⁺<[_]<⊤⁺ : ∀ k → ⊥⁺ < k < ⊤⁺
⊥⁺<[ k ]<⊤⁺ = ⊥⁺<[ k ] , [ k ]<⊤⁺

trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u
trans⁺ l = AddExtremaToOrder.<±-trans _<_ trans
