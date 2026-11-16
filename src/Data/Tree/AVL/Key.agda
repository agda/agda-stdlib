------------------------------------------------------------------------
-- The Agda standard library
--
-- Keys for AVL trees -- the original key type extended with a new
-- minimum and maximum.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles
  using (StrictTotalOrder; StrictPartialOrder)

module Data.Tree.AVL.Key
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Construct.Add.Extrema
  as AddExtremaToSet using (_±)
import Relation.Binary.Construct.Add.Extrema.Equality
  as AddExtremaToEquality
import Relation.Binary.Construct.Add.Extrema.Strict
  as AddExtremaToOrder

open StrictTotalOrder sto renaming (Carrier to Key)
  using (_≈_; _<_; trans; irrefl; module Eq)

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- The equality is extended in a corresponding manner

open AddExtremaToEquality _≈_ public
  using ()
  renaming
  ( _≈±_ to _≈⁺_
  ; [_]  to [_]ᴱ
  )

------------------------------------------------------------------------
-- The order is extended in a corresponding manner

open AddExtremaToOrder _<_ public
  using () renaming
  (_<±_    to _<⁺_
  ; [_]    to [_]ᴿ
  ; ⊥±<⊤±  to ⊥⁺<⊤⁺
  ; [_]<⊤± to [_]<⊤⁺
  ; ⊥±<[_] to ⊥⁺<[_]
  )

-- A pair of ordering constraints.

infix 4 _<_<_

_<_<_ : Key⁺ → Key → Key⁺ → Set (a ⊔ ℓ₂)
l < x < u = l <⁺ [ x ] × [ x ] <⁺ u

-- Properties

⊥⁺<[_]<⊤⁺ : ∀ k → ⊥⁺ < k < ⊤⁺
⊥⁺<[ k ]<⊤⁺ = ⊥⁺<[ k ] , [ k ]<⊤⁺

refl⁺ : Reflexive _≈⁺_
refl⁺ = AddExtremaToEquality.≈±-refl _≈_ Eq.refl

sym⁺ : ∀ {l u} → l ≈⁺ u → u ≈⁺ l
sym⁺ = AddExtremaToEquality.≈±-sym _≈_ Eq.sym

trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u
trans⁺ l = AddExtremaToOrder.<±-trans _<_ trans

irrefl⁺ : ∀ k → ¬ (k <⁺ k)
irrefl⁺ k = AddExtremaToOrder.<±-irrefl _<_ irrefl refl⁺

-- Bundle

strictPartialOrder : StrictPartialOrder _ _ _
strictPartialOrder = record
  { isStrictPartialOrder = AddExtremaToOrder.<±-isStrictPartialOrder STO._<_ STO.isStrictPartialOrder
  } where module STO = StrictTotalOrder sto

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { isStrictTotalOrder = AddExtremaToOrder.<±-isStrictTotalOrder STO._<_ STO.isStrictTotalOrder
  } where module STO = StrictTotalOrder sto
