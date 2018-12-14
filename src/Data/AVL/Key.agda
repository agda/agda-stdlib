------------------------------------------------------------------------
-- The Agda standard library
--
-- Keys for AVL trees -- the original key type extended with a new
-- minimum and maximum.
-----------------------------------------------------------------------

open import Relation.Binary

module Data.AVL.Key
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

-----------------------------------------------------------------------
-- Definition

infix 5 [_]

data Key⁺ : Set a where
  ⊥⁺ ⊤⁺ : Key⁺
  [_]   : (k : Key) → Key⁺

[_]-injective : ∀ {k l} → [ k ] ≡ [ l ] → k ≡ l
[_]-injective refl = refl

-----------------------------------------------------------------------
-- An extended strict ordering relation.

infix 4 _<⁺_

_<⁺_ : Key⁺ → Key⁺ → Set ℓ₂
⊥⁺    <⁺ [ _ ] = Lift ℓ₂ ⊤
⊥⁺    <⁺ ⊤⁺    = Lift ℓ₂ ⊤
[ x ] <⁺ [ y ] = x < y
[ _ ] <⁺ ⊤⁺    = Lift ℓ₂ ⊤
_     <⁺ _     = Lift ℓ₂ ⊥

-- A pair of ordering constraints.

infix 4 _<_<_

_<_<_ : Key⁺ → Key → Key⁺ → Set ℓ₂
l < x < u = l <⁺ [ x ] × [ x ] <⁺ u

-- _<⁺_ is transitive.

trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u

trans⁺ [ l ] {m = [ m ]} {u = [ u ]} l<m m<u = trans l<m m<u

trans⁺ ⊥⁺    {u = [ _ ]} _ _ = _
trans⁺ ⊥⁺    {u = ⊤⁺}    _ _ = _
trans⁺ [ _ ] {u = ⊤⁺}    _ _ = _

trans⁺ _     {m = ⊥⁺}    {u = ⊥⁺}    _ (lift ())
trans⁺ _     {m = [ _ ]} {u = ⊥⁺}    _ (lift ())
trans⁺ _     {m = ⊤⁺}    {u = ⊥⁺}    _ (lift ())
trans⁺ [ _ ] {m = ⊥⁺}    {u = [ _ ]} (lift ()) _
trans⁺ [ _ ] {m = ⊤⁺}    {u = [ _ ]} _ (lift ())
trans⁺ ⊤⁺    {m = ⊥⁺}                (lift ()) _
trans⁺ ⊤⁺    {m = [ _ ]}             (lift ()) _
trans⁺ ⊤⁺    {m = ⊤⁺}                (lift ()) _
