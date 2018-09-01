------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of equality for keys for AVL trees.
------------------------------------------------------------------------

open import Relation.Binary

module Data.AVL.Key.Relation.Pointwise
       {k e} (Key : Set k) (_≈_ : Rel Key e) where

open import Data.AVL.Key Key

open import Level
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

infix 4 _≈⁺_

_≈⁺_ : Rel Key⁺ e
⊥⁺    ≈⁺ ⊥⁺    = Lift e ⊤
⊤⁺    ≈⁺ ⊤⁺    = Lift e ⊤
[ k ] ≈⁺ [ l ] = k ≈ l
_     ≈⁺ _     = Lift e ⊥

≈⁺-refl : Reflexive _≈_ → Reflexive _≈⁺_
≈⁺-refl ≈-refl {⊥⁺}    = _
≈⁺-refl ≈-refl {⊤⁺}    = _
≈⁺-refl ≈-refl {[ k ]} = ≈-refl

≈⁺-sym : Symmetric _≈_ → Symmetric _≈⁺_
≈⁺-sym ≈-sym {⊥⁺}    {⊥⁺}    = _
≈⁺-sym ≈-sym {⊤⁺}    {⊤⁺}    = _
≈⁺-sym ≈-sym {[ k ]} {[ l ]} = ≈-sym
-- impossible cases
≈⁺-sym ≈-sym {⊥⁺} {⊤⁺} ()
≈⁺-sym ≈-sym {⊥⁺} {[ l ]} ()
≈⁺-sym ≈-sym {⊤⁺} {⊥⁺} ()
≈⁺-sym ≈-sym {⊤⁺} {[ l ]} ()
≈⁺-sym ≈-sym {[ k ]} {⊥⁺} ()
≈⁺-sym ≈-sym {[ k ]} {⊤⁺} ()

≈⁺-trans : Transitive _≈_ → Transitive _≈⁺_
≈⁺-trans ≈-trans {⊥⁺}    {⊥⁺}    {m}     = λ _ l≈m → l≈m
≈⁺-trans ≈-trans {⊤⁺}    {⊤⁺}    {m}     = λ _ l≈m → l≈m
≈⁺-trans ≈-trans {[ k ]} {[ l ]} {[ m ]} = ≈-trans
-- impossible cases
≈⁺-trans ≈-trans {⊥⁺} {⊤⁺} {m} ()
≈⁺-trans ≈-trans {⊥⁺} {[ k ]} {m} ()
≈⁺-trans ≈-trans {⊤⁺} {⊥⁺} {m} ()
≈⁺-trans ≈-trans {⊤⁺} {[ l ]} {m} ()
≈⁺-trans ≈-trans {[ k ]} {⊥⁺} {m} ()
≈⁺-trans ≈-trans {[ k ]} {⊤⁺} {m} ()
≈⁺-trans ≈-trans {[ k ]} {[ l ]} {⊥⁺} _ ()
≈⁺-trans ≈-trans {[ k ]} {[ l ]} {⊤⁺} _ ()

≈⁺-dec : Decidable _≈_ → Decidable _≈⁺_
≈⁺-dec ≈-dec ⊥⁺    ⊥⁺    = yes _
≈⁺-dec ≈-dec ⊤⁺    ⊤⁺    = yes _
≈⁺-dec ≈-dec [ k ] [ l ] = ≈-dec k l
-- negative cases
≈⁺-dec ≈-dec ⊥⁺ ⊤⁺ = no λ ()
≈⁺-dec ≈-dec ⊥⁺ [ k ] = no λ ()
≈⁺-dec ≈-dec ⊤⁺ ⊥⁺ = no λ ()
≈⁺-dec ≈-dec ⊤⁺ [ k ] = no λ ()
≈⁺-dec ≈-dec [ k ] ⊥⁺ = no λ ()
≈⁺-dec ≈-dec [ k ] ⊤⁺ = no λ ()


≈⁺-isEquivalence : IsEquivalence _≈_ → IsEquivalence _≈⁺_
≈⁺-isEquivalence isEquiv = record
  { refl  = λ {x} → ≈⁺-refl refl {x}
  ; sym   = λ {x} → ≈⁺-sym sym {x}
  ; trans = λ {x} → ≈⁺-trans trans {x}
  } where open IsEquivalence isEquiv
