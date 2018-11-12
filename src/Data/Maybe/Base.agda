------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type and some operations
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Maybe.

module Data.Maybe.Base where

open import Level
open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Unit.Base using (⊤)
open import Data.These using (These; this; that; these)
open import Data.Product as Prod using (_×_; _,_)
open import Function
open import Relation.Nullary

------------------------------------------------------------------------
-- Definition

data Maybe {a} (A : Set a) : Set a where
  just    : (x : A) → Maybe A
  nothing : Maybe A

{-# FOREIGN GHC type AgdaMaybe a b = Maybe b #-}
{-# COMPILE GHC Maybe = data MAlonzo.Code.Data.Maybe.Base.AgdaMaybe (Just | Nothing) #-}

------------------------------------------------------------------------
-- Some operations

boolToMaybe : Bool → Maybe ⊤
boolToMaybe true  = just _
boolToMaybe false = nothing

is-just : ∀ {a} {A : Set a} → Maybe A → Bool
is-just (just _) = true
is-just nothing  = false

is-nothing : ∀ {a} {A : Set a} → Maybe A → Bool
is-nothing = not ∘ is-just

decToMaybe : ∀ {a} {A : Set a} → Dec A → Maybe A
decToMaybe (yes x) = just x
decToMaybe (no _)  = nothing

-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n

-- A non-dependent eliminator.

maybe′ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Maybe A → B
maybe′ = maybe

-- A defaulting mechanism

fromMaybe : ∀ {a} {A : Set a} → A → Maybe A → A
fromMaybe = maybe′ id

-- A safe variant of "fromJust". If the value is nothing, then the
-- return type is the unit type.

module _ {a} {A : Set a} where

  From-just : Maybe A → Set a
  From-just (just _) = A
  From-just nothing  = Lift a ⊤

  from-just : (x : Maybe A) → From-just x
  from-just (just x) = x
  from-just nothing  = _

-- Functoriality: map.

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
map f = maybe (just ∘ f) nothing

-- Alternative: <∣>

_<∣>_ : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
just x  <∣> my = just x
nothing <∣> my = my

------------------------------------------------------------------------
-- Aligning and zipping

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  alignWith : (These A B → C) → Maybe A → Maybe B → Maybe C
  alignWith f (just a) (just b) = just (f (these a b))
  alignWith f (just a) nothing  = just (f (this a))
  alignWith f nothing  (just b) = just (f (that b))
  alignWith f nothing  nothing  = nothing

  zipWith : (A → B → C) → Maybe A → Maybe B → Maybe C
  zipWith f (just a) (just b) = just (f a b)
  zipWith _ _ _ = nothing

module _ {a b} {A : Set a} {B : Set b} where

  align : Maybe A → Maybe B → Maybe (These A B)
  align = alignWith id

  zip : Maybe A → Maybe B → Maybe (A × B)
  zip = zipWith _,_

module _ {a b} {A : Set a} {B : Set b} where

-- Injections.

  thisM : A → Maybe B → These A B
  thisM a = maybe′ (these a) (this a)

  thatM : Maybe A → B → These A B
  thatM = maybe′ these that
