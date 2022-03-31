------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.StrictPartialOrder
       {s₁ s₂ s₃} (SPO : StrictPartialOrder s₁ s₂ s₃) where

open import Data.Product using (_,_)
open import Function using (flip; _∘_)
private module SPO = Relation.Binary.StrictPartialOrder SPO
open SPO hiding (Carrier; _≈_; trans; isEquivalence; module Eq)
open import Relation.Binary.Construct.StrictToNonStrict SPO._≈_ _<_

------------------------------------------------------------------------
-- Strict partial orders can be converted to posets

poset : Poset _ _ _
poset = record
  { isPartialOrder = isPartialOrder isStrictPartialOrder
  }

open Poset poset public

------------------------------------------------------------------------
-- The inverse relation is also a strict partial order.

infix 4 _>_

_>_ : Rel Carrier s₃
x > y = y < x

>-isStrictPartialOrder : IsStrictPartialOrder _≈_ _>_
>-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = irrefl ∘ Eq.sym
  ; trans         = flip SPO.trans
  ; <-resp-≈      = <-respˡ-≈ , <-respʳ-≈
  }

>-strictPartialOrder : StrictPartialOrder s₁ s₂ s₃
>-strictPartialOrder = record { isStrictPartialOrder = >-isStrictPartialOrder }

open StrictPartialOrder >-strictPartialOrder public
  using ()
  renaming
  ( irrefl   to >-irrefl
  ; trans    to >-trans
  ; <-resp-≈ to >-resp-≈
  )
