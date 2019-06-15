------------------------------------------------------------------------
-- The Agda standard library
--
-- Names used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Name where

open import Data.List.Base
import Data.Product.Properties as Prodₚ
import Data.Word.Properties as Wₚ
open import Function
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality

open import Agda.Builtin.Reflection public
  using (Name)
  renaming ( primShowQName to show
           ; primQNameToWord64s to toWords
           )

open import Agda.Builtin.Reflection.Properties public
  renaming ( primQNameToWord64sInjective to toWords-injective )

Names : Set
Names = List Name

-- Equality of names is decidable.

_≈_ : Rel Name _
_≈_ = _≡_ on toWords

infix 4 _≈?_ _≟_

_≈?_ : Decidable _≈_
_≈?_ = On.decidable toWords _≡_ (Prodₚ.≡-dec Wₚ._≟_ Wₚ._≟_)

_≟_ : DecidableEquality Name
m ≟ n = map′ (toWords-injective _ _) (cong toWords) (m ≈? n)
