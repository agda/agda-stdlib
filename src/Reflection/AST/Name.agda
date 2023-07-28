------------------------------------------------------------------------
-- The Agda standard library
--
-- Names used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Name where

open import Data.List.Base              using (List)
import Data.Product.Properties as Prodₚ using (≡-dec)
import Data.Word.Properties as Wₚ       using (_≟_)
open import Function.Base               using (_on_)
open import Relation.Nullary.Decidable                 using (map′)
open import Relation.Binary                            using (Rel; Decidable; DecidableEquality)
open import Relation.Binary.Construct.On               using (decidable)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)

----------------------------------------------------------------------
-- Re-export built-ins

open import Agda.Builtin.Reflection public
  using (Name) renaming (primQNameToWord64s to toWords; primQNameEquality to _≡ᵇ_)

open import Agda.Builtin.Reflection.Properties public
  renaming (primQNameToWord64sInjective to toWords-injective)

----------------------------------------------------------------------
-- More definitions
----------------------------------------------------------------------

Names : Set
Names = List Name

----------------------------------------------------------------------
-- Decidable equality for names
----------------------------------------------------------------------

infix 4 _≈?_ _≟_ _≈_

_≈_ : Rel Name _
_≈_ = _≡_ on toWords

_≈?_ : Decidable _≈_
_≈?_ = decidable toWords _≡_ (Prodₚ.≡-dec Wₚ._≟_ Wₚ._≟_)

_≟_ : DecidableEquality Name
m ≟ n = map′ (toWords-injective _ _) (cong toWords) (m ≈? n)
