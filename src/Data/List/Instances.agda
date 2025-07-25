------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Instances where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Effectful
  using (functor; applicative; applicativeZero; alternative; monad
        ; monadZero; monadPlus)
import Data.List.Effectful.Transformer as Trans
  using (functor; applicative; monad; monadT)
open import Data.List.Properties
  using (≡-dec)
open import Data.List.Literals
  using (isString)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise)
open import Data.List.Relation.Binary.Lex.NonStrict
  using (Lex-≤; ≤-isDecTotalOrder)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses
  using (IsDecTotalOrder; IsDecEquivalence; _≟_)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

instance
  -- List
  listFunctor = functor
  listApplicative = applicative
  listApplicativeZero = applicativeZero
  listAlternative = alternative
  listMonad = monad
  listMonadZero = monadZero
  listMonadPlus = monadPlus
  listIsString = isString
  -- ListT
  listTFunctor = λ {f} {g} {M} {{inst}} → Trans.functor {f} {g} {M} inst
  listTApplicative = λ {f} {g} {M} {{inst}} → Trans.applicative {f} {g} {M} inst
  listTMonad = λ {f} {g} {M} {{inst}} → Trans.monad {f} {g} {M} inst
  listTMonadT = λ {f} {g} {M} {{inst}} → Trans.monadT {f} {g} {M} inst

  List-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = List A} _≡_
  List-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)

  List-Lex-≤-isDecTotalOrder : {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂}
                             → {{IsDecTotalOrder _≈_ _≼_}}
                             → IsDecTotalOrder (Pointwise _≈_) (Lex-≤ _≈_ _≼_)
  List-Lex-≤-isDecTotalOrder {{≼-isDecTotalOrder}} = ≤-isDecTotalOrder ≼-isDecTotalOrder
