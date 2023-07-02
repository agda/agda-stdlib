{-# OPTIONS --safe --cubical-compatible #-}

module TakeWhile where

open import Level
open import Data.List.Base hiding (takeWhile)
open import Data.List.Relation.Unary.All as List using ([]; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; refl)
open import Data.List.Relation.Ternary.Appending.Propositional
open import Data.Product using (_×_; proj₁)
open import Data.Maybe.Relation.Unary.All as Maybe using (nothing; just)
import Data.Nat
open import Relation.Unary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Product

-- Original bug reported in #1765 by James Wood
_ : Appending (3 ∷ []) (2 ∷ []) (3 ∷ 2 ∷ [])
_ = P.refl ∷ []++ P.refl ∷ []


variable
  a p : Level
  A : Set a
  P : A → Set p

infix 1 _,_,_
record TakeWhile {A : Set a} (P : A → Set p) xs : Set (a ⊔ p) where
  constructor _,_,_
  field
    {prefix rest} : List A
    goodPrefix : List.All P prefix
    isPrefix : Appending prefix rest xs
    isBiggest : Maybe.All (proj₁ ⊢ ∁ P) (uncons rest)
open TakeWhile public

takeWhile : Decidable P → Π[ TakeWhile P ]
takeWhile P? [] = [] , []++ [] , nothing
takeWhile P? (x ∷ xs) with P? x
... | yes px = let (pxs' , prf , biggest) = takeWhile P? xs in
               px ∷ pxs' , P.refl ∷ prf , biggest
... | no ¬px = [] , []++ refl P.refl , just ¬px

open import Data.Char
open import Data.String using (toList)

lower? : (c : Char) → Dec ('a' ≤ c × c ≤ 'z')
lower? c = 'a' ≤? c ×-dec c ≤? 'z'

_ : takeWhile lower? (toList "helLo")
  ≡ record { prefix = toList "hel"
           ; isPrefix = P.refl ∷ P.refl ∷ P.refl ∷ []++ P.refl ∷ P.refl ∷ []
           }
_ = P.refl
