------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of regular expressions and their semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex.Properties {a e r} (P? : DecPoset a e r) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (all?)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_$_)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Negation using (contradiction; ¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)

import Relation.Unary  as U
open import Relation.Binary using (Decidable)
import Relation.Binary.PropositionalEquality as P

open DecPoset P? renaming (Carrier to A)
open import Text.Regex.Base preorder

open import Data.List.Relation.Binary.Pointwise using ([])
open import Data.List.Relation.Ternary.Appending.Propositional {A = A}
open import Data.List.Relation.Ternary.Appending.Propositional.Properties {A = A}

------------------------------------------------------------------------
-- Publicly re-export core properties

open import Text.Regex.Properties.Core preorder public

------------------------------------------------------------------------
-- Decidability results

[]∈?_ : U.Decidable ([] ∈_)
[]∈? ε       = yes ε
[]∈? [ rs ]  = no (λ ())
[]∈? [^ rs ] = no (λ ())
[]∈? (e ∣ f) = map′ sum (λ where (sum pr) → pr)
             $ ([]∈? e) ⊎-dec ([]∈? f)
[]∈? (e ∙ f) = map′ (uncurry (prod ([]++ []))) []∈e∙f-inv
             $ ([]∈? e) ×-dec ([]∈? f)
[]∈? (e ⋆)   = yes (star (sum (inj₁ ε)))

_∈ᴿ?_ : Decidable _∈ᴿ_
c ∈ᴿ? [ a ]     = map′ [_] (λ where [ eq ] → eq) (c ≟ a)
c ∈ᴿ? (lb ─ ub) = map′ (uncurry _─_) (λ where (ge ─ le) → ge , le)
                $ (lb ≤? c) ×-dec (c ≤? ub)

_∉ᴿ?_ : Decidable _∉ᴿ_
a ∉ᴿ? r = ¬? (a ∈ᴿ? r)

_∈?ε : U.Decidable (_∈ ε)
[]      ∈?ε = yes ε
(a ∷ _) ∈?ε = no (λ ())

_∈?[_] : ∀ w rs → Dec (w ∈ [ rs ])
[]          ∈?[ rs ] = no (λ ())
(a ∷ b ∷ _) ∈?[ rs ] = no (λ ())
(a ∷ [])    ∈?[ rs ] = map′ [_] (λ where [ p ] → p)
                      $ any? (a ∈ᴿ?_) rs

_∈?[^_] : ∀ w rs → Dec (w ∈ [^ rs ])
[]          ∈?[^ rs ] = no (λ ())
(a ∷ [])    ∈?[^ rs ] = map′ [^_] (λ where [^ p ] → p) $ all? (a ∉ᴿ?_) rs
(a ∷ b ∷ _) ∈?[^ rs ] = no (λ ())
