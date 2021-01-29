------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions: basic types and semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Preorder)

module Text.Regex.Base {a e r} (P : Preorder a e r) where

open import Level using (_⊔_)

open import Data.Bool.Base using (Bool)
open import Data.List.Base as L using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All using (All)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality

open Preorder P using (_≈_) renaming (Carrier to A; _∼_ to _≤_)
open import Data.List.Relation.Ternary.Appending.Propositional {A = A}

------------------------------------------------------------------------
-- Regular expressions on the alphabet A

infix 10 [_] _─_
data Range : Set a where
  [_] : (a : A)     → Range
  _─_ : (lb ub : A) → Range

infixr 5 _∣_
infixr 6 _∙_
infixl 7 _⋆
infix 10 [^_]

data Exp : Set a where
  ε    : Exp
  [_]  : (rs : List Range) → Exp
  [^_] : (rs : List Range) → Exp
  _∣_  : (e f : Exp) → Exp
  _∙_  : (e f : Exp) → Exp
  _⋆   : (e : Exp) → Exp

-- A regular expression has additional parameters:
-- * should the match begin at the very start of the input?
-- * should it span until the very end?

record Regex : Set a where
  field
    fromStart  : Bool
    tillEnd    : Bool
    expression : Exp

updateExp : (Exp → Exp) → Regex → Regex
updateExp f r = record r { expression = f (Regex.expression r) }

------------------------------------------------------------------------
-- Derived notions: nothing, anything, and singleton

pattern ∅ = [ List.[] ]
pattern · = [^ List.[] ]

pattern singleton a = [ Range.[ a ] ∷ [] ]

------------------------------------------------------------------------
-- Semantics: matching words

infix 4 _∈ᴿ_ _∉ᴿ_
data _∈ᴿ_ (c : A) : Range → Set (a ⊔ r ⊔ e) where
  [_] : ∀ {val}   → c ≈ val         → c ∈ᴿ [ val ]
  _─_ : ∀ {lb ub} → lb ≤ c → c ≤ ub → c ∈ᴿ (lb ─ ub)

_∉ᴿ_ : A → Range → Set (a ⊔ r ⊔ e)
a ∉ᴿ r = ¬ (a ∈ᴿ r)

infix 4 _∈_ _∉_
data _∈_ : List A → Exp → Set (a ⊔ r ⊔ e) where
  ε      :                                                     []      ∈ ε
  [_]    : ∀ {a rs} → Any (a ∈ᴿ_) rs →                         L.[ a ] ∈ [ rs ]
  [^_]   : ∀ {a rs} → All (a ∉ᴿ_) rs →                         L.[ a ] ∈ [^ rs ]
  sum    : ∀ {w e f} → (w ∈ e) ⊎ (w ∈ f) →                     w       ∈ (e ∣ f)
  prod   : ∀ {v w vw e f} → Appending v w vw → v ∈ e → w ∈ f → vw      ∈ (e ∙ f)
  star   : ∀ {v e} → v ∈ (ε ∣ e ∙ (e ⋆)) →                     v       ∈ (e ⋆)

_∉_ : List A → Exp → Set (a ⊔ r ⊔ e)
w ∉ e = ¬ (w ∈ e)
