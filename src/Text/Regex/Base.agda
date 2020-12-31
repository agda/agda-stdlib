------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions: basic types and semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Preorder; Setoid)

module Text.Regex.Base {a e r} (P : Preorder a e r) where

open import Level using (_⊔_)

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.List.Base as L using (List; []; _∷_; _++_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality

open Preorder P using (_≈_) renaming (Carrier to A; _∼_ to _≤_)

open import Data.List.Relation.Ternary.Appending.Propositional {A = A}
open import Data.List.Relation.Ternary.Appending.Propositional.Properties {A = A}

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
  field fromStart  : Bool
        tillEnd    : Bool
        expression : Exp

updateExp : (Exp → Exp) → Regex → Regex
updateExp f r = record r { expression = f (Regex.expression r) }

------------------------------------------------------------------------
-- Derived notions: nothing, anything, at least one and maybe one

pattern ∅ = [ List.[] ]
pattern · = [^ List.[] ]

pattern singleton a = [ Range.[ a ] ∷ [] ]

infixl 7 _+ _⁇
_+ : Exp → Exp
e + = e ∙ e ⋆

_⁇ : Exp → Exp
∅ ⁇ = ε
e ⁇ = ε ∣ e

-- View: is⊘, isε

is-∅ : ∀ (e : Exp) → Dec (e ≡ ∅)
is-∅ ε          = no (λ ())
is-∅ [ [] ]     = yes refl
is-∅ [ r ∷ rs ] = no (λ ())
is-∅ [^ rs ]    = no (λ ())
is-∅ (e ∣ f)    = no (λ ())
is-∅ (e ∙ f)    = no (λ ())
is-∅ (e ⋆)      = no (λ ())

is-ε : ∀ (e : Exp) → Dec (e ≡ ε)
is-ε ε       = yes refl
is-ε [ rs ]  = no (λ ())
is-ε [^ rs ] = no (λ ())
is-ε (e ∣ f) = no (λ ())
is-ε (e ∙ f) = no (λ ())
is-ε (e ⋆)   = no (λ ())

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

------------------------------------------------------------------------
-- Small inversion lemmas

∉∅ : ∀ {xs} → xs ∉ ∅
∉∅ [ () ]

∈ε⋆-inv : ∀ {w} → w ∈ (ε ⋆) → w ∈ ε
∈ε⋆-inv (star (sum (inj₁ ε))) = ε
∈ε⋆-inv (star (sum (inj₂ (prod eq ε p)))) rewrite []++⁻¹ eq = ∈ε⋆-inv p

∈∅⋆-inv : ∀ {w} → w ∈ (∅ ⋆) → w ∈ ε
∈∅⋆-inv (star (sum (inj₁ ε))) = ε
∈∅⋆-inv (star (sum (inj₂ (prod eq p q)))) = contradiction p ∉∅

∈ε∙e-inv : ∀ {w e} → w ∈ (ε ∙ e) → w ∈ e
∈ε∙e-inv (prod eq ε p) rewrite []++⁻¹ eq = p

∈e∙ε-inv : ∀ {w e} → w ∈ (e ∙ ε) → w ∈ e
∈e∙ε-inv (prod eq p ε) rewrite ++[]⁻¹ eq = p
