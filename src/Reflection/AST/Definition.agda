------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Definition where

import Data.List.Properties as List                    using (≡-dec)
import Data.Nat.Properties as ℕ                        using (_≟_)
open import Data.Product.Base                          using (_×_; <_,_>; uncurry)
open import Relation.Nullary.Decidable.Core            using (map′; _×-dec_; yes; no)
open import Relation.Binary.Definitions                using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂)

import Reflection.AST.Argument          as Arg
import Reflection.AST.Argument.Quantity as Quantity
import Reflection.AST.Name              as Name
import Reflection.AST.Term              as Term

------------------------------------------------------------------------
-- Re-exporting type publically

open import Agda.Builtin.Reflection public
  using    ( Definition
           ; function
           ; data-type
           ; axiom
           )
  renaming ( record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′ )

------------------------------------------------------------------------
-- Decidable equality

function-injective : ∀ {cs cs′} → function cs ≡ function cs′ → cs ≡ cs′
function-injective refl = refl

data-type-injective₁ : ∀ {pars pars′ cs cs′} → data-type pars cs ≡ data-type pars′ cs′ → pars ≡ pars′
data-type-injective₁ refl = refl

data-type-injective₂ : ∀ {pars pars′ cs cs′} → data-type pars cs ≡ data-type pars′ cs′ → cs ≡ cs′
data-type-injective₂ refl = refl

data-type-injective : ∀ {pars pars′ cs cs′} → data-type pars cs ≡ data-type pars′ cs′ → pars ≡ pars′ × cs ≡ cs′
data-type-injective = < data-type-injective₁ , data-type-injective₂ >

record′-injective₁ : ∀ {c c′ fs fs′} → record′ c fs ≡ record′ c′ fs′ → c ≡ c′
record′-injective₁ refl = refl

record′-injective₂ : ∀ {c c′ fs fs′} → record′ c fs ≡ record′ c′ fs′ → fs ≡ fs′
record′-injective₂ refl = refl

record′-injective : ∀ {c c′ fs fs′} → record′ c fs ≡ record′ c′ fs′ → c ≡ c′ × fs ≡ fs′
record′-injective = < record′-injective₁ , record′-injective₂ >

constructor′-injective₁ : ∀ {c c′ q q′} → constructor′ c q ≡ constructor′ c′ q′ → c ≡ c′
constructor′-injective₁ refl = refl

constructor′-injective₂ : ∀ {c c′ q q′} → constructor′ c q ≡ constructor′ c′ q′ → q ≡ q′
constructor′-injective₂ refl = refl

constructor′-injective : ∀ {c c′ q q′} → constructor′ c q ≡ constructor′ c′ q′ → c ≡ c′ × q ≡ q′
constructor′-injective = < constructor′-injective₁ , constructor′-injective₂ >

infix 4 _≟_

_≟_ : DecidableEquality Definition
function cs       ≟ function cs′        =
  map′ (cong function) function-injective (cs Term.≟-Clauses cs′)
data-type pars cs ≟ data-type pars′ cs′ =
  map′ (uncurry (cong₂ data-type)) data-type-injective
           (pars ℕ.≟ pars′ ×-dec List.≡-dec Name._≟_ cs cs′)
record′ c fs      ≟ record′ c′ fs′      =
  map′ (uncurry (cong₂ record′)) record′-injective
           (c Name.≟ c′ ×-dec List.≡-dec (Arg.≡-dec Name._≟_) fs fs′)
constructor′ d q  ≟ constructor′ d′ q′  =
  map′ (uncurry (cong₂ constructor′)) constructor′-injective
           (d Name.≟ d′ ×-dec q Quantity.≟ q′)
axiom             ≟ axiom               = yes refl
primitive′        ≟ primitive′          = yes refl

-- antidiagonal
function cs ≟ data-type pars cs₁ = no (λ ())
function cs ≟ record′ c fs = no (λ ())
function cs ≟ constructor′ d q = no (λ ())
function cs ≟ axiom = no (λ ())
function cs ≟ primitive′ = no (λ ())
data-type pars cs ≟ function cs₁ = no (λ ())
data-type pars cs ≟ record′ c fs = no (λ ())
data-type pars cs ≟ constructor′ d q = no (λ ())
data-type pars cs ≟ axiom = no (λ ())
data-type pars cs ≟ primitive′ = no (λ ())
record′ c fs ≟ function cs = no (λ ())
record′ c fs ≟ data-type pars cs = no (λ ())
record′ c fs ≟ constructor′ d q = no (λ ())
record′ c fs ≟ axiom = no (λ ())
record′ c fs ≟ primitive′ = no (λ ())
constructor′ d q ≟ function cs = no (λ ())
constructor′ d q ≟ data-type pars cs = no (λ ())
constructor′ d q ≟ record′ c fs = no (λ ())
constructor′ d q ≟ axiom = no (λ ())
constructor′ d q ≟ primitive′ = no (λ ())
axiom ≟ function cs = no (λ ())
axiom ≟ data-type pars cs = no (λ ())
axiom ≟ record′ c fs = no (λ ())
axiom ≟ constructor′ d q = no (λ ())
axiom ≟ primitive′ = no (λ ())
primitive′ ≟ function cs = no (λ ())
primitive′ ≟ data-type pars cs = no (λ ())
primitive′ ≟ record′ c fs = no (λ ())
primitive′ ≟ constructor′ d q = no (λ ())
primitive′ ≟ axiom = no (λ ())
