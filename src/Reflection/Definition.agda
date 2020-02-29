------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Definition where

open import Data.List.Base using (map)
import Data.List.Properties as Listₚ
import Data.Nat.Properties as ℕₚ
import Data.Nat.Show as NatShow
open import Data.Product using (_×_; <_,_>; uncurry)
open import Data.String as String using (String; _<+>_; intersperse; braces)
open import Function using (_∘′_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality

import Reflection.Argument as Arg
import Reflection.Name     as Name
import Reflection.Term     as Term

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

constructor′-injective : ∀ {c c′} → constructor′ c ≡ constructor′ c′ → c ≡ c′
constructor′-injective refl = refl

_≟_ : DecidableEquality Definition
function cs       ≟ function cs′        =
  Dec.map′ (cong function) function-injective (cs Term.≟-Clauses cs′)
data-type pars cs ≟ data-type pars′ cs′ =
  Dec.map′ (uncurry (cong₂ data-type)) data-type-injective
           (pars ℕₚ.≟ pars′ ×-dec Listₚ.≡-dec Name._≟_ cs cs′)
record′ c fs      ≟ record′ c′ fs′      =
  Dec.map′ (uncurry (cong₂ record′)) record′-injective
           (c Name.≟ c′ ×-dec Listₚ.≡-dec (Arg.≡-dec Name._≟_) fs fs′)
constructor′ d    ≟ constructor′ d′     =
  Dec.map′ (cong constructor′) constructor′-injective (d Name.≟ d′)
axiom             ≟ axiom               = yes refl
primitive′        ≟ primitive′          = yes refl

-- antidiagonal
function cs ≟ data-type pars cs₁ = no (λ ())
function cs ≟ record′ c fs = no (λ ())
function cs ≟ constructor′ d = no (λ ())
function cs ≟ axiom = no (λ ())
function cs ≟ primitive′ = no (λ ())
data-type pars cs ≟ function cs₁ = no (λ ())
data-type pars cs ≟ record′ c fs = no (λ ())
data-type pars cs ≟ constructor′ d = no (λ ())
data-type pars cs ≟ axiom = no (λ ())
data-type pars cs ≟ primitive′ = no (λ ())
record′ c fs ≟ function cs = no (λ ())
record′ c fs ≟ data-type pars cs = no (λ ())
record′ c fs ≟ constructor′ d = no (λ ())
record′ c fs ≟ axiom = no (λ ())
record′ c fs ≟ primitive′ = no (λ ())
constructor′ d ≟ function cs = no (λ ())
constructor′ d ≟ data-type pars cs = no (λ ())
constructor′ d ≟ record′ c fs = no (λ ())
constructor′ d ≟ axiom = no (λ ())
constructor′ d ≟ primitive′ = no (λ ())
axiom ≟ function cs = no (λ ())
axiom ≟ data-type pars cs = no (λ ())
axiom ≟ record′ c fs = no (λ ())
axiom ≟ constructor′ d = no (λ ())
axiom ≟ primitive′ = no (λ ())
primitive′ ≟ function cs = no (λ ())
primitive′ ≟ data-type pars cs = no (λ ())
primitive′ ≟ record′ c fs = no (λ ())
primitive′ ≟ constructor′ d = no (λ ())
primitive′ ≟ axiom = no (λ ())
