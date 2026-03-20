------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive pointwise lifting of relations to streams
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream.Relation.Binary.Pointwise where

open import Codata.Guarded.Stream as Stream using (Stream; head; tail)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∘_; _on_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (REL; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Reflexive; Sym; Trans; Antisym; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡ using (setoid)

private
  variable
    a ℓ : Level
    A B C D : Set a
    R S T : REL A B ℓ
    xs ys : Stream A

------------------------------------------------------------------------
-- Bisimilarity

infixr 5 _∷_

record Pointwise (_∼_ : REL A B ℓ) (as : Stream A) (bs : Stream B) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : head as ∼ head bs
    tail : Pointwise _∼_ (tail as) (tail bs)

open Pointwise public

lookup⁺ : ∀ {as bs} → Pointwise R as bs →
          ∀ n → R (Stream.lookup as n) (Stream.lookup bs n)
lookup⁺ rs zero    = rs .head
lookup⁺ rs (suc n) = lookup⁺ (rs .tail) n

map : R ⇒ S → Pointwise R ⇒ Pointwise S
head (map R⇒S xs) = R⇒S (head xs)
tail (map R⇒S xs) = map R⇒S (tail xs)

reflexive : Reflexive R → Reflexive (Pointwise R)
head (reflexive R-refl) = R-refl
tail (reflexive R-refl) = reflexive R-refl

symmetric : Sym R S → Sym (Pointwise R) (Pointwise S)
head (symmetric R-sym-S xsRys) = R-sym-S (head xsRys)
tail (symmetric R-sym-S xsRys) = symmetric R-sym-S (tail xsRys)

transitive : Trans R S T → Trans (Pointwise R) (Pointwise S) (Pointwise T)
head (transitive RST-trans xsRys ysSzs) = RST-trans (head xsRys) (head ysSzs)
tail (transitive RST-trans xsRys ysSzs) = transitive RST-trans (tail xsRys) (tail ysSzs)

isEquivalence : IsEquivalence R → IsEquivalence (Pointwise R)
isEquivalence equiv^R = record
  { refl  = reflexive equiv^R.refl
  ; sym   = symmetric equiv^R.sym
  ; trans = transitive equiv^R.trans
  } where module equiv^R = IsEquivalence equiv^R

setoid : Setoid a ℓ → Setoid a ℓ
setoid S = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence S)
  }

antisymmetric : Antisym R S T → Antisym (Pointwise R) (Pointwise S) (Pointwise T)
head (antisymmetric RST-antisym xsRys ysSxs) = RST-antisym (head xsRys) (head ysSxs)
tail (antisymmetric RST-antisym xsRys ysSxs) = antisymmetric RST-antisym (tail xsRys) (tail ysSxs)

tabulate⁺ : ∀ {f : ℕ → A} {g : ℕ → B} →
            (∀ i → R (f i) (g i)) → Pointwise R (Stream.tabulate f) (Stream.tabulate g)
head (tabulate⁺ f∼g) = f∼g 0
tail (tabulate⁺ f∼g) = tabulate⁺ (f∼g ∘ suc)

tabulate⁻ : ∀ {f : ℕ → A} {g : ℕ → B} →
            Pointwise R (Stream.tabulate f) (Stream.tabulate g) → (∀ i → R (f i) (g i))
tabulate⁻ xsRys zero    = head xsRys
tabulate⁻ xsRys (suc i) = tabulate⁻ (tail xsRys) i

map⁺ : ∀ (f : A → C) (g : B → D) →
       Pointwise (λ a b → R (f a) (g b)) xs ys →
       Pointwise R (Stream.map f xs) (Stream.map g ys)
head (map⁺ f g faRgb) = head faRgb
tail (map⁺ f g faRgb) = map⁺ f g (tail faRgb)

map⁻ : ∀ (f : A → C) (g : B → D) →
       Pointwise R (Stream.map f xs) (Stream.map g ys) →
       Pointwise (λ a b → R (f a) (g b)) xs ys
head (map⁻ f g faRgb) = head faRgb
tail (map⁻ f g faRgb) = map⁻ f g (tail faRgb)

drop⁺ : ∀ n → Pointwise R ⇒ (Pointwise R on Stream.drop n)
drop⁺ zero    as≈bs = as≈bs
drop⁺ (suc n) as≈bs = drop⁺ n (as≈bs .tail)

------------------------------------------------------------------------
-- Pointwise Equality as a Bisimilarity

module _ {A : Set a} where

 infix 1 _≈_
 _≈_ : Stream A → Stream A → Set a
 _≈_ = Pointwise _≡_

 refl : Reflexive _≈_
 refl = reflexive ≡.refl

 sym : Symmetric _≈_
 sym = symmetric ≡.sym

 trans : Transitive _≈_
 trans = transitive ≡.trans

 ≈-setoid : Setoid _ _
 ≈-setoid = setoid (≡.setoid A)

------------------------------------------------------------------------
-- Pointwise DSL
--
-- A guardedness check does not play well with compositional proofs.
-- Luckily we can learn from Nils Anders Danielsson's
-- Beating the Productivity Checker Using Embedded Languages
-- and design a little compositional DSL to define such proofs
--
-- NOTE: also because of the guardedness check we can't use the standard
-- `Relation.Binary.Reasoning.Syntax` approach.

module pw-Reasoning (S : Setoid a ℓ) where
  private module S = Setoid S
  open S using (Carrier) renaming (_≈_ to _∼_)

  record `Pointwise∞ (as bs : Stream Carrier) : Set (a ⊔ ℓ)
  data   `Pointwise  (as bs : Stream Carrier) : Set (a ⊔ ℓ)

  record `Pointwise∞ as bs where
    coinductive
    field
      head : (as .head) ∼ (bs .head)
      tail : `Pointwise (as .tail) (bs .tail)

  data `Pointwise as bs where
    `lift  : Pointwise _∼_ as bs → `Pointwise as bs
    `step  : `Pointwise∞ as bs → `Pointwise as bs
    `refl  : as ≡ bs → `Pointwise as bs
    `bisim : as ≈ bs → `Pointwise as bs
    `sym   : `Pointwise bs as → `Pointwise as bs
    `trans : ∀ {ms} → `Pointwise as ms → `Pointwise ms bs → `Pointwise as bs

  open `Pointwise∞ public

  `head : ∀ {as bs} → `Pointwise as bs → as .head ∼ bs .head
  `head (`lift rs)         = rs .head
  `head (`refl eq)         = S.reflexive (≡.cong head eq)
  `head (`bisim rs)        = S.reflexive (rs .head)
  `head (`step `rs)        = `rs .head
  `head (`sym `rs)         = S.sym (`head `rs)
  `head (`trans `rs₁ `rs₂) = S.trans (`head `rs₁) (`head `rs₂)

  `tail : ∀ {as bs} → `Pointwise as bs → `Pointwise (as .tail)  (bs .tail)
  `tail (`lift rs)         = `lift (rs .tail)
  `tail (`refl eq)         = `refl (≡.cong tail eq)
  `tail (`bisim rs)        = `bisim (rs .tail)
  `tail (`step `rs)        = `rs .tail
  `tail (`sym `rs)         = `sym (`tail `rs)
  `tail (`trans `rs₁ `rs₂) = `trans (`tail `rs₁) (`tail `rs₂)

  run : ∀ {as bs} → `Pointwise as bs → Pointwise _∼_ as bs
  run `rs .head = `head `rs
  run `rs .tail = run (`tail `rs)

  infix  1 begin_
  infixr 2 _↺⟨_⟩_ _↺⟨_⟨_ _∼⟨_⟩_ _∼⟨_⟨_ _≈⟨_⟩_ _≈⟨_⟨_ _≡⟨_⟩_ _≡⟨_⟨_ _≡⟨⟩_
  infix  3 _∎

  -- Beginning of a proof
  begin_ : ∀ {as bs} → `Pointwise∞ as bs → Pointwise _∼_ as bs
  (begin `rs) .head = `rs .head
  (begin `rs) .tail = run (`rs .tail)

  pattern _↺⟨_⟩_  as as∼bs bs∼cs = `trans {as = as} (`step as∼bs) bs∼cs
  pattern _↺⟨_⟨_ as bs∼as bs∼cs = `trans {as = as} (`sym (`step bs∼as)) bs∼cs
  pattern _∼⟨_⟩_  as as∼bs bs∼cs = `trans {as = as} (`lift as∼bs) bs∼cs
  pattern _∼⟨_⟨_ as bs∼as bs∼cs = `trans {as = as} (`sym (`lift bs∼as)) bs∼cs
  pattern _≈⟨_⟩_  as as∼bs bs∼cs = `trans {as = as} (`bisim as∼bs) bs∼cs
  pattern _≈⟨_⟨_ as bs∼as bs∼cs = `trans {as = as} (`sym (`bisim bs∼as)) bs∼cs
  pattern _≡⟨_⟩_  as as∼bs bs∼cs = `trans {as = as} (`refl as∼bs) bs∼cs
  pattern _≡⟨_⟨_ as bs∼as bs∼cs = `trans {as = as} (`sym (`refl bs∼as)) bs∼cs
  pattern _≡⟨⟩_   as as∼bs       = `trans {as = as} (`refl ≡.refl) as∼bs
  pattern _∎      as             = `refl  {as = as} ≡.refl


  -- Deprecated v2.0
  infixr 2 _↺˘⟨_⟩_ _∼˘⟨_⟩_ _≈˘⟨_⟩_ _≡˘⟨_⟩_
  pattern _↺˘⟨_⟩_ as bs∼as bs∼cs = `trans {as = as} (`sym (`step bs∼as)) bs∼cs
  pattern _∼˘⟨_⟩_ as bs∼as bs∼cs = `trans {as = as} (`sym (`lift bs∼as)) bs∼cs
  pattern _≈˘⟨_⟩_ as bs∼as bs∼cs = `trans {as = as} (`sym (`bisim bs∼as)) bs∼cs
  pattern _≡˘⟨_⟩_ as bs∼as bs∼cs = `trans {as = as} (`sym (`refl bs∼as)) bs∼cs
  {-# WARNING_ON_USAGE _↺˘⟨_⟩_
  "Warning: _↺˘⟨_⟩_ was deprecated in v2.0.
  Please use _↺⟨_⟨_ instead."
  #-}
  {-# WARNING_ON_USAGE _∼˘⟨_⟩_
  "Warning: _∼˘⟨_⟩_ was deprecated in v2.0.
  Please use _∼⟨_⟨_ instead."
  #-}
  {-# WARNING_ON_USAGE _≈˘⟨_⟩_
  "Warning: _≈˘⟨_⟩_ was deprecated in v2.0.
  Please use _≈⟨_⟨_ instead."
  #-}
  {-# WARNING_ON_USAGE _≡˘⟨_⟩_
  "Warning: _≡˘⟨_⟩_ was deprecated in v2.0.
  Please use _≡⟨_⟨_ instead."
  #-}


module ≈-Reasoning {a} {A : Set a} where

  open pw-Reasoning (≡.setoid A) public

  infix 4 _≈∞_
  _≈∞_ = `Pointwise∞
