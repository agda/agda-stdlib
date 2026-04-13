------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions: core properties (only require a Preorder)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Preorder)

module Text.Regex.Properties.Core {a e r} (P : Preorder a e r) where

open import Level using (_⊔_)

open import Data.Bool.Base using (Bool)
open import Data.List.Base as List using (List; []; _∷_; _++_)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open Preorder P using (_≈_) renaming (Carrier to A; _∼_ to _≤_)
open import Text.Regex.Base P

open import Data.List.Relation.Ternary.Appending.Propositional.Properties {A = A}
  using (++[]⁻¹; []++⁻¹; conicalˡ; conicalʳ)

------------------------------------------------------------------------
-- Views

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
-- Inversion lemmas

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

[]∈e∙f-inv : ∀ {e f} → [] ∈ (e ∙ f) → [] ∈ e × [] ∈ f
[]∈e∙f-inv (prod eq p q) rewrite conicalˡ eq | conicalʳ eq = p , q
