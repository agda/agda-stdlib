------------------------------------------------------------------------
-- The Agda standard library
--
-- Format strings for Printf and Scanf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Function.Definitions

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Binary.Bundles

module Text.Language.Grammar {σₛ ℓₛ} (Σₛ : Setoid σₛ ℓₛ) where

open Setoid Σₛ renaming (Carrier to Σ)

open import Data.Nat using (ℕ)
import Data.List.Membership.Setoid as L
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.List.Relation.Binary.Pointwise as P using (Pointwise)
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Base

open import Function.Base using (_∘_)

open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Unary as Pred using (Pred; U)
open import Relation.Nullary

open import Level using (_⊔_) renaming (suc to lsuc)

record Grammar : Set (σₛ ⊔ ℓₛ) where
  field
    N : ℕ
    P : List (List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N))
    .Pne : All (λ {(f , _) → Any U f}) P
    S : Fin N

module _ (g : Grammar) where
  open Grammar g
  private
    ΣN-setoid = ⊎-setoid Σₛ (setoid (Fin N))

  open Setoid (ΣN-setoid) using () renaming (_≈_ to _≃_)
  open import Data.List.Relation.Binary.Equality.Setoid (ΣN-setoid)

  data _↦_ : List (Σ ⊎ Fin N) → List (Σ ⊎ Fin N) → Set (σₛ ⊔ ℓₛ) where
    refl↦ : ∀ {x₁ x₂} → x₁ ≋ x₂ → x₁ ↦ x₂
    step↦ : ∀ {s m₁ m₂ e} → L._∈_ (×-setoid ≋-setoid ≋-setoid) (m₁ , m₂) P → (s ++ m₁ ++ e) ↦ (s ++ m₂ ++ e)
    tran↦ : ∀ {x₁ x₂ x₃} → x₁ ↦ x₂ → x₂ ↦ x₃ → x₁ ↦ x₃

  _∋_ : List Σ → Set (σₛ ⊔ ℓₛ)
  _∋_ s = [ inj₂ S ] ↦ map inj₁ s

_∈_ : List Σ → Grammar → Set (σₛ ⊔ ℓₛ)
s ∈ g = g ∋ s

_∉_ : List Σ → Grammar → Set (σₛ ⊔ ℓₛ)
s ∉ g = ¬ (s ∈ g)

_⊆_ : Grammar → Grammar → Set (σₛ ⊔ ℓₛ)
g₁ ⊆ g₂ = ∀ s → s ∈ g₁ → s ∈ g₂

_≃_ : Grammar → Grammar → Set (σₛ ⊔ ℓₛ)
g₁ ≃ g₂ = g₁ ⊆ g₂ × g₂ ⊆ g₁

module _ {N : ℕ} where
  private
    ΣN-setoid = ⊎-setoid Σₛ (setoid (Fin N))
  open import Data.List.Relation.Binary.Equality.Setoid (ΣN-setoid)

  ContextSensitiveRule : Pred (List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N)) (σₛ ⊔ ℓₛ)
  ContextSensitiveRule (f , t) = ∃[ α ] ∃[ A ] ∃[ β ] ∃[ γ ] (α ++ [ inj₂ A ] ++ β ≋ f × α ++ γ ++ β ≋ t)

  ContextFreeRule : Pred (List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N)) (σₛ ⊔ ℓₛ)
  ContextFreeRule (f , t) = ∃[ A ] [ inj₂ A ] ≋ f

  LeftRegularRule : Pred (List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N)) (σₛ ⊔ ℓₛ)
  LeftRegularRule (f , t) = ContextFreeRule (f , t) × ([] ≋ t ⊎ ∃[ a ] ∃[ B ] inj₁ a ∷ inj₂ B ∷ [] ≋ t)

  ContextFreeRule⊆ContextSensitiveRule : ContextFreeRule Pred.⊆ ContextSensitiveRule
  ContextFreeRule⊆ContextSensitiveRule {f , t} (A , [A]≋f) = [] , A , [] , t , [A]≋f , (begin
    [] ++ t ++ [] ≡⟨⟩
    t ++ []       ≡⟨ ++-identityʳ t ⟩
    t             ∎)
    where
      open import Relation.Binary.Reasoning.Setoid ≋-setoid
      open import Data.List.Properties

  LeftRegularRule⊆ContextFreeRule : LeftRegularRule Pred.⊆ ContextFreeRule
  LeftRegularRule⊆ContextFreeRule = proj₁

  LeftRegularRule⊆ContextSensitiveRule : LeftRegularRule Pred.⊆ ContextSensitiveRule
  LeftRegularRule⊆ContextSensitiveRule = ContextFreeRule⊆ContextSensitiveRule ∘ LeftRegularRule⊆ContextFreeRule

ContextSensitive′ : Pred Grammar (σₛ ⊔ ℓₛ)
ContextSensitive′ g = All ContextSensitiveRule (Grammar.P g)

ContextFree′ : Pred Grammar (σₛ ⊔ ℓₛ)
ContextFree′ g = All ContextFreeRule (Grammar.P g)

LeftRegular′ : Pred Grammar (σₛ ⊔ ℓₛ)
LeftRegular′ g = All LeftRegularRule (Grammar.P g)

ContextSensitive : Pred Grammar (σₛ ⊔ ℓₛ)
ContextSensitive g = ∃[ g′ ] (g ≃ g′ × ContextSensitive′ g′)

ContextFree : Pred Grammar (σₛ ⊔ ℓₛ)
ContextFree g = ∃[ g′ ] (g ≃ g′ × ContextFree′ g′)

Regular : Pred Grammar (σₛ ⊔ ℓₛ)
Regular g = ∃[ g′ ] (g ≃ g′ × LeftRegular′ g′)

Regular⊆ContextFree : Regular Pred.⊆ ContextFree
Regular⊆ContextFree {g} (g′ , g≃g′ , all[lrr]) = g′ , g≃g′ , All.map LeftRegularRule⊆ContextFreeRule all[lrr]

ContextFree⊆ContextSensitive : ContextFree Pred.⊆ ContextSensitive
ContextFree⊆ContextSensitive {g} (g′ , g≃g′ , all[cfr]) = g′ , g≃g′ , All.map ContextFreeRule⊆ContextSensitiveRule all[cfr]

Regular⊆ContextSensitive : Regular Pred.⊆ ContextSensitive
Regular⊆ContextSensitive = ContextFree⊆ContextSensitive ∘ Regular⊆ContextFree

