open import Data.Fin
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Function.Definitions

open import Relation.Binary.PropositionalEquality as ≡ renaming (setoid to ≡-setoid)

open import Relation.Binary.Bundles

module Text.Language.Regular.DecNFA {σₛ ℓₛ} (Σₛ : DecSetoid σₛ ℓₛ) where

open DecSetoid Σₛ renaming (Carrier to Σ; _≟_ to _≈?_) hiding (refl)

import Data.Fin.Properties as F
open import Data.List
import Data.List.Membership.Propositional as L
import Data.List.Relation.Unary.Any as LA
open import Data.Sum
open import Data.Empty

open import Function.Base using (_∘_)

open import Text.Language.Regular.NFA setoid public
import Text.Language.Grammar setoid as G

open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

_⊢_↦?_ : ∀ {E} → (nfa : NFA E) → ∀ q₁×σs q₂ → Dec (nfa ⊢ q₁×σs ↦ q₂)
nfa ⊢ q₁ , σs ↦? q₂ = aux σs q₁ q₂ where
  open NFA nfa
  aux : ∀ σs q₁ q₂ → Dec (nfa ⊢ (q₁ , σs) ↦ q₂)
  aux [] q₁ q₂ = Dec.map′ _∷[] (λ { (q₁↦εq₂ ∷[]) → q₁↦εq₂}) (nfa ⊢ q₁ ↦ε? q₂)
  aux (σ ∷ σs) q₁ q₂ = Dec.map′ aff neg (F.any? (λ qₘ → (nfa ⊢ q₁ ↦ε? qₘ) ×-dec (LA.any? (λ qₙ → aux σs qₙ q₂) (Δ qₘ (inj₂ σ))))) where
    aff : ∃[ qₘ ] nfa ⊢ q₁ ↦ε qₘ × LA.Any (λ qₙ → nfa ⊢ qₙ , σs ↦ q₂) (Δ qₘ (inj₂ σ)) → nfa ⊢ q₁ , σ ∷ σs ↦ q₂
    aff (_ , q₁↦εqₘ , any[P,Δ[qₘ,σ]]) with L.find any[P,Δ[qₘ,σ]]
    ... | _ , qₙ∈Δ[qₘ,σ] , Pqₙ = q₁↦εqₘ ↦ qₙ∈Δ[qₘ,σ] ∷ Pqₙ
    neg : nfa ⊢ q₁ , σ ∷ σs ↦ q₂ → ∃[ qₘ ] nfa ⊢ q₁ ↦ε qₘ × LA.Any (λ qₙ → nfa ⊢ qₙ , σs ↦ q₂) (Δ qₘ (inj₂ σ))
    neg (q₁↦εqₘ ↦ qₙ∈Δ[qₘ,σ] ∷ Pqₙ) = _ , q₁↦εqₘ , L.lose qₙ∈Δ[qₘ,σ] Pqₙ

_∈?_ : ∀ {E} → (σs : List Σ) → (nfa : NFA E) → Dec (σs ∈ nfa)
σs ∈? nfa = Dec.map′ L.find (uncurry L.lose ∘ proj₂) (LA.any? (λ q₂ → nfa ⊢ q₀ , σs ↦? q₂) F) where
  open NFA nfa

fromGrammar : (g : G.Grammar) → G.LeftRegular′ g → NFA without-ε
fromGrammar g lr = record
  { Q = N
  ; Δ = Δ-ctor lr
  ; Δ-cong = {!!}
  ; q₀ = S
  ; F = F-ctor lr
  } where
    open G.Grammar g
    open import Data.Maybe
    open import Data.Bool using (true; false)
    open import Data.List.Relation.Binary.Pointwise
    open import Data.Sum.Relation.Binary.Pointwise
    open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
    open import Data.Product.Relation.Binary.Pointwise.NonDependent
    open import Data.List.Relation.Binary.Equality.DecSetoid (⊎-decSetoid Σₛ (F.≡-decSetoid N)) as LE
    open import Data.List.Membership.DecSetoid (×-decSetoid LE.≋-decSetoid LE.≋-decSetoid) as LS
    open import Function.Base using (id)
    Δ-aux : {r : List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N)} → G.LeftRegularRule r → Fin N → ⊥ ⊎ Σ → Maybe (Fin N)
    Δ-aux ((A , inj₂ ≡.refl ∷ []) , inj₁ [])                                   _  _        = nothing
    Δ-aux ((A , inj₂ ≡.refl ∷ []) , inj₂ (σ₁ , B , inj₁ _ ∷ inj₂ ≡.refl ∷ [])) q (inj₂ σ₂) with does (A F.≟ q ×-dec σ₁ ≈? σ₂)
    ... | false = nothing
    ... | true = just B

    Δ-ctor : {P : List (List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N))} → All G.LeftRegularRule P → Fin N → ⊥ ⊎ Σ → List (Fin N)
    Δ-ctor  []        q σ = []
    Δ-ctor (px ∷ pxs) q σ = maybe′ _∷_ id (Δ-aux px q σ) (Δ-ctor pxs q σ)

    mapMaybeΔ⁻ : ∀ {q₁ q₂ σ P} (pxs : All G.LeftRegularRule P) → q₂ L.∈ Δ-ctor pxs q₁ (inj₂ σ) → (inj₂ q₁ ∷ [] , inj₁ σ ∷ inj₂ q₂ ∷ []) LS.∈ P
    mapMaybeΔ⁻ (((A , inj₂ ≡.refl ∷ []) , inj₁ []) ∷ pxs) q₂∈Δ[pxs,q₁,σ] = LA.there (mapMaybeΔ⁻ pxs q₂∈Δ[pxs,q₁,σ])
    mapMaybeΔ⁻ {q₁} {q₂} {σ} (((A , inj₂ ≡.refl ∷ []) , inj₂ (σ₁ , B , inj₁ _ ∷ inj₂ ≡.refl ∷ [])) ∷ pxs) q₂∈Δ[pxs,q₁,σ] with does (A F.≟ q ×-dec σ₁ ≈? σ₂)

    Δ-cong : ∀ {q₁ q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δ-ctor lr q₁ (inj₂ σ₁) → q₂ L.∈ Δ-ctor lr q₁ (inj₂ σ₂)
    Δ-cong σ₁≈σ₂ q₂∈Δ[q₁,σ₁] = {!!}

    F-aux : {r : List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N)} → G.LeftRegularRule r → Maybe (Fin N)
    F-aux ((A , inj₂ ≡.refl ∷ []) , inj₁ _) = nothing
    F-aux ((A , inj₂ ≡.refl ∷ []) , inj₂ _) = just A

    F-ctor : {P : List (List (Σ ⊎ Fin N) × List (Σ ⊎ Fin N))} → All G.LeftRegularRule P → List (Fin N)
    F-ctor  []        = []
    F-ctor (px ∷ pxs) = maybe′ _∷_ id (F-aux px) (F-ctor pxs)
