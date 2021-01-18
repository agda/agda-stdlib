open import Data.Fin as F
open import Data.Product as Σ using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Definitions

open import Relation.Binary.PropositionalEquality as ≡

open import Relation.Binary.Bundles

module Text.Language.Regular.NFA {σₛ ℓₛ} (Σₛ : Setoid σₛ ℓₛ) where

open Setoid Σₛ renaming (Carrier to Σ; sym to ≈-sym) hiding (refl)

open import Data.Bool using (true; false)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Data.Fin.Properties as F
open import Data.List.Base
import Data.List.Membership.Propositional as L
import Data.List.Membership.Propositional.Properties as L
import Data.List.Properties as L
import Data.Vec as V
import Data.Vec.Relation.Unary.All as VAll
open import Data.List.Relation.Binary.Equality.Setoid (Σₛ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit

open import Level using (_⊔_) renaming (suc to lsuc)

open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary using (Pred)
import Relation.Nullary.Decidable as Dec

data NFAε : Set where
  with-ε : NFAε
  without-ε : NFAε

ε′ :  NFAε → Set
ε′ with-ε = ⊤
ε′ without-ε = ⊥

record NFA (E : NFAε) : Set (σₛ ⊔ ℓₛ) where
  field
    Q : ℕ
    Δ : Fin Q → ε′ E ⊎ Σ → List (Fin Q)
    Δ-cong : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δ q₁ (inj₂ σ₁) → q₂ L.∈ Δ q₁ (inj₂ σ₂)
    q₀ : Fin Q
    F : List (Fin Q)
  ε = ε′ E

data _⊢_↦ε_ : ∀ {E} → (nfa : NFA E) → Fin (NFA.Q nfa) → Fin (NFA.Q nfa) → Set (σₛ ⊔ ℓₛ) where
  [] : ∀ {E} {nfa : NFA E} {q} → nfa ⊢ q ↦ε q
  _∷_ : {nfa : NFA with-ε} → ∀ {q₁ q₂ q₃} → q₂ L.∈ NFA.Δ nfa q₁ (inj₁ tt) → nfa ⊢ q₂ ↦ε q₃ → nfa ⊢ q₁ ↦ε q₃

data _⊢_↦_ : ∀ {E} → (nfa : NFA E) → Fin (NFA.Q nfa) × List Σ → Fin (NFA.Q nfa) → Set (σₛ ⊔ ℓₛ) where
  _∷[] : ∀ {E} {nfa : NFA E} {q₁ q₂} → nfa ⊢ q₁ ↦ε q₂ → nfa ⊢ (q₁ , []) ↦ q₂
  _↦_∷_ : ∀ {E} {nfa : NFA E} {q₁ q₂ q₃ q₄ σ σs}
        → nfa ⊢ q₁ ↦ε q₂
        → q₃ L.∈ NFA.Δ nfa q₂ (inj₂ σ)
        → nfa ⊢ (q₃ , σs) ↦ q₄
        → nfa ⊢ (q₁ , σ ∷ σs) ↦ q₄

_∈_ : ∀ {E} → List Σ → NFA E → Set (σₛ ⊔ ℓₛ)
σs ∈ nfa = ∃[ q ] q L.∈ NFA.F nfa × nfa ⊢ (NFA.q₀ nfa , σs) ↦ q

_∉_ : ∀ {E} → List Σ → NFA E → Set (σₛ ⊔ ℓₛ)
σs ∉ nfa = ¬ (σs ∈ nfa)

_∋_ : ∀ {E} → NFA E → List Σ → Set (σₛ ⊔ ℓₛ)
nfa ∋ σs = σs ∈ nfa

_∌_ : ∀ {E} → NFA E → List Σ → Set (σₛ ⊔ ℓₛ)
nfa ∌ σs = ¬ (σs ∈ nfa)

_⊆_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊆ b = ∀ {σs} → σs ∈ a → σs ∈ b

_⊈_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊈ b = ¬ (a ⊆ b)

_⊇_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊇ b = b ⊆ a

_⊉_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊉ b = ¬ (b ⊆ a)

_≃_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ≃ b = a ⊆ b × b ⊆ a

_⊂_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊂ b = a ⊆ b × b ⊈ a

_⊄_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊄ b = ¬ (a ⊂ b)

_⊃_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊃ b = b ⊂ a

_⊅_ : ∀ {E₁ E₂} → NFA E₁ → NFA E₂ → Set (σₛ ⊔ ℓₛ)
a ⊅ b = b ⊄ a

module εClosure (nfa : NFA with-ε) where
  open NFA nfa
  import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD

  P : Fin Q → V.Vec (List (Fin Q)) Q → Fin Q → Set _
  P q₁ r q₂ = ¬ (q₂ L.∈ r′) where
    r′ = V.lookup r q₁

  P? : ∀ q₁ r q₂ → Dec (P q₁ r q₂)
  P? q₁ r q₂ = ¬? (q₂ LD.∈? r′) where
    r′ = V.lookup r q₁

  wfi-aux : V.Vec (List (Fin Q)) Q → Fin Q → List (Fin Q)
  wfi-aux wfi-rec q₁ = wfi-rec[q₁] ++ deduplicate F._≟_ (filter (P? q₁ wfi-rec) add) where
    wfi-rec[q₁] = V.lookup wfi-rec q₁
    add = concatMap (V.lookup wfi-rec) (Δ q₁ (inj₁ tt))

  wfi : ℕ → V.Vec (List (Fin Q)) Q
  wfi ℕ.zero = V.tabulate (_∷ [])
  wfi (ℕ.suc n) = V.tabulate (wfi-aux wfi-rec) where
    wfi-rec = wfi n

ε-closure : ∀ {E} → (nfa : NFA E) → V.Vec (List (Fin (NFA.Q nfa))) (NFA.Q nfa)
ε-closure {without-ε} nfa = V.tabulate (_∷ [])
ε-closure {with-ε} nfa@record {Q = ℕ.suc Q-1 } = εClosure.wfi nfa Q-1

toWith-ε : NFA without-ε → NFA with-ε
toWith-ε nfa =
  record
  { Q = Q
  ; Δ = Δε
  ; Δ-cong = Δ-cong
  ; q₀ = q₀
  ; F = F
  } where
    open NFA nfa
    Δε : Fin Q → ⊤ ⊎ Σ → List (Fin Q)
    Δε _ (inj₁ tt) = []
    Δε q (inj₂ σ)  = Δ q (inj₂ σ)

toWithout-ε : NFA with-ε → NFA without-ε
toWithout-ε nfa =
  record
  { Q = Q
  ; Δ = Δε
  ; Δ-cong = Δε-cong
  ; q₀ = q₀
  ; F = Fε
  } where
    open NFA nfa
    import Data.List.Relation.Unary.Any as LA
    import Data.List.Relation.Unary.Any.Properties as Any
    import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD
    open import Function.Base using (id; flip; _∘_)

    ε-cl = ε-closure nfa

    Δε : Fin Q → ⊥ ⊎ Σ → List (Fin Q)
    Δε q₁ (inj₂ σ) = deduplicate F._≟_ (concatMap (λ qₘ → Δ qₘ (inj₂ σ)) (V.lookup ε-cl q₁))

    Δε-cong : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δε q₁ (inj₂ σ₁) → q₂ L.∈ Δε q₁ (inj₂ σ₂)
    Δε-cong q₁ {q₂} {σ₁} {σ₂} σ₁≈σ₂ q₂∈Δ[q₁,σ₁] with L.find (Any.concatMap⁻ {f = λ qₘ → Δ qₘ (inj₂ σ₁)} (V.lookup ε-cl q₁) (Any.deduplicate⁻ F._≟_ q₂∈Δ[q₁,σ₁]))
    ... | qₘ , qₘ∈ε[q₁] , q₂∈Δ[qₘ,σ₁] = Any.deduplicate⁺ F._≟_ lemma (Any.concatMap⁺ (L.lose qₘ∈ε[q₁] (Δ-cong _ σ₁≈σ₂ q₂∈Δ[qₘ,σ₁]))) where
      lemma : _≡_ q₂ Respects flip _≡_
      lemma refl refl = refl

    Fε : List (Fin Q)
    Fε = filter (λ q₁ → LA.any? (λ q₂ → q₂ LD.∈? V.lookup ε-cl q₁) F) (tabulate id)

∅ : ∀ {E} → NFA E
∅ = record
  { Q = 1
  ; Δ = λ _ _ → []
  ; Δ-cong = λ {_ _ ()}
  ; q₀ = zero
  ; F = []
  }

ε : ∀ {E} → NFA E
ε = record
  { Q = 1
  ; Δ = λ _ _ → []
  ; Δ-cong = λ {_ _ ()}
  ; q₀ = zero
  ; F = zero ∷ []
  }

_⊕_ : ∀ {E} → NFA E → NFA E → NFA E
l ⊕ r = aux l r where
  app : NFA with-ε → NFA with-ε → NFA with-ε
  app l r = record
    { Q = Q₁ ℕ.+ Q₂
    ; Δ = Δ⊕ ∘ F.splitAt Q₁
    ; Δ-cong = Δ⊕-cong′
    ; q₀ = join _ _ (inj₁ q₀)
    ; F = map (join _ _ ∘ inj₂) F₂
    } where
      open NFA l using (q₀) renaming (Q to Q₁; Δ to Δ₁; Δ-cong to Δ₁-cong; F to F₁)
      open NFA r using () renaming (Q to Q₂; Δ to Δ₂; Δ-cong to Δ₂-cong; F to F₂; q₀ to q₂)
      import Data.List.Membership.DecPropositional (F._≟_ {Q₁}) as LD
      open import Function.Base using (id; flip; _∘_; _$_)

      Δ⊕ : Fin Q₁ ⊎ Fin Q₂ → ⊤ ⊎ Σ → List (Fin (Q₁ ℕ.+ Q₂))
      Δ⊕ (inj₁ q₁) (inj₁ tt) with q₁ LD.∈? F₁
      ... | yes _ = map (join _ _ ∘ inj₁) (Δ₁ q₁ $ inj₁ tt)
      ... | no  _ = (join _ _ (inj₂ q₂)) ∷ (map (join _ _ ∘ inj₁) (Δ₁ q₁ $ inj₁ tt))
      Δ⊕ (inj₁ q₁) (inj₂ σ) = map (join _ _ ∘ inj₁) (Δ₁ q₁ $ inj₂ σ)
      Δ⊕ (inj₂ q₁) σ = map (join _ _ ∘ inj₂) (Δ₂ q₁ σ)

      Δ⊕-cong : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δ⊕ q₁ (inj₂ σ₁) → q₂ L.∈ Δ⊕ q₁ (inj₂ σ₂)
      Δ⊕-cong (inj₁ q₁) σ₁≈σ₂ q₂∈Δ⊕[q₁,σ₁] with L.∈-map⁻ (join _ _ ∘ inj₁) q₂∈Δ⊕[q₁,σ₁]
      ... | _ , q₂∈Δ₁[q₁,σ₁] , refl = L.∈-map⁺ (join _ _ ∘ inj₁) (Δ₁-cong _ σ₁≈σ₂ q₂∈Δ₁[q₁,σ₁])
      Δ⊕-cong (inj₂ q₁) σ₁≈σ₂ q₂∈Δ⊕[q₁,σ₁] with L.∈-map⁻ (join _ _ ∘ inj₂) q₂∈Δ⊕[q₁,σ₁]
      ... | _ , q₂∈Δ₂[q₁,σ₁] , refl = L.∈-map⁺ (join _ _ ∘ inj₂) (Δ₂-cong _ σ₁≈σ₂ q₂∈Δ₂[q₁,σ₁])

      Δ⊕-cong′ : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δ⊕ (F.splitAt Q₁ q₁) (inj₂ σ₁) → q₂ L.∈ Δ⊕ (F.splitAt Q₁ q₁) (inj₂ σ₂)
      Δ⊕-cong′ q₁ {q₂} σ₁≈σ₂ q₂∈Δ⊕[q₁,σ₁] = Δ⊕-cong (F.splitAt Q₁ q₁) σ₁≈σ₂ q₂∈Δ⊕[q₁,σ₁]

  aux : ∀ {E} → NFA E → NFA E → NFA E
  aux {with-ε} l r = app l r
  aux {without-ε} l r = toWithout-ε (app (toWith-ε l) (toWith-ε r))

_∣_ : ∀ {E} → NFA E → NFA E → NFA E
l ∣ r = aux′ l r where
  aux : NFA with-ε → NFA with-ε → NFA with-ε
  aux l r = record
    { Q = ℕ.suc (Qₗ ℕ.+ Qᵣ)
    ; Δ = Δ∣
    ; Δ-cong = Δ∣-cong
    ; q₀ = F.zero
    ; F = map (suc ∘ join _ _ ∘ inj₁) Fₗ ++ map (suc ∘ join _ _ ∘ inj₂) Fᵣ
    } where
      open NFA l using () renaming (Q to Qₗ; Δ to Δₗ; Δ-cong to Δₗ-cong; F to Fₗ; q₀ to qₗ)
      open NFA r using () renaming (Q to Qᵣ; Δ to Δᵣ; Δ-cong to Δᵣ-cong; F to Fᵣ; q₀ to qᵣ)
      open import Function.Base using (id; flip; _∘_; _$_)

      Δ∣ : Fin (ℕ.suc (Qₗ ℕ.+ Qᵣ)) → ⊤ ⊎ Σ → List (Fin (ℕ.suc $ Qₗ ℕ.+ Qᵣ))
      Δ∣ zero (inj₁ tt) = map (suc ∘ join Qₗ Qᵣ) $ inj₁ qₗ ∷ inj₂ qᵣ ∷ []
      Δ∣ zero (inj₂ _) = []
      Δ∣ (suc s) σ with F.splitAt Qₗ s
      ... | inj₁ q₁ = map (suc ∘ join _ _ ∘ inj₁) (Δₗ q₁ σ)
      ... | inj₂ q₁ = map (suc ∘ join _ _ ∘ inj₂) (Δᵣ q₁ σ)

      Δ∣-cong : ∀ q₁ {q₂ : Fin (ℕ.suc (Qₗ ℕ.+ Qᵣ))} {σ₁ σ₂ : Σ} → σ₁ ≈ σ₂ → q₂ L.∈ Δ∣ q₁ (inj₂ σ₁) → q₂ L.∈ Δ∣ q₁ (inj₂ σ₂)
      Δ∣-cong (suc q₁) σ₁≈σ₂ q₂∈Δ∣[q₁,σ₁] with F.splitAt Qₗ q₁
      Δ∣-cong (suc q₁) σ₁≈σ₂ q₂∈Δ∣[q₁,σ₁] | inj₁ q₁′ with L.∈-map⁻ (suc ∘ join _ _ ∘ inj₁) q₂∈Δ∣[q₁,σ₁]
      ... | _ , q₂∈Δₗ[q₁′,σ₁] , refl = L.∈-map⁺ (suc ∘ join _ _ ∘ inj₁) (Δₗ-cong _ σ₁≈σ₂ q₂∈Δₗ[q₁′,σ₁])
      Δ∣-cong (suc q₁) σ₁≈σ₂ q₂∈Δ∣[q₁,σ₁] | inj₂ q₁′ with L.∈-map⁻ (suc ∘ join _ _ ∘ inj₂) q₂∈Δ∣[q₁,σ₁]
      ... | _ , q₂∈Δᵣ[q₁′,σ₁] , refl = L.∈-map⁺ (suc ∘ join _ _ ∘ inj₂) (Δᵣ-cong _ σ₁≈σ₂ q₂∈Δᵣ[q₁′,σ₁])


  aux′ : ∀ {E} → NFA E → NFA E → NFA E
  aux′ {with-ε} l r = aux l r
  aux′ {without-ε} l r = toWithout-ε (aux (toWith-ε l) (toWith-ε r))

_⋆ : ∀ {E} → NFA E → NFA E
_⋆ = aux′ where
  open import Function.Base using (id; flip; _∘_; _$_)

  aux : NFA with-ε → NFA with-ε
  aux nfa = record
    { Q = Q
    ; Δ = Δ⋆
    ; Δ-cong = Δ-cong
    ; q₀ = q₀
    ; F = F
    } where
      open NFA nfa
      import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD

      Δ⋆ : Fin Q → ⊤ ⊎ Σ → List (Fin Q)
      Δ⋆ q₁ (inj₁ tt) with q₁ LD.∈? F
      ... | yes _ = q₀ ∷ Δ q₁ (inj₁ tt)
      ... | no  _ = Δ q₁ (inj₁ tt)
      Δ⋆ q₁ (inj₂ σ) = Δ q₁ (inj₂ σ)

  aux′ : ∀ {E} → NFA E → NFA E
  aux′ {with-ε} = aux
  aux′ {without-ε} = toWithout-ε ∘ aux ∘ toWith-ε

_ʳ : ∀ {E} → NFA E → NFA E
_ʳ = aux′ where
  open import Function.Base using (id; flip; _∘_; _$_)

  aux : NFA with-ε → NFA with-ε
  aux nfa = record
    { Q = ℕ.suc Q
    ; Δ = Δʳ
    ; Δ-cong = Δʳ-cong
    ; q₀ = zero
    ; F = suc q₀ ∷ []
    } where
      open NFA nfa
      import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD

      ∈Δʳ? = λ q₁ σ q₂ → q₁ LD.∈? Δ q₂ σ

      Δʳ : Fin (ℕ.suc Q) → ⊤ ⊎ Σ → List (Fin (ℕ.suc Q))
      Δʳ zero (inj₁ tt) = map suc F
      Δʳ zero (inj₂ _) = []
      Δʳ (suc q₁) σ = map suc $ filter (∈Δʳ? q₁ σ) $ tabulate id

      Δʳ-cong : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δʳ q₁ (inj₂ σ₁) → q₂ L.∈ Δʳ q₁ (inj₂ σ₂)
      Δʳ-cong (suc q₁) {zero} {σ₁} {σ₂} σ₁≈σ₂ 0∈Δʳ[q₁,σ₁] = contradiction (proj₂ (proj₂ (L.∈-map⁻ suc 0∈Δʳ[q₁,σ₁]))) 0≢1+n
      Δʳ-cong (suc q₁) {suc q₂} {σ₁} {σ₂} σ₁≈σ₂ q₂∈Δʳ[q₁,σ₁] with L.∈-map⁻ suc q₂∈Δʳ[q₁,σ₁]
      ... | .q₂ , q₂∈filter[∈Δ[q₁,σ],id] , refl with L.∈-filter⁻ (∈Δʳ? q₁ (inj₂ σ₁)) {xs = tabulate id} q₂∈filter[∈Δ[q₁,σ],id]
      ... | q₂∈tabulate[id] , q₁∈Δ[q₂,σ₁] = L.∈-map⁺ suc (L.∈-filter⁺ (∈Δʳ? q₁ (inj₂ σ₂)) (L.∈-tabulate⁺ q₂) (Δ-cong _ σ₁≈σ₂ q₁∈Δ[q₂,σ₁]))

  aux′ : ∀ {E} → NFA E → NFA E
  aux′ {with-ε} = aux
  aux′ {without-ε} = toWithout-ε ∘ aux ∘ toWith-ε

_&_ : ∀ {E} → NFA E → NFA E → NFA E
l & r = aux′ l r where
  aux : NFA without-ε → NFA without-ε → NFA without-ε
  aux l r = record
    { Q = Qᵣ ℕ.* Qₗ
    ; Δ = Δ&
    ; Δ-cong = Δ&-cong
    ; q₀ = quotRem⁻¹ qₗ qᵣ
    ; F = F&
    } where
      open NFA l using () renaming (Q to Qₗ; Δ to Δₗ; Δ-cong to Δₗ-cong; F to Fₗ; q₀ to qₗ)
      open NFA r using () renaming (Q to Qᵣ; Δ to Δᵣ; Δ-cong to Δᵣ-cong; F to Fᵣ; q₀ to qᵣ)
      open import Data.Product using (uncurry)
      open import Relation.Nullary.Product using (_×-dec_)
      open import Function.Base using (id; flip; _∘_; _$_)
      import Data.List.Membership.DecPropositional (F._≟_ {Qₗ}) as LDₗ
      import Data.List.Membership.DecPropositional (F._≟_ {Qᵣ}) as LDᵣ

      Δ& : Fin (Qᵣ ℕ.* Qₗ) → ⊥ ⊎ Σ → List (Fin (Qᵣ ℕ.* Qₗ))
      Δ& q₁ σ with quotRem {Qᵣ} Qₗ q₁
      ... | qₗ , qᵣ = map (uncurry quotRem⁻¹) (cartesianProduct (Δₗ qₗ σ) (Δᵣ qᵣ σ))

      Δ&-cong : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ Δ& q₁ (inj₂ σ₁) → q₂ L.∈ Δ& q₁ (inj₂ σ₂)
      Δ&-cong q₁ {q₂} {σ₁} {σ₂} σ₁≈σ₂ q₂∈Δ&[q₁,σ₁] with quotRem {Qᵣ} Qₗ q₁
      ... | q₁ₗ , q₁ᵣ = subst (L._∈ _) (≡.sym q₂≡quotRem⁻¹[qₗ₂,qᵣ₂]) (L.∈-map⁺ (uncurry quotRem⁻¹) qₗ₂×qᵣ₂∈Δₗ[q₁ₗ,σ₂]×Δ₂[q₂ᵣ,σ₂]) where
        open Σ.Σ (L.∈-map⁻ (uncurry quotRem⁻¹) q₂∈Δ&[q₁,σ₁]) renaming (proj₁ to qₗ₂×qᵣ₂; proj₂ to qₗ₂×qᵣ₂∈Δₗ[qₗ,σ₁]×Δᵣ[qᵣ,σ₂]∧q₂≡quotRem⁻¹[qₗ₂,qᵣ₂])
        open Σ.Σ qₗ₂×qᵣ₂ renaming (proj₁ to qₗ₂; proj₂ to qᵣ₂)
        open Σ.Σ qₗ₂×qᵣ₂∈Δₗ[qₗ,σ₁]×Δᵣ[qᵣ,σ₂]∧q₂≡quotRem⁻¹[qₗ₂,qᵣ₂] renaming (proj₁ to qₗ₂×qᵣ₂∈Δₗ[qₗ,σ₁]×Δᵣ[qᵣ,σ₂]; proj₂ to q₂≡quotRem⁻¹[qₗ₂,qᵣ₂])
        open Σ.Σ (L.∈-cartesianProduct⁻ (Δₗ q₁ₗ (inj₂ σ₁)) (Δᵣ q₁ᵣ (inj₂ σ₁)) qₗ₂×qᵣ₂∈Δₗ[qₗ,σ₁]×Δᵣ[qᵣ,σ₂]) renaming (proj₁ to qₗ₂∈Δₗ[q₁ₗ,σ₁]; proj₂ to qᵣ₂∈Δ₂[q₂ᵣ,σ₁])
        qₗ₂∈Δₗ[q₁ₗ,σ₂] = Δₗ-cong _ σ₁≈σ₂ qₗ₂∈Δₗ[q₁ₗ,σ₁]
        qᵣ₂∈Δ₂[q₂ᵣ,σ₂] = Δᵣ-cong _ σ₁≈σ₂ qᵣ₂∈Δ₂[q₂ᵣ,σ₁]
        qₗ₂×qᵣ₂∈Δₗ[q₁ₗ,σ₂]×Δ₂[q₂ᵣ,σ₂] = L.∈-cartesianProduct⁺ qₗ₂∈Δₗ[q₁ₗ,σ₂] qᵣ₂∈Δ₂[q₂ᵣ,σ₂]

      F& : List (Fin (Qᵣ ℕ.* Qₗ))
      F& = map (uncurry quotRem⁻¹) (cartesianProduct Fₗ Fᵣ)

  aux′ : ∀ {E} → NFA E → NFA E → NFA E
  aux′ {without-ε} l r = aux l r
  aux′ {with-ε} l r = toWith-ε (aux (toWithout-ε l) (toWithout-ε r))

∁ : ∀ {E} → NFA E → NFA E
∁ = aux′ where
  open import Function.Base using (id; flip; _∘_; _$_)
  aux : NFA without-ε → NFA without-ε
  aux nfa@record { Q = ℕ.suc Q-1 } = record
    { Q = ℕ.suc Q
    ; Δ = ∁Δ
    ; Δ-cong = ∁Δ-cong
    ; q₀ = suc q₀
    ; F = ∁F
    } where
      open NFA nfa
      import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD
      import Data.List.Relation.Unary.Any as LA
      open import Data.List.Relation.Binary.Equality.DecSetoid (F.≡-decSetoid Q)

      ∁Δ : Fin (ℕ.suc Q) → ⊥ ⊎ Σ → List (Fin (ℕ.suc Q))
      ∁Δ zero σ = zero ∷ []
      ∁Δ (suc q₁) σ with Δ q₁ σ
      ... | [] = zero ∷ []
      ... | qs@(_ ∷ _) = map suc qs

      lemma₁ : ∀ q₁ σ → zero L.∈ ∁Δ (suc q₁) σ → Δ q₁ σ ≡ []
      lemma₁ q₁ σ 0∈∁δ[1+q₁,σ] with Δ q₁ σ
      ... | [] = refl
      ... | qs@(_ ∷ _) = contradiction (proj₂ (proj₂ (L.∈-map⁻ suc 0∈∁δ[1+q₁,σ]))) 0≢1+n

      lemma₂ : ∀ q₁ {q₂} σ → suc q₂ L.∈ ∁Δ (suc q₁) σ → q₂ L.∈ Δ q₁ σ
      lemma₂ q₁ {q₂} σ 1+q₂∈∁δ[1+q₁,σ] with Δ q₁ σ
      lemma₂ q₁ {q₂} σ (LA.here ())    | []
      lemma₂ q₁ {q₂} σ (LA.there ())   | []
      lemma₂ q₁ {q₂} σ 1+q₂∈∁δ[1+q₁,σ] | qs@(_ ∷ _) with L.∈-map⁻ suc 1+q₂∈∁δ[1+q₁,σ]
      ... | .q₂ , q₂∈qs , refl = q₂∈qs

      lemma₃ : ∀ {a b} {A : Set a} {B : Set b} (as : List A) (bs : List B) → (∀ {a} → a L.∈ as → ∃[ b ] b L.∈ bs) → bs ≡ [] → as ≡ []
      lemma₃ [] [] f bs≡[] = refl
      lemma₃ (a ∷ as) [] f refl with f (LA.here refl)
      ... | ()

      lemma₄ : ∀ q₁ {q₂} σ → q₂ L.∈ Δ q₁ σ → suc q₂ L.∈ ∁Δ (suc q₁) σ
      lemma₄ q₁ {q₂} σ q₂∈Δ[q₁,σ] with Δ q₁ σ
      ... | qs@(_ ∷ _) = L.∈-map⁺ suc q₂∈Δ[q₁,σ]

      ∁Δ-cong : ∀ q₁ {q₂ σ₁ σ₂} → σ₁ ≈ σ₂ → q₂ L.∈ ∁Δ q₁ (inj₂ σ₁) → q₂ L.∈ ∁Δ q₁ (inj₂ σ₂)
      ∁Δ-cong zero σ₁≈σ₂ (LA.here refl) = LA.here refl
      ∁Δ-cong (suc q₁) {zero} {σ₁ = σ₁} {σ₂} σ₁≈σ₂ 0∈∁Δ[1+q₁,σ₁] = 0∈∁Δ[1+q₁,σ₂] where
        Δ[q₁,σ₁]≡[] : Δ q₁ (inj₂ σ₁) ≡ []
        Δ[q₁,σ₁]≡[] = lemma₁ q₁ (inj₂ σ₁) 0∈∁Δ[1+q₁,σ₁]
        Δ[q₁,σ₂]≡[] : Δ q₁ (inj₂ σ₂) ≡ []
        Δ[q₁,σ₂]≡[] = lemma₃ (Δ q₁ (inj₂ σ₂)) (Δ q₁ (inj₂ σ₁)) (λ {qₘ} qₘ∈Δ[q₁,σ₂] → qₘ , (Δ-cong _ (≈-sym σ₁≈σ₂) qₘ∈Δ[q₁,σ₂])) Δ[q₁,σ₁]≡[]
        0∈∁Δ[1+q₁,σ₂] : zero L.∈ ∁Δ (suc q₁) (inj₂ σ₂)
        0∈∁Δ[1+q₁,σ₂] rewrite Δ[q₁,σ₂]≡[] = LA.here refl
      ∁Δ-cong (suc q₁) {suc q₂} {σ₁ = σ₁} {σ₂} σ₁≈σ₂ 1+q₂∈∁Δ[1+q₁,σ₁] = 1+q₂∈∁Δ[1+q₁,σ₂] where
        q₂∈Δ[q₁,σ₁] : q₂ L.∈ Δ q₁ (inj₂ σ₁)
        q₂∈Δ[q₁,σ₁] = lemma₂ q₁ (inj₂ σ₁) 1+q₂∈∁Δ[1+q₁,σ₁]
        q₂∈Δ[q₁,σ₂] : q₂ L.∈ Δ q₁ (inj₂ σ₂)
        q₂∈Δ[q₁,σ₂] = Δ-cong _ σ₁≈σ₂ q₂∈Δ[q₁,σ₁]
        1+q₂∈∁Δ[1+q₁,σ₂] : suc q₂ L.∈ ∁Δ (suc q₁) (inj₂ σ₂)
        1+q₂∈∁Δ[1+q₁,σ₂] = lemma₄ q₁ (inj₂ σ₂) q₂∈Δ[q₁,σ₂]
      ∁F : List (Fin (ℕ.suc Q))
      ∁F = zero ∷ (map suc $ filter (¬? ∘ (LD._∈? F)) $ tabulate id)

  aux′ : ∀ {E} → NFA E → NFA E
  aux′ {without-ε} l = aux l
  aux′ {with-ε} l = toWith-ε (aux (toWithout-ε l))
