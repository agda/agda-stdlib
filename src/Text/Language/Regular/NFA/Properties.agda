open import Data.Fin
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Definitions

open import Relation.Binary.PropositionalEquality as ≡

open import Relation.Binary.Bundles

module Text.Language.Regular.NFA.Properties {σₛ ℓₛ} (Σₛ : Setoid σₛ ℓₛ) where

open Setoid Σₛ renaming (Carrier to Σ) hiding (refl)

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Data.Fin.Properties as F
open import Data.List.Base as List
import Data.List.Membership.Propositional as L
import Data.List.Membership.Propositional.Properties as L
import Data.List.Properties as L
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
import Data.List.Relation.Unary.All.Properties as All
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Vec.Properties as V

open import Function.Base using (id; _∘_; _$_; _on_)

open import Relation.Binary
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation
open import Relation.Unary using (Pred)

open import Text.Language.Regular.NFA Σₛ

open import Level using (_⊔_)

------------------------------------------------------------------------
-- Properties of _⊢_↦ε_
------------------------------------------------------------------------

private
  ε-length : ∀ {E} {nfa : NFA E} {q₁ q₂} → nfa ⊢ q₁ ↦ε q₂ → ℕ
  ε-length [] = 0
  ε-length (_ ∷ p) = 1 ℕ.+ ε-length p

  _++ε_ : ∀ {E} {nfa : NFA E} {q₁ q₂ q₃} → nfa ⊢ q₁ ↦ε q₂ → nfa ⊢ q₂ ↦ε q₃ → nfa ⊢ q₁ ↦ε q₃
  [] ++ε p₂ = p₂
  (x ∷ p₁) ++ε p₂ = x ∷ (p₁ ++ε p₂)

  ++ε-length : ∀ {E} {nfa : NFA E} {q₁ q₂ q₃} → (p₁ : nfa ⊢ q₁ ↦ε q₂) → (p₂ : nfa ⊢ q₂ ↦ε q₃) → ε-length p₁ ℕ.+ ε-length p₂ ≡ ε-length (p₁ ++ε p₂)
  ++ε-length [] p₂ = refl
  ++ε-length (x ∷ p₁) p₂ = cong ℕ.suc (++ε-length p₁ p₂)

  q₂∈ε-closure[q₁]⇒q₁↦εq₂ : ∀ {E} → (nfa : NFA E) → ∀ {q₁ q₂} → q₂ L.∈ V.lookup (ε-closure nfa) q₁ → nfa ⊢ q₁ ↦ε q₂
  q₂∈ε-closure[q₁]⇒q₁↦εq₂ {without-ε} nfa = aux where
    open NFA nfa

    aux : ∀ {q₁ q₂} → q₂ L.∈ V.lookup (ε-closure nfa) q₁ → nfa ⊢ q₁ ↦ε q₂
    aux {q₁} q₂∈ε-closure[q₁] with V.lookup (V.tabulate {A = List (Fin (NFA.Q nfa))} (_∷ [])) q₁ | V.lookup∘tabulate {A = List (Fin (NFA.Q nfa))} (_∷ []) q₁
    aux {q₁} (here refl) | .(q₁ ∷ []) | refl = []

  q₂∈ε-closure[q₁]⇒q₁↦εq₂ {with-ε} nfa@record {Q = ℕ.suc Q-1} = wfi′ Q-1 where
    open NFA nfa
    open εClosure nfa
    import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD

    wfi′ : (n : ℕ) → ∀ {q₁ q₂} → q₂ L.∈ V.lookup (wfi n) q₁ → nfa ⊢ q₁ ↦ε q₂
    wfi′ ℕ.zero = aux where
      aux : ∀ {q₁ q₂} → q₂ L.∈ V.lookup (wfi ℕ.zero) q₁ → nfa ⊢ q₁ ↦ε q₂
      aux {q₁} q₂∈fw[0][q₁] with V.lookup (V.tabulate {A = List (Fin Q)} (_∷ [])) q₁ | V.lookup∘tabulate {A = List (Fin Q)} (_∷ []) q₁
      aux {q₁} (here refl) | .(q₁ ∷ []) | refl = []

    wfi′ (ℕ.suc n) = aux where
      wfi′-rec = wfi′ n
      wfi-rec = wfi n
      aux : ∀ {q₁ q₂} → q₂ L.∈ V.lookup (wfi (ℕ.suc n)) q₁ → nfa ⊢ q₁ ↦ε q₂
      aux {q₁} {q₂} q₂∈fw[1+n][q₁] rewrite V.lookup∘tabulate (wfi-aux wfi-rec) q₁ with L.∈-++⁻ (V.lookup wfi-rec q₁) q₂∈fw[1+n][q₁]
      ... | inj₁ q₂∈r[q₁] = wfi′-rec q₂∈r[q₁]
      ... | inj₂ q₂∈add′ = qₘ∈Δ[q₁,ε] ∷ qₘ↦εq₂ where
        q₂∈add = proj₁ $ L.∈-filter⁻ (P? q₁ wfi-rec) (L.∈-deduplicate⁻ _≟_ _ q₂∈add′)
        any[q₂∈∘wfi-rec,Δ[q₁,ε]] = Any.concatMap⁻ (Δ q₁ (inj₁ tt)) q₂∈add
        ∃[qₘ]qₘ∈Δ[q₁,ε]×q₂∈wfi-rec[qₘ] = L.find any[q₂∈∘wfi-rec,Δ[q₁,ε]]
        qₘ = proj₁ ∃[qₘ]qₘ∈Δ[q₁,ε]×q₂∈wfi-rec[qₘ]
        qₘ∈Δ[q₁,ε] = proj₁ (proj₂ ∃[qₘ]qₘ∈Δ[q₁,ε]×q₂∈wfi-rec[qₘ])
        q₂∈wfi-rec[qₘ] = proj₂ (proj₂ ∃[qₘ]qₘ∈Δ[q₁,ε]×q₂∈wfi-rec[qₘ])
        qₘ↦εq₂ : nfa ⊢ qₘ ↦ε q₂
        qₘ↦εq₂ = wfi′-rec q₂∈wfi-rec[qₘ]
  q₁↦εq₂⇒q₂∈ε-closure[q₁] : ∀ {E} → (nfa : NFA E) → ∀ {q₁ q₂} → nfa ⊢ q₁ ↦ε q₂ → q₂ L.∈ V.lookup (ε-closure nfa) q₁
  q₁↦εq₂⇒q₂∈ε-closure[q₁] {without-ε} nfa = aux where
    open NFA nfa

    aux : ∀ {q₁ q₂} → nfa ⊢ q₁ ↦ε q₂ → q₂ L.∈ V.lookup (ε-closure nfa) q₁
    aux {q₁} [] rewrite V.lookup∘tabulate {A = List (Fin Q)} (_∷ []) q₁ = here refl

  q₁↦εq₂⇒q₂∈ε-closure[q₁] {with-ε} nfa@record {Q = ℕ.suc Q-1} = aux where
    open NFA nfa
    open εClosure nfa
    open Function.Base using (flip; _∘_)
    import Data.List.Membership.DecPropositional (F._≟_ {Q}) as L?

    wfi′ : (n : ℕ) → ∀ {q₁ q₂} → (p : nfa ⊢ q₁ ↦ε q₂) → ε-length p ℕ.≤ n → q₂ L.∈ V.lookup (wfi n) q₁
    wfi′ ℕ.zero = aux where
      aux : ∀ {q₁ q₂} → (p : nfa ⊢ q₁ ↦ε q₂) → ε-length p ℕ.≤ 0 → q₂ L.∈ V.lookup (wfi 0) q₁
      aux {q₁} {q₂} [] ℕ.z≤n rewrite V.lookup∘tabulate {A = List (Fin Q)} (_∷ []) q₁ = here refl
    wfi′ (ℕ.suc n) = aux′ where
      wfi-rec = wfi n
      wfi′-rec = wfi′ n

      aux : ∀ {q₁ q₂} → (p : nfa ⊢ q₁ ↦ε q₂) → ε-length p ℕ.≤ (ℕ.suc n) → q₂ L.∈ wfi-aux wfi-rec q₁
      aux {q₁} {q₂} p p≤1+n with ε-length p ℕ.≟ ℕ.suc n
      aux {q₁} {q₂} p p≤1+n | no p≢1+n = L.∈-++⁺ˡ $ wfi′-rec p $ ℕ.1+m≤1+n⇒m≤n $ ℕ.≤∧≢⇒< p≤1+n p≢1+n
      aux {q₁} {q₂} (_∷_ {q₂ = qₘ} qₘ∈Δ[q₁,ε] p) (ℕ.s≤s p≤n) | yes refl with q₂ L?.∈? V.lookup wfi-rec q₁
      ... | yes q₂∈wfi-rec[q₁] = L.∈-++⁺ˡ q₂∈wfi-rec[q₁]
      ... | no q₂∉wfi-rec[q₁] = L.∈-++⁺ʳ (V.lookup wfi-rec q₁) (L.∈-deduplicate⁺ F._≟_ q₂∈add) where
        lemma : (q₂ ≡_) Respects flip _≡_
        lemma refl refl = refl

        q₂∈wfi-rec[qₘ] = wfi′-rec p p≤n
        any[q₂∈∘wfi-rec,Δ[q₁,ε]] = L.lose qₘ∈Δ[q₁,ε] q₂∈wfi-rec[qₘ]
        q₂∈concatMap[wfi-rec,Δ[q₁,ε]] = Any.concatMap⁺ any[q₂∈∘wfi-rec,Δ[q₁,ε]]
        P[q₁,wfi-rec,q₂] = q₂∉wfi-rec[q₁]

        q₂∈add : q₂ L.∈ filter (P? q₁ wfi-rec) (concatMap (V.lookup wfi-rec) (Δ q₁ (inj₁ tt)))
        q₂∈add = L.∈-filter⁺ (P? q₁ wfi-rec) q₂∈concatMap[wfi-rec,Δ[q₁,ε]] P[q₁,wfi-rec,q₂]

      aux′ : ∀ {q₁ q₂} → (p : nfa ⊢ q₁ ↦ε q₂) → ε-length p ℕ.≤ (ℕ.suc n) → q₂ L.∈ V.lookup (wfi $ ℕ.suc n) q₁
      aux′ {q₁} {q₂} rewrite V.lookup∘tabulate (wfi-aux wfi-rec) q₁ = aux

    nodes : ∀ {q₁ q₂} (q₁↦εq₂ : nfa ⊢ q₁ ↦ε q₂) → Fin (ℕ.suc (ε-length q₁↦εq₂)) → Fin Q
    nodes {q₁}  q₁↦εq₂       zero   = q₁
    nodes      (_ ∷ q₁↦εq₂) (suc i) = nodes q₁↦εq₂ i

    subpath₁ : ∀ {q₁ q₂} (q₁↦εq₂ : nfa ⊢ q₁ ↦ε q₂) → (i : Fin (ℕ.suc (ε-length q₁↦εq₂))) → (let qₘ = nodes q₁↦εq₂ i) → Σ[ q₁↦εqₘ ∈ nfa ⊢ q₁ ↦ε qₘ ] ε-length q₁↦εqₘ ≡ toℕ i
    subpath₁  q₁↦εq₂                zero   = [] , refl
    subpath₁ (qₙ∈Δ[q₁,ε] ∷ qₙ↦εq₂) (suc i) with subpath₁ qₙ↦εq₂ i
    ... | qₙ↦εqₘ , ε-length[qₙ↦εqₘ]≡i = qₙ∈Δ[q₁,ε] ∷ qₙ↦εqₘ , cong ℕ.suc ε-length[qₙ↦εqₘ]≡i

    subpath₂ : ∀ {q₁ q₂} (q₁↦εq₂ : nfa ⊢ q₁ ↦ε q₂) → (i : Fin (ℕ.suc (ε-length q₁↦εq₂))) → (let qₘ = nodes q₁↦εq₂ i) → Σ[ qₘ↦εq₂ ∈ nfa ⊢ qₘ ↦ε q₂ ] ε-length qₘ↦εq₂ ≡ ε-length q₁↦εq₂ ℕ-ℕ i
    subpath₂  q₁↦εq₂                zero = q₁↦εq₂ , refl
    subpath₂ (qₙ∈Δ[q₁,ε] ∷ qₙ↦εq₂) (suc i) with subpath₂ qₙ↦εq₂ i
    ... | qₘ↦εq₂ , ε-length[qₘ↦εq₂]≡ε-length[qₙ↦εq₂]-i = qₘ↦εq₂ , ε-length[qₘ↦εq₂]≡ε-length[qₙ↦εq₂]-i

    shorten : ∀ {q₁ q₂} (q₁↦εq₂ : nfa ⊢ q₁ ↦ε q₂) → Σ[ q₁↦εq₂′ ∈ nfa ⊢ q₁ ↦ε q₂ ] ε-length q₁↦εq₂′ ℕ.≤ Q-1
    shorten {q₁} {q₂} q₁↦εq₂ = aux q₁↦εq₂ (wellFounded ε-length <-wellFounded q₁↦εq₂) where
      open import Induction.WellFounded
      open import Data.Nat.Induction
      open import Relation.Binary.Construct.On

      aux : ∀ {q₁ q₂} (q₁↦εq₂ : nfa ⊢ q₁ ↦ε q₂) → Acc (ℕ._<_ on ε-length) q₁↦εq₂ → Σ[ q₁↦εq₂′ ∈ nfa ⊢ q₁ ↦ε q₂ ] ε-length q₁↦εq₂′ ℕ.≤ Q-1
      aux {q₁} {q₂} q₁↦εq₂ (acc acc-rec) with ε-length q₁↦εq₂ ℕ.≤? Q-1
      ... | yes q₁↦εq₂≤Q-1 = q₁↦εq₂ , q₁↦εq₂≤Q-1
      ... | no  q₁↦εq₂≰Q-1 = aux q₁↦εq₂′ (acc-rec _ q₁↦εq₂′<q₁↦εq₂) where
        ∃[i]∃[j]i<j∧nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j] : ∃[ i ] ∃[ j ] i < j × nodes q₁↦εq₂ i ≡ nodes q₁↦εq₂ j
        ∃[i]∃[j]i<j∧nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j] with pigeonhole (ℕ.s≤s (ℕ.≰⇒> q₁↦εq₂≰Q-1)) (nodes q₁↦εq₂)
        ... | i , j , i≢j , nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j] with j ≤? i
        ... | yes j≤i = _ , _ , ℕ.≤∧≢⇒< j≤i (contraposition toℕ-injective (≢-sym i≢j)) , ≡.sym nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j]
        ... | no  j≰i = _ , _ , ℕ.≰⇒> j≰i , nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j]

        i = proj₁ ∃[i]∃[j]i<j∧nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j]
        j = proj₁ (proj₂ ∃[i]∃[j]i<j∧nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j])
        i<j = proj₁ (proj₂ (proj₂ ∃[i]∃[j]i<j∧nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j]))
        nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j] = proj₂ (proj₂ (proj₂ ∃[i]∃[j]i<j∧nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j]))
        qₘ = nodes q₁↦εq₂ i
        ∃[q₁↦εqₘ]q₁↦εqₘ=i = subpath₁ q₁↦εq₂ i
        q₁↦εqₘ = proj₁ ∃[q₁↦εqₘ]q₁↦εqₘ=i
        q₁↦εqₘ=i = proj₂ ∃[q₁↦εqₘ]q₁↦εqₘ=i

        ∃[qₘ↦εq₂]qₘ↦εq₂=q₁↦εq₂-j : Σ[ qₘ↦εq₂ ∈ nfa ⊢ qₘ ↦ε q₂ ] ε-length qₘ↦εq₂ ≡ ε-length q₁↦εq₂ ℕ-ℕ j
        ∃[qₘ↦εq₂]qₘ↦εq₂=q₁↦εq₂-j rewrite nodes[q₁↦εq₂,i]≡nodes[q₁↦εq₂,j] = subpath₂ q₁↦εq₂ j

        qₘ↦εq₂ = proj₁ ∃[qₘ↦εq₂]qₘ↦εq₂=q₁↦εq₂-j
        qₘ↦εq₂=q₁↦εq₂-j = proj₂ ∃[qₘ↦εq₂]qₘ↦εq₂=q₁↦εq₂-j
        q₁↦εq₂′ = q₁↦εqₘ ++ε qₘ↦εq₂
        j≤q₁↦εq₂ = ℕ.1+m≤1+n⇒m≤n $ F.toℕ<n {ℕ.suc (ε-length q₁↦εq₂)} j
        q₁↦εq₂′<q₁↦εq₂ = begin
          ℕ.suc (ε-length q₁↦εq₂′)                       ≡⟨⟩
          ℕ.suc (ε-length (q₁↦εqₘ ++ε qₘ↦εq₂))           ≡˘⟨ cong ℕ.suc $ ++ε-length q₁↦εqₘ qₘ↦εq₂ ⟩
          ℕ.suc (ε-length q₁↦εqₘ) ℕ.+ ε-length qₘ↦εq₂    ≡⟨ cong₂ ℕ._+_ (cong ℕ.suc q₁↦εqₘ=i) qₘ↦εq₂=q₁↦εq₂-j ⟩
          ℕ.suc (toℕ i) ℕ.+ (ε-length q₁↦εq₂ ℕ-ℕ j)      ≡⟨ cong (ℕ.suc (toℕ i) ℕ.+_) (nℕ-ℕi≡n∸toℕi _ j) ⟩
          ℕ.suc (toℕ i) ℕ.+ (ε-length q₁↦εq₂ ℕ.∸ toℕ j)  ≤⟨ ℕ.+-monoˡ-≤ (ε-length q₁↦εq₂ ℕ.∸ toℕ j) i<j ⟩
          toℕ j ℕ.+ (ε-length q₁↦εq₂ ℕ.∸ toℕ j)          ≡⟨ ℕ.m+[n∸m]≡n j≤q₁↦εq₂ ⟩
          ε-length q₁↦εq₂                                ∎
          where open ℕ.≤-Reasoning

    wfi′-end = wfi′ Q-1

    aux : ∀ {q₁ q₂} → nfa ⊢ q₁ ↦ε q₂ → q₂ L.∈ V.lookup (ε-closure nfa) q₁
    aux p with shorten p
    ... | p′ , p′≤Q-1 = wfi′-end p′ p′≤Q-1

_⊢_↦ε?_ : ∀ {E} → (nfa : NFA E) → (q₁ : Fin (NFA.Q nfa)) → (q₂ : Fin (NFA.Q nfa)) → Dec (nfa ⊢ q₁ ↦ε q₂)
_⊢_↦ε?_ {without-ε} nfa q₁ q₂ with q₁ F.≟ q₂
... | yes refl = yes []
... | no  q₁≢q₂ = no λ {[] → q₁≢q₂ refl}
_⊢_↦ε?_ {with-ε} nfa = aux where
  open NFA nfa
  import Data.List.Membership.DecPropositional (F._≟_ {Q}) as L?

  ε-closure′ = ε-closure nfa

  aux : (q₁ : Fin Q) → (q₂ : Fin Q) → Dec (nfa ⊢ q₁ ↦ε q₂)
  aux q₁ q₂ = Dec.map′ (q₂∈ε-closure[q₁]⇒q₁↦εq₂ nfa) (q₁↦εq₂⇒q₂∈ε-closure[q₁] nfa) (q₂ L?.∈? V.lookup ε-closure′ q₁)

------------------------------------------------------------------------
-- Properties of _⊆_ and _≃_
------------------------------------------------------------------------

⊆-refl : ∀ {E} → Reflexive (_⊆_ {E} {E})
⊆-refl = id

⊆-trans : ∀ {E₁ E₂ E₃} → Trans (_⊆_ {E₁} {E₂}) (_⊆_ {E₂} {E₃}) (_⊆_ {E₁} {E₃})
⊆-trans x⊆y y⊆z σs∈x = y⊆z (x⊆y σs∈x)

⊆-antisym : ∀ {E} → Antisymmetric (_≃_ {E} {E}) (_⊆_ {E} {E})
⊆-antisym x⊆y y⊆x = x⊆y , y⊆x

≃-refl : ∀ {E} → Reflexive (_≃_ {E} {E})
≃-refl = id , id

≃-sym : ∀ {E} → Symmetric (_≃_ {E} {E})
≃-sym (x⊆y , y⊆x) = y⊆x , x⊆y

≃-trans : ∀ {E₁ E₂ E₃} → Trans (_≃_ {E₁} {E₂}) (_≃_ {E₂} {E₃}) (_≃_ {E₁} {E₃})
≃-trans (x⊆y , y⊆x) (y⊆z , z⊆y) = ⊆-trans x⊆y y⊆z , ⊆-trans z⊆y y⊆x

⊆-reflexive : ∀ {E₁ E₂} {n₁ : NFA E₁} {n₂ : NFA E₂} → n₁ ≃ n₂ → n₁ ⊆ n₂
⊆-reflexive (n₁⊆n₂ , _) = n₁⊆n₂

------------------------------------------------------------------------
-- Structures

≃-isEquivalence : ∀ {E} → IsEquivalence (_≃_ {E} {E})
≃-isEquivalence = record
  { refl = ≃-refl
  ; sym = ≃-sym
  ; trans = ≃-trans
  }

⊆-isPreorder : ∀ {E} → IsPreorder (_≃_ {E} {E}) (_⊆_ {E} {E})
⊆-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive = ⊆-reflexive
  ; trans = ⊆-trans
  }

⊆-isPartialOrder : ∀ {E} → IsPartialOrder (_≃_ {E} {E}) (_⊆_ {E} {E})
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym = ⊆-antisym
  }

------------------------------------------------------------------------
-- Bundles

≃-setoid : ∀ E → Setoid (σₛ ⊔ ℓₛ) (σₛ ⊔ ℓₛ)
≃-setoid E = record
  { isEquivalence = ≃-isEquivalence {E}
  }

⊆-preorder : ∀ E → Preorder (σₛ ⊔ ℓₛ) (σₛ ⊔ ℓₛ) (σₛ ⊔ ℓₛ)
⊆-preorder E = record
  { isPreorder = ⊆-isPreorder {E}
  }

⊆-poset : ∀ E → Poset (σₛ ⊔ ℓₛ) (σₛ ⊔ ℓₛ) (σₛ ⊔ ℓₛ)
⊆-poset E = record
  { isPartialOrder = ⊆-isPartialOrder {E}
  }

------------------------------------------------------------------------
-- Properties of toWith-ε
------------------------------------------------------------------------

n≃toWith-ε[n] : ∀ nfa → nfa ≃ toWith-ε nfa
n≃toWith-ε[n] nfa = nfa⊆toWith-ε[nfa] , toWith-ε[nfa]⊆nfa where
  open NFA nfa
  lemma₁ : ∀ {q₁ q₂ σs} → nfa ⊢ (q₁ , σs) ↦ q₂ → toWith-ε nfa ⊢ (q₁ , σs) ↦ q₂
  lemma₁ ([] ∷[]) = [] ∷[]
  lemma₁ ([] ↦ qₘ∈Δ[q₁,σ] ∷ qₘ↦q₂) = [] ↦ qₘ∈Δ[q₁,σ] ∷ lemma₁ qₘ↦q₂
  lemma₂ : ∀ {q₁ q₂ σs} → toWith-ε nfa ⊢ (q₁ , σs) ↦ q₂ → nfa ⊢ (q₁ , σs) ↦ q₂
  lemma₂ ([] ∷[]) = [] ∷[]
  lemma₂ ([] ↦ qₘ∈Δ[q₁,σ] ∷ qₘ↦q₂) = [] ↦ qₘ∈Δ[q₁,σ] ∷ lemma₂ qₘ↦q₂
  nfa⊆toWith-ε[nfa] : nfa ⊆ toWith-ε nfa
  nfa⊆toWith-ε[nfa] (q , q∈F , q₀↦q) = q , q∈F , lemma₁ q₀↦q
  toWith-ε[nfa]⊆nfa : toWith-ε nfa ⊆ nfa
  toWith-ε[nfa]⊆nfa (q , q∈F , q₀↦q) = q , q∈F , lemma₂ q₀↦q


------------------------------------------------------------------------
-- Properties of toWithout-ε
------------------------------------------------------------------------

n≃toWithout-ε[n] : ∀ nfa → nfa ≃ toWithout-ε nfa
n≃toWithout-ε[n] nfa = nfa⊆toWithout-ε[nfa] , toWithout-ε[nfa]⊆nfa where
  open NFA nfa
  open NFA (toWithout-ε nfa) using () renaming (F to Fε; Δ to Δε)
  import Data.List.Relation.Unary.Any as LA
  import Data.List.Relation.Unary.Any.Properties as Any
  open import Function.Base using (id; _∘_)
  import Data.List.Membership.DecPropositional (F._≟_ {Q}) as LD

  ε-cl = ε-closure nfa

  lemma₁ : ∀ {q₁ q₂ σs} → q₂ L.∈ F → nfa ⊢ (q₁ , σs) ↦ q₂ → ∃[ q′₂ ] q′₂ L.∈ Fε × toWithout-ε nfa ⊢ (q₁ , σs) ↦ q′₂
  lemma₁ {q₁} {q₂} q₂∈F (q₁↦εq₂ ∷[]) = q₁ , q₁∈Fε , [] ∷[] where
    q₂∈ε-cl[q₁] = q₁↦εq₂⇒q₂∈ε-closure[q₁] nfa q₁↦εq₂
    any[∈ε-cl[q₁],F] = L.lose q₂∈F q₂∈ε-cl[q₁]
    q₁∈Fε = L.∈-filter⁺ (λ q₁ → Any.any? (LD._∈? V.lookup ε-cl q₁) F) (L.∈-tabulate⁺ q₁) any[∈ε-cl[q₁],F]
  lemma₁ {q₁} {q₂} {σ ∷ σs} q₂∈F (q₁↦εqₘ ↦ qₙ∈Δ[qₘ,σ] ∷ [qₙ,σs]↦q₂) with lemma₁ q₂∈F [qₙ,σs]↦q₂
  ... | q′₂ , q′₂∈Fε , [q₁,σs]↦q′₂ = _ , q′₂∈Fε , [] ↦ qₙ∈Δε[q₁,σ] ∷ [q₁,σs]↦q′₂ where
    any[qₙ∈∘Δσ,ε-cl[q₁]] = L.lose (q₁↦εq₂⇒q₂∈ε-closure[q₁] _ q₁↦εqₘ) qₙ∈Δ[qₘ,σ]
    qₙ∈Δε[q₁,σ] = L.∈-deduplicate⁺ _≟_ (Any.concatMap⁺ any[qₙ∈∘Δσ,ε-cl[q₁]])

  lemma₂ : ∀ {q₁ q₂ σs} → q₂ L.∈ Fε → toWithout-ε nfa ⊢ (q₁ , σs) ↦ q₂ → ∃[ q₂′ ] q₂′ L.∈ F × nfa ⊢ (q₁ , σs) ↦ q₂′
  lemma₂ {q₁} {.q₁} {[]} q₁∈Fε ([] ∷[]) with L.∈-filter⁻ (λ q₁ → LA.any? (λ q₂ → q₂ LD.∈? V.lookup ε-cl q₁) F) {xs = tabulate id} q₁∈Fε
  ... | _ , any[q₂∈∘ε-cl[q₁]] with L.find any[q₂∈∘ε-cl[q₁]]
  ... | q₂ , q₂∈F , q₂∈ε-cl[q₁] = q₂ , q₂∈F , q₂∈ε-closure[q₁]⇒q₁↦εq₂ _ q₂∈ε-cl[q₁] ∷[]
  lemma₂ {q₁} {q₂} {σ ∷ σs} q₂∈Fε (_↦_∷_ {q₃ = qₘ} [] qₘ∈Δε[q₁,σ] [qₘ,σs]↦q₂) with lemma₂ q₂∈Fε [qₘ,σs]↦q₂
  ... | q′₂ , q′₂∈Fε , [qₘ,σs]↦q′₂ = q′₂ , q′₂∈Fε , q₂∈ε-closure[q₁]⇒q₁↦εq₂ _ qₙ∈ε-cl[q₁] ↦ qₘ∈Δ[qₙ,σ] ∷ [qₘ,σs]↦q′₂ where
    qₘ∈concatMap[Δ,σ] : qₘ L.∈ concatMap (λ qₘ → Δ qₘ (inj₂ σ)) (V.lookup ε-cl q₁)
    qₘ∈concatMap[Δ,σ] = L.∈-deduplicate⁻ _≟_ (concatMap (λ qₘ → Δ qₘ (inj₂ σ)) (V.lookup ε-cl q₁)) qₘ∈Δε[q₁,σ]
    any[qₘ∈∘Δσ,ε-cl[q₁]] : Any ((qₘ L.∈_) ∘ (λ qₘ → Δ qₘ (inj₂ σ))) (V.lookup ε-cl q₁)
    any[qₘ∈∘Δσ,ε-cl[q₁]] = Any.concatMap⁻ (V.lookup ε-cl q₁) qₘ∈concatMap[Δ,σ]
    ∃[qₙ]qₙ∈ε-cl[q₁]∧qₘ∈Δ[qₙ,σ] : ∃[ qₙ ] qₙ L.∈ V.lookup ε-cl q₁ × qₘ L.∈ Δ qₙ (inj₂ σ)
    ∃[qₙ]qₙ∈ε-cl[q₁]∧qₘ∈Δ[qₙ,σ] = L.find any[qₘ∈∘Δσ,ε-cl[q₁]]
    qₙ = proj₁ ∃[qₙ]qₙ∈ε-cl[q₁]∧qₘ∈Δ[qₙ,σ]
    qₙ∈ε-cl[q₁] = proj₁ $ proj₂ $ ∃[qₙ]qₙ∈ε-cl[q₁]∧qₘ∈Δ[qₙ,σ]
    qₘ∈Δ[qₙ,σ] = proj₂ $ proj₂ $ ∃[qₙ]qₙ∈ε-cl[q₁]∧qₘ∈Δ[qₙ,σ]

  nfa⊆toWithout-ε[nfa] : nfa ⊆ toWithout-ε nfa
  nfa⊆toWithout-ε[nfa] (q , q∈F , q₀↦q) = lemma₁ q∈F q₀↦q

  toWithout-ε[nfa]⊆nfa : toWithout-ε nfa ⊆ nfa
  toWithout-ε[nfa]⊆nfa (q , q∈Fε , q₀↦q) = lemma₂ q∈Fε q₀↦q
