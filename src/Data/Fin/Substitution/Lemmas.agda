------------------------------------------------------------------------
-- The Agda standard library
--
-- Substitution lemmas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Substitution.Lemmas where

open import Data.Fin.Substitution
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; zero; suc; lift)
open import Data.Vec.Base using (lookup; []; _∷_; map)
import Data.Vec.Properties as Vec
open import Function.Base as Fun using (_∘_; _$_; flip)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; refl; sym; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _▻_)
open ≡-Reasoning
open import Relation.Unary using (Pred)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    m n o p : ℕ

------------------------------------------------------------------------
-- A lemma which does not refer to any substitutions.

lift-commutes : ∀ k j (x : Fin (j + (k + n))) →
                lift j suc (lift j (lift k suc) x) ≡
                lift j (lift (suc k) suc) (lift j suc x)
lift-commutes k zero    x       = refl
lift-commutes k (suc j) zero    = refl
lift-commutes k (suc j) (suc x) = cong suc (lift-commutes k j x)

------------------------------------------------------------------------
-- The modules below prove a number of substitution lemmas, on the
-- assumption that the underlying substitution machinery satisfies
-- certain properties.

record Lemmas₀ (T : Pred ℕ ℓ) : Set ℓ where
  field simple : Simple T

  open Simple simple

  extensionality : {ρ₁ ρ₂ : Sub T m n} →
                   (∀ x → lookup ρ₁ x ≡ lookup ρ₂ x) → ρ₁ ≡ ρ₂
  extensionality {ρ₁ = []}      {[]}       hyp = refl
  extensionality {ρ₁ = t₁ ∷ ρ₁} { t₂ ∷ ρ₂} hyp with hyp zero
  extensionality {ρ₁ = t₁ ∷ ρ₁} {.t₁ ∷ ρ₂} hyp | refl =
    cong (_∷_ t₁) (extensionality (hyp ∘ suc))

  id-↑⋆ : ∀ {n} k → id ↑⋆ k ≡ id {k + n}
  id-↑⋆ zero    = refl
  id-↑⋆ (suc k) = begin
    (id ↑⋆ k) ↑ ≡⟨ cong _↑ (id-↑⋆ k) ⟩
    id        ↑ ∎

  lookup-map-weaken-↑⋆ : ∀ k x {ρ : Sub T m n} →
                         lookup (map weaken ρ ↑⋆ k) x ≡
                         lookup ((ρ ↑) ↑⋆ k) (lift k suc x)
  lookup-map-weaken-↑⋆ zero    x           = refl
  lookup-map-weaken-↑⋆ (suc k) zero        = refl
  lookup-map-weaken-↑⋆ (suc k) (suc x) {ρ} = begin
    lookup (map weaken (map weaken ρ ↑⋆ k)) x        ≡⟨ Vec.lookup-map x weaken (map weaken ρ ↑⋆ k) ⟩
    weaken (lookup (map weaken ρ ↑⋆ k) x)            ≡⟨ cong weaken (lookup-map-weaken-↑⋆ k x) ⟩
    weaken (lookup ((ρ ↑) ↑⋆ k) (lift k suc x))      ≡⟨ sym $ Vec.lookup-map (lift k suc x) weaken ((ρ ↑) ↑⋆ k) ⟩
    lookup (map weaken ((ρ ↑) ↑⋆ k)) (lift k suc x)  ∎

record Lemmas₁ (T : Pred ℕ ℓ) : Set ℓ where
  field lemmas₀ : Lemmas₀ T

  open Lemmas₀ lemmas₀
  open Simple simple

  field weaken-var : ∀ {n} {x : Fin n} → weaken (var x) ≡ var (suc x)

  lookup-map-weaken : ∀ x {y} {ρ : Sub T m n} →
                      lookup             ρ  x ≡ var      y →
                      lookup (map weaken ρ) x ≡ var (suc y)
  lookup-map-weaken x {y} {ρ} hyp = begin
    lookup (map weaken ρ) x  ≡⟨ Vec.lookup-map x weaken ρ ⟩
    weaken (lookup ρ x)      ≡⟨ cong weaken hyp ⟩
    weaken (var y)           ≡⟨ weaken-var ⟩
    var (suc y)              ∎

  mutual

    lookup-id : (x : Fin n) → lookup id x ≡ var x
    lookup-id zero    = refl
    lookup-id (suc x) = lookup-wk x

    lookup-wk : (x : Fin n) → lookup wk x ≡ var (suc x)
    lookup-wk x = lookup-map-weaken x {ρ = id} (lookup-id x)

  lookup-↑⋆ : (f : Fin m → Fin n) {ρ : Sub T m n} →
              (∀ x → lookup ρ x ≡ var (f x)) →
              ∀ k x → lookup (ρ ↑⋆ k) x ≡ var (lift k f x)
  lookup-↑⋆ f         hyp zero    x       = hyp x
  lookup-↑⋆ f         hyp (suc k) zero    = refl
  lookup-↑⋆ f {ρ = ρ} hyp (suc k) (suc x) =
    lookup-map-weaken x {ρ = ρ ↑⋆ k} (lookup-↑⋆ f hyp k x)

  lookup-lift-↑⋆ : (f : Fin n → Fin m) {ρ : Sub T m n} →
                   (∀ x → lookup ρ (f x) ≡ var x) →
                   ∀ k x → lookup (ρ ↑⋆ k) (lift k f x) ≡ var x
  lookup-lift-↑⋆ f         hyp zero    x       = hyp x
  lookup-lift-↑⋆ f         hyp (suc k) zero    = refl
  lookup-lift-↑⋆ f {ρ = ρ} hyp (suc k) (suc x) =
    lookup-map-weaken (lift k f x) {ρ = ρ ↑⋆ k} (lookup-lift-↑⋆ f hyp k x)

  lookup-wk-↑⋆ : ∀ k (x : Fin (k + n)) →
                 lookup (wk ↑⋆ k) x ≡ var (lift k suc x)
  lookup-wk-↑⋆ = lookup-↑⋆ suc lookup-wk

  lookup-wk-↑⋆-↑⋆ : ∀ k j (x : Fin (j + (k + n))) →
                    lookup (wk ↑⋆ k ↑⋆ j) x ≡
                    var (lift j (lift k suc) x)
  lookup-wk-↑⋆-↑⋆ k = lookup-↑⋆ (lift k suc) (lookup-wk-↑⋆ k)

  lookup-sub-↑⋆ : ∀ {t} k (x : Fin (k + n)) →
                  lookup (sub t ↑⋆ k) (lift k suc x) ≡ var x
  lookup-sub-↑⋆ = lookup-lift-↑⋆ suc lookup-id

  open Lemmas₀ lemmas₀ public

record Lemmas₂ (T : Pred ℕ ℓ) : Set ℓ where
  field
    lemmas₁     : Lemmas₁ T
    application : Application T T

  open Lemmas₁ lemmas₁

  subst : Subst T
  subst = record { simple = simple; application = application }

  open Subst subst

  field var-/ : ∀ {m n x} {ρ : Sub T m n} → var x / ρ ≡ lookup ρ x

  suc-/-sub : ∀ {x} {t : T n} → var (suc x) / sub t ≡ var x
  suc-/-sub {x = x} {t} = begin
    var (suc x) / sub t     ≡⟨ var-/ ⟩
    lookup (sub t) (suc x)  ≡⟨ refl ⟩
    lookup id x             ≡⟨ lookup-id x ⟩
    var x                   ∎

  lookup-⊙ : ∀ x {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} →
             lookup (ρ₁ ⊙ ρ₂) x ≡ lookup ρ₁ x / ρ₂
  lookup-⊙ x {ρ₁} {ρ₂} = Vec.lookup-map x (λ t → t / ρ₂) ρ₁

  lookup-⨀ : ∀ x (ρs : Subs T m n) →
             lookup (⨀ ρs) x ≡ var x /✶ ρs
  lookup-⨀ x ε                = lookup-id x
  lookup-⨀ x (ρ ◅ ε)          = sym var-/
  lookup-⨀ x (ρ ◅ (ρ′ ◅ ρs′)) = begin
    lookup (⨀ (ρ ◅ ρs)) x  ≡⟨ refl ⟩
    lookup (⨀ ρs ⊙ ρ) x    ≡⟨ lookup-⊙ x {ρ₁ = ⨀ (ρ′ ◅ ρs′)} ⟩
    lookup (⨀ ρs) x / ρ    ≡⟨ cong₂ _/_ (lookup-⨀ x (ρ′ ◅ ρs′)) refl ⟩
    var x /✶ ρs / ρ        ∎
    where ρs = ρ′ ◅ ρs′

  id-⊙ : {ρ : Sub T m n} → id ⊙ ρ ≡ ρ
  id-⊙ {ρ = ρ} = extensionality λ x → begin
    lookup (id ⊙ ρ) x  ≡⟨ lookup-⊙ x {ρ₁ = id} ⟩
    lookup  id x / ρ   ≡⟨ cong₂ _/_ (lookup-id x) refl ⟩
    var x        / ρ   ≡⟨ var-/ ⟩
    lookup ρ x         ∎

  lookup-wk-↑⋆-⊙ : ∀ k {x} {ρ : Sub T (k + suc m) n} →
                   lookup (wk ↑⋆ k ⊙ ρ) x ≡ lookup ρ (lift k suc x)
  lookup-wk-↑⋆-⊙ k {x} {ρ} = begin
    lookup (wk ↑⋆ k ⊙ ρ) x   ≡⟨ lookup-⊙ x {ρ₁ = wk ↑⋆ k} ⟩
    lookup (wk ↑⋆ k) x / ρ   ≡⟨ cong₂ _/_ (lookup-wk-↑⋆ k x) refl ⟩
    var (lift k suc x) / ρ   ≡⟨ var-/ ⟩
    lookup ρ (lift k suc x)  ∎

  wk-⊙-sub′ : ∀ {t : T n} k → wk ↑⋆ k ⊙ sub t ↑⋆ k ≡ id
  wk-⊙-sub′ {t = t} k = extensionality λ x → begin
    lookup (wk ↑⋆ k ⊙ sub t ↑⋆ k) x     ≡⟨ lookup-wk-↑⋆-⊙ k ⟩
    lookup (sub t ↑⋆ k) (lift k suc x)  ≡⟨ lookup-sub-↑⋆ k x ⟩
    var x                               ≡⟨ sym (lookup-id x) ⟩
    lookup id x                         ∎

  wk-⊙-sub : {t : T n} → wk ⊙ sub t ≡ id
  wk-⊙-sub = wk-⊙-sub′ zero

  var-/-wk-↑⋆ : ∀ {n} k (x : Fin (k + n)) →
                var x / wk ↑⋆ k ≡ var (lift k suc x)
  var-/-wk-↑⋆ k x = begin
    var x / wk ↑⋆ k     ≡⟨ var-/ ⟩
    lookup (wk ↑⋆ k) x  ≡⟨ lookup-wk-↑⋆ k x ⟩
    var (lift k suc x)  ∎

  wk-↑⋆-⊙-wk : ∀ k j →
               wk {n} ↑⋆ k ↑⋆ j ⊙ wk ↑⋆ j ≡
               wk ↑⋆ j ⊙ wk ↑⋆ suc k ↑⋆ j
  wk-↑⋆-⊙-wk k j = extensionality λ x → begin
    lookup (wk ↑⋆ k ↑⋆ j ⊙ wk ↑⋆ j) x               ≡⟨ lookup-⊙ x {ρ₁ = wk ↑⋆ k ↑⋆ j} ⟩
    lookup (wk ↑⋆ k ↑⋆ j) x / wk ↑⋆ j               ≡⟨ cong₂ _/_ (lookup-wk-↑⋆-↑⋆ k j x) refl ⟩
    var (lift j (lift k suc) x) / wk ↑⋆ j           ≡⟨ var-/-wk-↑⋆ j (lift j (lift k suc) x) ⟩
    var (lift j suc (lift j (lift k suc) x))        ≡⟨ cong var (lift-commutes k j x) ⟩
    var (lift j (lift (suc k) suc) (lift j suc x))  ≡⟨ sym (lookup-wk-↑⋆-↑⋆ (suc k) j (lift j suc x)) ⟩
    lookup (wk ↑⋆ suc k ↑⋆ j) (lift j suc x)        ≡⟨ sym var-/ ⟩
    var (lift j suc x) / wk ↑⋆ suc k ↑⋆ j           ≡⟨ cong₂ _/_ (sym (lookup-wk-↑⋆ j x)) refl ⟩
    lookup (wk ↑⋆ j) x / wk ↑⋆ suc k ↑⋆ j           ≡⟨ sym (lookup-⊙ x {ρ₁ = wk ↑⋆ j}) ⟩
    lookup (wk ↑⋆ j ⊙ wk ↑⋆ suc k ↑⋆ j) x           ∎

  open Subst   subst   public hiding (simple; application)
  open Lemmas₁ lemmas₁ public

record Lemmas₃ (T : Pred ℕ ℓ) : Set ℓ where
  field lemmas₂ : Lemmas₂ T

  open Lemmas₂ lemmas₂

  field
    /✶-↑✶ : ∀ {m n} (ρs₁ ρs₂ : Subs T m n) →
            (∀ k x → var x /✶ ρs₁ ↑✶ k ≡ var x /✶ ρs₂ ↑✶ k) →
            ∀ k t → t /✶ ρs₁ ↑✶ k ≡ t /✶ ρs₂ ↑✶ k

  /✶-↑✶′ : (ρs₁ ρs₂ : Subs T m n) →
           (∀ k → ⨀ (ρs₁ ↑✶ k) ≡ ⨀ (ρs₂ ↑✶ k)) →
           ∀ k t → t /✶ ρs₁ ↑✶ k ≡ t /✶ ρs₂ ↑✶ k
  /✶-↑✶′ ρs₁ ρs₂ hyp = /✶-↑✶ ρs₁ ρs₂ (λ k x → begin
    var x /✶ ρs₁ ↑✶ k        ≡⟨ sym (lookup-⨀ x (ρs₁ ↑✶ k)) ⟩
    lookup (⨀ (ρs₁ ↑✶ k)) x  ≡⟨ cong (flip lookup x) (hyp k) ⟩
    lookup (⨀ (ρs₂ ↑✶ k)) x  ≡⟨ lookup-⨀ x (ρs₂ ↑✶ k) ⟩
    var x /✶ ρs₂ ↑✶ k        ∎)

  id-vanishes : (t : T n) → t / id ≡ t
  id-vanishes = /✶-↑✶′ (ε ▻ id) ε id-↑⋆ zero

  ⊙-id : {ρ : Sub T m n} → ρ ⊙ id ≡ ρ
  ⊙-id {ρ = ρ} = begin
    map (λ t → t / id) ρ  ≡⟨ Vec.map-cong id-vanishes ρ ⟩
    map Fun.id         ρ  ≡⟨ Vec.map-id ρ ⟩
    ρ                     ∎

  open Lemmas₂ lemmas₂ public hiding (wk-⊙-sub′)

record Lemmas₄ (T : Pred ℕ ℓ) : Set ℓ where
  field lemmas₃ : Lemmas₃ T

  open Lemmas₃ lemmas₃

  field /-wk : ∀ {n} {t : T n} → t / wk ≡ weaken t

  private

    ↑-distrib′ : {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} →
                 (∀ t → t / ρ₂ / wk ≡ t / wk / ρ₂ ↑) →
                 (ρ₁ ⊙ ρ₂) ↑ ≡ ρ₁ ↑ ⊙ ρ₂ ↑
    ↑-distrib′ {ρ₁ = ρ₁} {ρ₂} hyp = begin
      (ρ₁ ⊙ ρ₂) ↑                             ≡⟨ refl ⟩
      var zero        ∷ map weaken (ρ₁ ⊙ ρ₂)  ≡⟨ cong₂ _∷_ (sym var-/) lemma ⟩
      var zero / ρ₂ ↑ ∷ map weaken ρ₁ ⊙ ρ₂ ↑  ≡⟨ refl ⟩
      ρ₁ ↑ ⊙ ρ₂ ↑                             ∎
      where
      lemma = begin
        map weaken (map (λ t → t / ρ₂) ρ₁)    ≡⟨ sym (Vec.map-∘ _ _ _) ⟩
        map (λ t → weaken (t / ρ₂)) ρ₁        ≡⟨ Vec.map-cong (λ t → begin
                                                   weaken (t / ρ₂)  ≡⟨ sym /-wk ⟩
                                                   t / ρ₂ / wk      ≡⟨ hyp t ⟩
                                                   t / wk / ρ₂ ↑    ≡⟨ cong₂ _/_ /-wk refl ⟩
                                                   weaken t / ρ₂ ↑  ∎) ρ₁ ⟩
        map (λ t → weaken t / ρ₂ ↑) ρ₁        ≡⟨ Vec.map-∘ _ _ _ ⟩
        map (λ t → t / ρ₂ ↑) (map weaken ρ₁)  ∎

    ↑⋆-distrib′ : {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} →
                  (∀ k t → t / ρ₂ ↑⋆ k / wk ≡ t / wk / ρ₂ ↑⋆ suc k) →
                  ∀ k → (ρ₁ ⊙ ρ₂) ↑⋆ k ≡ ρ₁ ↑⋆ k ⊙ ρ₂ ↑⋆ k
    ↑⋆-distrib′                hyp zero    = refl
    ↑⋆-distrib′ {ρ₁ = ρ₁} {ρ₂} hyp (suc k) = begin
      (ρ₁ ⊙ ρ₂) ↑⋆ suc k         ≡⟨ cong _↑ (↑⋆-distrib′ hyp k) ⟩
      (ρ₁ ↑⋆ k ⊙ ρ₂ ↑⋆ k) ↑      ≡⟨ ↑-distrib′ (hyp k) ⟩
      ρ₁ ↑⋆ suc k ⊙ ρ₂ ↑⋆ suc k  ∎

  map-weaken : {ρ : Sub T m n} → map weaken ρ ≡ ρ ⊙ wk
  map-weaken {ρ = ρ} = begin
    map weaken ρ          ≡⟨ Vec.map-cong (λ _ → sym /-wk) ρ ⟩
    map (λ t → t / wk) ρ  ≡⟨ refl ⟩
    ρ ⊙ wk                ∎

  private

    ⊙-wk′ : ∀ {ρ : Sub T m n} k →
            ρ ↑⋆ k ⊙ wk ↑⋆ k ≡ wk ↑⋆ k ⊙ ρ ↑ ↑⋆ k
    ⊙-wk′ {ρ = ρ} k = sym (begin
      wk ↑⋆ k ⊙ ρ ↑ ↑⋆ k  ≡⟨ lemma ⟩
      map weaken ρ ↑⋆ k   ≡⟨ cong (λ ρ′ → ρ′ ↑⋆ k) map-weaken ⟩
      (ρ ⊙ wk) ↑⋆ k       ≡⟨ ↑⋆-distrib′ (λ k t →
                               /✶-↑✶′ (ε ▻ wk ↑⋆ k ▻ wk) (ε ▻ wk ▻ wk ↑⋆ suc k)
                                      (wk-↑⋆-⊙-wk k) zero t) k ⟩
      ρ ↑⋆ k ⊙ wk ↑⋆ k    ∎)
      where
      lemma = extensionality λ x → begin
        lookup (wk ↑⋆ k ⊙ ρ ↑ ↑⋆ k) x     ≡⟨ lookup-wk-↑⋆-⊙ k ⟩
        lookup (ρ ↑ ↑⋆ k) (lift k suc x)  ≡⟨ sym (lookup-map-weaken-↑⋆ k x) ⟩
        lookup (map weaken ρ ↑⋆ k) x      ∎

  ⊙-wk : {ρ : Sub T m n} → ρ ⊙ wk ≡ wk ⊙ ρ ↑
  ⊙-wk = ⊙-wk′ zero

  wk-commutes : ∀ {ρ : Sub T m n} t →
                t / ρ / wk ≡ t / wk / ρ ↑
  wk-commutes {ρ = ρ} = /✶-↑✶′ (ε ▻ ρ ▻ wk) (ε ▻ wk ▻ ρ ↑) ⊙-wk′ zero

  ↑⋆-distrib : {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} →
               ∀ k → (ρ₁ ⊙ ρ₂) ↑⋆ k ≡ ρ₁ ↑⋆ k ⊙ ρ₂ ↑⋆ k
  ↑⋆-distrib = ↑⋆-distrib′ (λ _ → wk-commutes)

  /-⊙ : ∀ {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} t →
        t / ρ₁ ⊙ ρ₂ ≡ t / ρ₁ / ρ₂
  /-⊙ {ρ₁ = ρ₁} {ρ₂} t =
    /✶-↑✶′ (ε ▻ ρ₁ ⊙ ρ₂) (ε ▻ ρ₁ ▻ ρ₂) ↑⋆-distrib zero t

  ⊙-assoc : {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} {ρ₃ : Sub T o p} →
            ρ₁ ⊙ (ρ₂ ⊙ ρ₃) ≡ (ρ₁ ⊙ ρ₂) ⊙ ρ₃
  ⊙-assoc {ρ₁ = ρ₁} {ρ₂} {ρ₃} = begin
    map (λ t → t / ρ₂ ⊙ ρ₃) ρ₁                  ≡⟨ Vec.map-cong /-⊙ ρ₁ ⟩
    map (λ t → t / ρ₂ / ρ₃) ρ₁                  ≡⟨ Vec.map-∘ _ _ _ ⟩
    map (λ t → t / ρ₃) (map (λ t → t / ρ₂) ρ₁)  ∎

  map-weaken-⊙-sub : ∀ {ρ : Sub T m n} {t} → map weaken ρ ⊙ sub t ≡ ρ
  map-weaken-⊙-sub {ρ = ρ} {t} = begin
    map weaken ρ ⊙ sub t  ≡⟨ cong₂ _⊙_ map-weaken refl ⟩
    ρ ⊙ wk ⊙ sub t        ≡⟨ sym ⊙-assoc ⟩
    ρ ⊙ (wk ⊙ sub t)      ≡⟨ cong (_⊙_ ρ) wk-⊙-sub ⟩
    ρ ⊙ id                ≡⟨ ⊙-id ⟩
    ρ                     ∎

  sub-⊙ : ∀ {ρ : Sub T m n} t → sub t ⊙ ρ ≡ ρ ↑ ⊙ sub (t / ρ)
  sub-⊙ {ρ = ρ} t = begin
    sub t ⊙ ρ                           ≡⟨ refl ⟩
    t / ρ ∷ id ⊙ ρ                      ≡⟨ cong (_∷_ (t / ρ)) id-⊙ ⟩
    t / ρ ∷ ρ                           ≡⟨ cong (_∷_ (t / ρ)) (sym map-weaken-⊙-sub) ⟩
    t / ρ ∷ map weaken ρ ⊙ sub (t / ρ)  ≡⟨ cong₂ _∷_ (sym var-/) refl ⟩
    ρ ↑ ⊙ sub (t / ρ)                   ∎

  suc-/-↑ : ∀ {ρ : Sub T m n} x →
            var (suc x) / ρ ↑ ≡ var x / ρ / wk
  suc-/-↑ {ρ = ρ} x = begin
    var (suc x) / ρ ↑        ≡⟨ var-/ ⟩
    lookup (map weaken ρ) x  ≡⟨ cong (flip lookup x) (map-weaken {ρ = ρ}) ⟩
    lookup (ρ ⊙ wk)       x  ≡⟨ lookup-⊙ x {ρ₁ = ρ} ⟩
    lookup ρ x / wk          ≡⟨ cong₂ _/_ (sym var-/) refl ⟩
    var x / ρ / wk           ∎

  weaken-↑ : ∀ t {ρ : Sub T m n} → weaken t / (ρ ↑) ≡ weaken (t / ρ)
  weaken-↑ t {ρ} = begin
    weaken t / (ρ ↑) ≡⟨ cong (_/ ρ ↑) (sym /-wk) ⟩
    t / wk / ρ ↑     ≡⟨ sym (wk-commutes t) ⟩
    t / ρ / wk       ≡⟨ /-wk ⟩
    weaken (t / ρ)   ∎

  open Lemmas₃ lemmas₃ public
    hiding (/✶-↑✶; /✶-↑✶′; wk-↑⋆-⊙-wk;
            lookup-wk-↑⋆-⊙; lookup-map-weaken-↑⋆)

------------------------------------------------------------------------
-- For an example of how AppLemmas can be used, see
-- Data.Fin.Substitution.List.

record AppLemmas (T₁ : Pred ℕ ℓ₁) (T₂ : Pred ℕ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    application : Application T₁ T₂
    lemmas₄     : Lemmas₄ T₂

  open Application application using (_/_; _/✶_)
  open Lemmas₄ lemmas₄
    using (id; _⊙_; wk; weaken; sub; _↑; ⨀; /-wk) renaming (_/_ to _⊘_)

  field
    id-vanishes : ∀ {n} (t : T₁ n) → t / id ≡ t
    /-⊙         : ∀ {m n k} {ρ₁ : Sub T₂ m n} {ρ₂ : Sub T₂ n k} t →
                  t / ρ₁ ⊙ ρ₂ ≡ t / ρ₁ / ρ₂

  private module L₄ = Lemmas₄ lemmas₄

  /-⨀ : ∀ t (ρs : Subs T₂ m n) → t / ⨀ ρs ≡ t /✶ ρs
  /-⨀ t ε                = id-vanishes t
  /-⨀ t (ρ ◅ ε)          = refl
  /-⨀ t (ρ ◅ (ρ′ ◅ ρs′)) = begin
    t / ⨀ ρs ⊙ ρ  ≡⟨ /-⊙ t ⟩
    t / ⨀ ρs / ρ  ≡⟨ cong₂ _/_ (/-⨀ t (ρ′ ◅ ρs′)) refl ⟩
    t /✶ ρs / ρ   ∎
    where ρs = ρ′ ◅ ρs′

  ⨀→/✶ : (ρs₁ ρs₂ : Subs T₂ m n) →
         ⨀ ρs₁ ≡ ⨀ ρs₂ → ∀ t → t /✶ ρs₁ ≡ t /✶ ρs₂
  ⨀→/✶ ρs₁ ρs₂ hyp t = begin
    t /✶ ρs₁   ≡⟨ sym (/-⨀ t ρs₁) ⟩
    t / ⨀ ρs₁  ≡⟨ cong (_/_ t) hyp ⟩
    t / ⨀ ρs₂  ≡⟨ /-⨀ t ρs₂ ⟩
    t /✶ ρs₂   ∎

  wk-commutes : ∀ {ρ : Sub T₂ m n} t →
                t / ρ / wk ≡ t / wk / ρ ↑
  wk-commutes {ρ = ρ} = ⨀→/✶ (ε ▻ ρ ▻ wk) (ε ▻ wk ▻ ρ ↑) L₄.⊙-wk

  sub-commutes : ∀ {t′} {ρ : Sub T₂ m n} t →
                 t / sub t′ / ρ ≡ t / ρ ↑ / sub (t′ ⊘ ρ)
  sub-commutes {t′ = t′} {ρ} =
    ⨀→/✶ (ε ▻ sub t′ ▻ ρ) (ε ▻ ρ ↑ ▻ sub (t′ ⊘ ρ)) (L₄.sub-⊙ t′)

  wk-sub-vanishes : ∀ {t′} (t : T₁ n) → t / wk / sub t′ ≡ t
  wk-sub-vanishes {t′ = t′} = ⨀→/✶ (ε ▻ wk ▻ sub t′) ε L₄.wk-⊙-sub

  /-weaken : ∀ {ρ : Sub T₂ m n} t → t / map weaken ρ ≡ t / ρ / wk
  /-weaken {ρ = ρ} = ⨀→/✶ (ε ▻ map weaken ρ) (ε ▻ ρ ▻ wk) L₄.map-weaken

  open Application application public
  open L₄ public
    hiding (application; _⊙_; _/_; _/✶_;
            id-vanishes; /-⊙; wk-commutes)

record Lemmas₅ {ℓ} (T : Pred ℕ ℓ) : Set ℓ where
  field lemmas₄ : Lemmas₄ T

  private module L₄ = Lemmas₄ lemmas₄

  appLemmas : AppLemmas T T
  appLemmas = record
    { application = L₄.application
    ; lemmas₄     = lemmas₄
    ; id-vanishes = L₄.id-vanishes
    ; /-⊙         = L₄./-⊙
    }

  open AppLemmas appLemmas public hiding (lemmas₄)

------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Lemmas about variable substitutions (renamings).

module VarLemmas where

  open VarSubst

  lemmas₃ : Lemmas₃ Fin
  lemmas₃ = record
    { lemmas₂ = record
      { lemmas₁ = record
        { lemmas₀ = record
          { simple = simple
          }
        ; weaken-var = refl
        }
      ; application = application
      ; var-/       = refl
      }
    ; /✶-↑✶ = λ _ _ hyp → hyp
    }

  private module L₃ = Lemmas₃ lemmas₃

  lemmas₅ : Lemmas₅ Fin
  lemmas₅ = record
    { lemmas₄ = record
      { lemmas₃ = lemmas₃
      ; /-wk    = L₃.lookup-wk _
      }
    }

  open Lemmas₅ lemmas₅ public hiding (lemmas₃)

-- Lemmas about "term" substitutions.

record TermLemmas (T : ℕ → Set) : Set₁ where
  field
    termSubst : TermSubst T

  open TermSubst termSubst
  private module T = TermSubst termSubst

  field
    app-var : ∀ {T′} {lift : Lift T′ T} {m n x} {ρ : Sub T′ m n} →
              app lift (var x) ρ ≡ Lift.lift lift (lookup ρ x)
    /✶-↑✶   : ∀ {T₁ T₂} {lift₁ : Lift T₁ T} {lift₂ : Lift T₂ T} →
              let open Lifted lift₁
                    using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
                  open Lifted lift₂
                    using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)
              in
              ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
              (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
              ∀ k t → t /✶₁ ρs₁ ↑✶₁ k ≡ t /✶₂ ρs₂ ↑✶₂ k

  private module V = VarLemmas

  lemmas₃ : Lemmas₃ T
  lemmas₃ = record
    { lemmas₂ = record
      { lemmas₁ = record
        { lemmas₀ = record
          { simple = simple
          }
        ; weaken-var = λ {_ x} → begin
            var x /Var V.wk      ≡⟨ app-var ⟩
            var (lookup V.wk x)  ≡⟨ cong var (V.lookup-wk x) ⟩
            var (suc x)          ∎
        }
      ; application = Subst.application subst
      ; var-/       = app-var
      }
    ; /✶-↑✶ = /✶-↑✶
    }

  private module L₃ = Lemmas₃ lemmas₃

  lemmas₅ : Lemmas₅ T
  lemmas₅ = record
    { lemmas₄ = record
      { lemmas₃ = lemmas₃
      ; /-wk    = λ {_ t} → begin
          t / wk       ≡⟨ /✶-↑✶ (ε ▻ wk) (ε ▻ V.wk)
                            (λ k x → begin
                               var x / wk ↑⋆ k                 ≡⟨ L₃.var-/-wk-↑⋆ k x ⟩
                               var (lift k suc x)              ≡⟨ cong var (sym (V.var-/-wk-↑⋆ k x)) ⟩
                               var (lookup (V._↑⋆_ V.wk k) x)  ≡⟨ sym app-var ⟩
                               var x /Var V._↑⋆_ V.wk k        ∎)
                            zero t ⟩
          t /Var V.wk  ≡⟨⟩
          weaken t     ∎
      }
    }

  open Lemmas₅ lemmas₅ public hiding (lemmas₃)

  wk-⊙-∷ : (t : T n) (ρ : Sub T m n) → (T.wk T.⊙ (t ∷ ρ)) ≡ ρ
  wk-⊙-∷ t ρ = extensionality λ x → begin
    lookup (T.wk T.⊙ (t ∷ ρ)) x ≡⟨ L₃.lookup-wk-↑⋆-⊙ 0 {ρ = t ∷ ρ} ⟩
    lookup ρ x                  ∎

  weaken-∷ : (t₁ : T m) {t₂ : T n} {ρ : Sub T m n} →
    T.weaken t₁ T./ (t₂ ∷ ρ) ≡ t₁ T./ ρ
  weaken-∷ t₁ {t₂} {ρ} = begin
    T.weaken t₁ T./ (t₂ ∷ ρ)   ≡⟨ cong (T._/ (t₂ ∷ ρ)) (sym /-wk) ⟩
    (t₁ T./ T.wk) T./ (t₂ ∷ ρ) ≡⟨ ⨀→/✶ ((t₂ ∷ ρ) ◅ T.wk ◅ ε) (ρ ◅ ε) (wk-⊙-∷ t₂ ρ) t₁ ⟩
    t₁ T./ ρ                   ∎

  weaken-sub : (t₁ : T n) {t₂ : T n} → T.weaken t₁ T./ (T.sub t₂) ≡ t₁
  weaken-sub t₁ {t₂} = begin
    T.weaken t₁ T./ (T.sub t₂) ≡⟨ weaken-∷ t₁ ⟩
    t₁ T./ T.id                ≡⟨ id-vanishes t₁ ⟩
    t₁                         ∎

  -- Lemmas relating renamings to substitutions.

  map-var≡ : {ρ₁ : Sub Fin m n} {ρ₂ : Sub T m n} {f : Fin m → Fin n} →
             (∀ x → lookup ρ₁ x ≡ f x) →
             (∀ x → lookup ρ₂ x ≡ T.var (f x)) →
             map T.var ρ₁ ≡ ρ₂
  map-var≡ {ρ₁ = ρ₁} {ρ₂ = ρ₂} {f = f} hyp₁ hyp₂ = extensionality λ x →
    lookup (map T.var ρ₁) x  ≡⟨ Vec.lookup-map x _ ρ₁ ⟩
    T.var (lookup ρ₁ x)      ≡⟨ cong T.var $ hyp₁ x ⟩
    T.var (f x)              ≡⟨ sym $ hyp₂ x ⟩
    lookup ρ₂ x              ∎

  wk≡wk : map T.var VarSubst.wk ≡ T.wk {n = n}
  wk≡wk = map-var≡ VarLemmas.lookup-wk lookup-wk

  id≡id : map T.var VarSubst.id ≡ T.id {n = n}
  id≡id = map-var≡ VarLemmas.lookup-id lookup-id

  sub≡sub : {x : Fin n} → map T.var (VarSubst.sub x) ≡ T.sub (T.var x)
  sub≡sub = cong (_ ∷_) id≡id

  ↑≡↑ : {ρ : Sub Fin m n} → map T.var (ρ VarSubst.↑) ≡ map T.var ρ T.↑
  ↑≡↑ {ρ = ρ} = map-var≡
    (VarLemmas.lookup-↑⋆ (lookup ρ) (λ _ → refl) 1)
    (lookup-↑⋆ (lookup ρ) (λ _ → Vec.lookup-map _ _ ρ) 1)

  /Var≡/ : ∀ {ρ : Sub Fin m n} {t} → t /Var ρ ≡ t T./ map T.var ρ
  /Var≡/ {ρ = ρ} {t = t} =
    /✶-↑✶ (ε ▻ ρ) (ε ▻ map T.var ρ)
      (λ k x →
         T.var x /Var ρ VarSubst.↑⋆ k        ≡⟨ app-var ⟩
         T.var (lookup (ρ VarSubst.↑⋆ k) x)  ≡⟨ cong T.var $ VarLemmas.lookup-↑⋆ _ (λ _ → refl) k _ ⟩
         T.var (lift k (VarSubst._/ ρ) x)    ≡⟨ sym $ lookup-↑⋆ _ (λ _ → Vec.lookup-map _ _ ρ) k _ ⟩
         lookup (map T.var ρ T.↑⋆ k) x       ≡⟨ sym app-var ⟩
         T.var x T./ map T.var ρ T.↑⋆ k      ∎)
      zero t

  sub-renaming-commutes : ∀ {t x} {ρ : Sub T m n} →
    t /Var VarSubst.sub x T./ ρ ≡ t T./ ρ T.↑ T./ T.sub (lookup ρ x)
  sub-renaming-commutes {t = t} {x = x} {ρ = ρ} =
    t /Var VarSubst.sub x T./ ρ             ≡⟨ cong (T._/ ρ) /Var≡/ ⟩
    t T./ map T.var (VarSubst.sub x) T./ ρ  ≡⟨ cong (λ ρ′ → t T./ ρ′ T./ ρ) sub≡sub ⟩
    t T./ T.sub (T.var x) T./ ρ             ≡⟨ sub-commutes _ ⟩
    t T./ ρ T.↑ T./ T.sub (T.var x T./ ρ)   ≡⟨ cong (λ t′ → t T./ ρ T.↑ T./ T.sub t′) app-var ⟩
    t T./ ρ T.↑ T./ T.sub (lookup ρ x)      ∎

  sub-commutes-with-renaming : ∀ {t t′} {ρ : Sub Fin m n} →
    t T./ T.sub t′ /Var ρ ≡ t /Var ρ VarSubst.↑ T./ T.sub (t′ /Var ρ)
  sub-commutes-with-renaming {t = t} {t′ = t′} {ρ = ρ} =
    t T./ T.sub t′ /Var ρ                                          ≡⟨ /Var≡/ ⟩
    t T./ T.sub t′ T./ map T.var ρ                                 ≡⟨ sub-commutes _ ⟩
    t T./ map T.var ρ T.↑ T./ T.sub (t′ T./ map T.var ρ)           ≡⟨ sym $ cong (λ ρ′ → t T./ ρ′ T./ T.sub (t′ T./ map T.var ρ)) ↑≡↑ ⟩
    t T./ map T.var (ρ VarSubst.↑) T./ T.sub (t′ T./ map T.var ρ)  ≡⟨ sym $ cong₂ (λ t ρ → t T./ T.sub ρ) /Var≡/ /Var≡/ ⟩
    t /Var ρ VarSubst.↑ T./ T.sub (t′ /Var ρ)                      ∎
