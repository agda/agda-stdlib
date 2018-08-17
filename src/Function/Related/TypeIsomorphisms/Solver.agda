------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solver for equations over product and sum types
--
-- See examples at the bottom of the file for how to use this solver
------------------------------------------------------------------------

module Function.Related.TypeIsomorphisms.Solver where

open import Algebra using (CommutativeSemiring)
import Algebra.Operations.Semiring as SemiringOperations
import Algebra.Solver.Ring.NaturalCoefficients
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc; _≟_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Level using (Level; Lift; lift; lower)
open import Function using (id; _$_; const)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; Equivalence)
open import Function.Inverse as Inv using (_↔_; Inverse; inverse)
open import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable as Decidable using (True)

------------------------------------------------------------------------
-- A decision procedure used by the solver below.

private

  coefficient-dec :
    ∀ s ℓ →
    let open CommutativeSemiring (×-⊎-commutativeSemiring s ℓ)
        open SemiringOperations semiring renaming (_×_ to Times)
    in

    ∀ m n → Dec (Times m 1# ∼[ ⌊ s ⌋ ] Times n 1#)

  coefficient-dec equivalence ℓ m n with m | n
  ... | zero  | zero  = yes (Eq.equivalence id id)
  ... | zero  | suc _ = no  (λ eq → lower (Equivalence.from eq ⟨$⟩ inj₁ _))
  ... | suc _ | zero  = no  (λ eq → lower (Equivalence.to   eq ⟨$⟩ inj₁ _))
  ... | suc _ | suc _ = yes (Eq.equivalence (λ _ → inj₁ _) (λ _ → inj₁ _))
  coefficient-dec bijection ℓ m n = Decidable.map′ to (from m n) (m ≟ n)
    where
    open CommutativeSemiring (×-⊎-commutativeSemiring bijection ℓ)
      using (1#; semiring)
    open SemiringOperations semiring renaming (_×_ to Times)

    to : ∀ {m n} → m ≡ n → Times m 1# ↔ Times n 1#
    to {m} P.refl = K-refl

    from : ∀ m n → Times m 1# ↔ Times n 1# → m ≡ n
    from zero    zero    _   = P.refl
    from zero    (suc n) 0↔+ = ⊥-elim $ lower $ Inverse.from 0↔+ ⟨$⟩ inj₁ _
    from (suc m) zero    +↔0 = ⊥-elim $ lower $ Inverse.to   +↔0 ⟨$⟩ inj₁ _
    from (suc m) (suc n) +↔+ = P.cong suc $ from m n (pred↔pred +↔+)
      where
      open P.≡-Reasoning

      ↑⊤ : Set ℓ
      ↑⊤ = Lift ℓ ⊤

      inj₁≢inj₂ : ∀ {A : Set ℓ} {x : ↑⊤ ⊎ A} {y} →
                  x ≡ inj₂ y → x ≡ inj₁ (lift tt) → ⊥
      inj₁≢inj₂ {x = x} {y} eq₁ eq₂ =
        P.subst [ const ⊥ , const ⊤ ] (begin
          inj₂ y  ≡⟨ P.sym eq₁ ⟩
          x       ≡⟨ eq₂ ⟩
          inj₁ _  ∎)
          _

      g′ : {A B : Set ℓ}
           (f : (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B)) (x : A) (y z : ↑⊤ ⊎ B) →
           Inverse.to f ⟨$⟩ inj₂ x ≡ y →
           Inverse.to f ⟨$⟩ inj₁ _ ≡ z →
           B
      g′ _ _ (inj₂ y)       _  _   _   = y
      g′ _ _ (inj₁ _) (inj₂ z) _   _   = z
      g′ f _ (inj₁ _) (inj₁ _) eq₁ eq₂ = ⊥-elim $
        inj₁≢inj₂ (Inverse.to-from f eq₁) (Inverse.to-from f eq₂)

      g : {A B : Set ℓ} → (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B) → A → B
      g f x = g′ f x _ _ P.refl P.refl

      g′∘g′ : ∀ {A B} (f : (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B))
              x y₁ z₁ y₂ z₂ eq₁₁ eq₂₁ eq₁₂ eq₂₂ →
              g′ (reverse f) (g′ f x y₁ z₁ eq₁₁ eq₂₁) y₂ z₂ eq₁₂ eq₂₂ ≡
              x
      g′∘g′ f x (inj₂ y₁) _ (inj₂ y₂) _ eq₁₁ _ eq₁₂ _ =
        P.cong [ const y₂ , id ] (begin
          inj₂ y₂                     ≡⟨ P.sym eq₁₂ ⟩
          Inverse.from f ⟨$⟩ inj₂ y₁  ≡⟨ Inverse.to-from f eq₁₁ ⟩
          inj₂ x                      ∎)
      g′∘g′ f x (inj₁ _) (inj₂ _) (inj₁ _) (inj₂ z₂) eq₁₁ _ _ eq₂₂ =
        P.cong [ const z₂ , id ] (begin
          inj₂ z₂                    ≡⟨ P.sym eq₂₂ ⟩
          Inverse.from f ⟨$⟩ inj₁ _  ≡⟨ Inverse.to-from f eq₁₁ ⟩
          inj₂ x                     ∎)
      g′∘g′ f _ (inj₂ y₁) _ (inj₁ _) _ eq₁₁ _ eq₁₂ _ =
        ⊥-elim $ inj₁≢inj₂ (Inverse.to-from f eq₁₁) eq₁₂
      g′∘g′ f _ (inj₁ _) (inj₂ z₁) (inj₂ y₂) _ _ eq₂₁ eq₁₂ _ =
        ⊥-elim $ inj₁≢inj₂ eq₁₂ (Inverse.to-from f eq₂₁)
      g′∘g′ f _ (inj₁ _) (inj₂ _) (inj₁ _) (inj₁ _) eq₁₁ _ _ eq₂₂ =
        ⊥-elim $ inj₁≢inj₂ (Inverse.to-from f eq₁₁) eq₂₂
      g′∘g′ f _ (inj₁ _) (inj₁ _) _ _ eq₁₁ eq₂₁ _ _ =
        ⊥-elim $ inj₁≢inj₂ (Inverse.to-from f eq₁₁)
                           (Inverse.to-from f eq₂₁)

      g∘g : ∀ {A B} (f : (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B)) x →
            g (reverse f) (g f x) ≡ x
      g∘g f x = g′∘g′ f x _ _ _ _ P.refl P.refl P.refl P.refl

      pred↔pred : {A B : Set ℓ} → (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B) → A ↔ B
      pred↔pred X⊎↔X⊎ = inverse (g X⊎↔X⊎) (g (reverse X⊎↔X⊎))
                                (g∘g X⊎↔X⊎) (g∘g (reverse X⊎↔X⊎))

------------------------------------------------------------------------
-- The solver

module ×-⊎-Solver (k : Symmetric-kind) {ℓ} =
  Algebra.Solver.Ring.NaturalCoefficients
    (×-⊎-commutativeSemiring k ℓ)
    (coefficient-dec k ℓ)

------------------------------------------------------------------------
-- Tests

private

  -- A test of the solver above.

  test : {ℓ : Level} (A B C : Set ℓ) →
         (Lift ℓ ⊤ × A × (B ⊎ C)) ↔ (A × B ⊎ C × (Lift ℓ ⊥ ⊎ A))
  test = solve 3 (λ A B C → con 1 :* (A :* (B :+ C)) :=
                            A :* B :+ C :* (con 0 :+ A))
                 Inv.id
    where open ×-⊎-Solver bijection
