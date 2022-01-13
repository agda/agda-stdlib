------------------------------------------------------------------------
-- The Agda standard library
--
-- Proving that Fin m ↪ Fin n implies that m ≤ n.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Injection.injection-Fin where
            
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; punchOut; pinch)
open import Data.Fin.Properties using (¬Fin0; 0≢1+n; toℕ-injective; punchOut-injective; suc-injective)
open import Data.Nat.Base as ℕ using (ℕ; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤⇒≯; <-irrefl)
open import Function.Bundles as Bundles using (_↣_; mk↣)
open import Function.Consequences using (contraInjective)
open import Function.Construct.Composition as Comp hiding (injective)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; cong; _≢_)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
      
Injective⇒≤ : {k l : ℕ} {f : Fin k → Fin l} → Injective _≡_ _≡_ f → k ≤ l
Injective⇒≤ {ℕ.zero} {l} {f} H = z≤n
Injective⇒≤ {ℕ.suc k} {ℕ.zero} {f} H = ⊥-elim (¬Fin0 (f zero))
Injective⇒≤ {ℕ.suc k} {ℕ.suc l} {f} H =
  s≤s (Injective⇒≤ (λ p →
    suc-injective (H (punchOut-injective
      ( contraInjective _≡_ _≡_ H (0≢1+n _))
      ( contraInjective _≡_ _≡_ H (0≢1+n _))
      ( p)))))

-- Any function f : ℕ → Fin k is not injective

ℕ→Fin-notInjective : {k : ℕ} (f : ℕ → Fin k) → ¬ (Injective _≡_ _≡_ f)
ℕ→Fin-notInjective f H =
  <-irrefl refl (Injective⇒≤ (Comp.injective _≡_ _≡_ _≡_ toℕ-injective H))

-- Pinch is almost injectve

pinch-injective :
  {k : ℕ} (x : Fin k) {y z : Fin (ℕ.suc k)} →
  suc x ≢ y → suc x ≢ z → pinch x y ≡ pinch x z → y ≡ z
pinch-injective _ {zero} {zero} f g p = refl
pinch-injective zero {zero} {suc z} f g p =
  ⊥-elim (g (cong suc p))
pinch-injective zero {suc y} {zero} f g p =
  ⊥-elim (f (cong suc (sym p)))
pinch-injective zero {suc y} {suc z} f g p =
  cong suc p
pinch-injective (suc x) {suc y} {suc z} f g p =
  cong
    ( suc)
    ( pinch-injective x
      ( λ q → f (cong suc q))
      ( λ q → g (cong suc q))
      ( suc-injective p))
