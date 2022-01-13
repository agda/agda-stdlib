------------------------------------------------------------------------
-- The Agda standard library
--
-- Proving that Fin m ↪ Fin n implies that m ≤ n.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Injection.injection-Fin where
            
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin; toℕ; punchOut; pinch)
open import Data.Fin.Properties as Fin using (¬Fin0; toℕ-injective; punchOut-injective)
open import Data.Nat.Base as ℕ using (ℕ; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤⇒≯)
open import Function.Base using (_∘_)
open import Function.Bundles as Bundles using (_↣_; mk↣)
open import Function.Construct.Composition as Comp
open import Function.Definitions using (Injective)
open import Level as L using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; cong; _≢_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation.Core using (contraposition)

--------------------------------------------------------------------------------
      
-- Finite types

is-nonzero-succ-Fin : {k : ℕ} {x : Fin k} → Fin.zero ≢ Fin.suc x
is-nonzero-succ-Fin ()

map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (ℕ.suc k) ↣ Fin (ℕ.suc l)) → Fin k → Fin l
map-reduce-inj-Fin f x =
  punchOut
    ( contraposition (Bundles.Injection.injective f) (is-nonzero-succ-Fin {x = x}))

is-injective-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (ℕ.suc k) ↣ Fin (ℕ.suc l)) →
  Injective _≡_ _≡_ (map-reduce-inj-Fin f)
is-injective-map-reduce-inj-Fin f {x} {y} p =
  Fin.suc-injective
    ( Bundles.Injection.injective f
      ( punchOut-injective
        ( contraposition
          ( Bundles.Injection.injective f)
          ( is-nonzero-succ-Fin))
        ( contraposition
          ( Bundles.Injection.injective f)
          ( is-nonzero-succ-Fin))
        ( p)))

reduce-inj-Fin : {k l : ℕ} → Fin (ℕ.suc k) ↣ Fin (ℕ.suc l) → Fin k ↣ Fin l
reduce-inj-Fin f = mk↣ (is-injective-map-reduce-inj-Fin f)

leq-inj-Fin : {k l : ℕ} → Fin k ↣ Fin l → k ≤ l
leq-inj-Fin {ℕ.zero} {_} f = z≤n
leq-inj-Fin {ℕ.suc k} {ℕ.zero} f =
  ⊥-elim (¬Fin0 (Bundles.Injection.f f Fin.zero))
leq-inj-Fin {ℕ.suc k} {ℕ.suc l} f =
  s≤s (leq-inj-Fin (reduce-inj-Fin f))

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → Injective _≡_ _≡_ f → k ≤ l
  leq-is-injective-Fin {k} {l} {f} H = leq-inj-Fin (mk↣ H)

-- Finally, we show that there is no injection ℕ ↣ Fin k

inj-toℕ : (k : ℕ) → Fin k ↣ ℕ
inj-toℕ k = mk↣ toℕ-injective

no-injection-ℕ-Fin : (k : ℕ) → ¬ (ℕ ↣ Fin k)
no-injection-ℕ-Fin k f =
  ≤⇒≯ ≤-refl (leq-inj-Fin (Comp.injection (inj-toℕ (ℕ.suc k)) f))

-- We also show that pinch is almost injectve

pinch-injective :
  {k : ℕ} (x : Fin k) {y z : Fin (ℕ.suc k)} →
  Fin.suc x ≢ y → Fin.suc x ≢ z → pinch x y ≡ pinch x z → y ≡ z
pinch-injective _ {Fin.zero} {Fin.zero} f g p = refl
pinch-injective Fin.zero {Fin.zero} {Fin.suc z} f g p =
  ⊥-elim (g (cong Fin.suc p))
pinch-injective Fin.zero {Fin.suc y} {Fin.zero} f g p =
  ⊥-elim (f (cong Fin.suc (sym p)))
pinch-injective Fin.zero {Fin.suc y} {Fin.suc z} f g p =
  cong Fin.suc p
pinch-injective (Fin.suc x) {Fin.suc y} {Fin.suc z} f g p =
  cong
    ( Fin.suc)
    ( pinch-injective x
      ( λ q → f (cong Fin.suc q))
      ( λ q → g (cong Fin.suc q))
      ( Fin.suc-injective p))
