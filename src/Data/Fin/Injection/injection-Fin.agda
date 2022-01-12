------------------------------------------------------------------------
-- The Agda standard library
--
-- Proving that Fin m ↪ Fin n implies that m ≤ n.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Injection.injection-Fin where
            
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ; pinch)
  renaming
    ( zero to zero-Fin;
      suc to succ-Fin)
open import Data.Fin.Properties using (¬Fin0; toℕ-injective)
  renaming
    ( suc-injective to is-injective-succ-Fin)
open import Data.Nat.Base using (ℕ; _≤_; z≤n; s≤s; _<_)
  renaming (suc to succ-ℕ; zero to zero-ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Function.Bundles using (_↣_)
open Function.Bundles.Injection using ()
  renaming
    ( f to map-inj;
      cong to cong-inj;
      injective to is-injective-map-inj)
open import Function.Definitions using (Injective)
open import Level using (Level; _⊔_)
  renaming
    ( zero to lzero;
      suc to lsuc)
open import Relation.Binary.PropositionalEquality.Core
  using
    ( _≡_; refl; sym; cong)
  renaming
    ( trans to _∙_)
open import Relation.Nullary using (¬_)

-- We declare private definitions for things that already exist in agda-stdlib

private

  module _
    {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
    where

    is-injective-comp :
      {g : B → C} {f : A → B} →
      Injective _≡_ _≡_ g → Injective _≡_ _≡_ f → Injective _≡_ _≡_ (g ∘ f)
    is-injective-comp H K p = K (H p)

    _∘i_ : B ↣ C → A ↣ B → A ↣ C
    map-inj (g ∘i f) = map-inj g ∘ map-inj f
    Function.Bundles.Injection.cong (g ∘i f) = cong-inj g ∘ cong-inj f
    is-injective-map-inj (g ∘i f) =
      is-injective-comp (is-injective-map-inj g) (is-injective-map-inj f)

-- Decidability

is-decidable : {l : Level} (A : Set l) → Set l
is-decidable A = A ⊎ (¬ A)

-- Strict inequality on ℕ

contradiction-le-ℕ : (m n : ℕ) → m < n → ¬ (n ≤ m)
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) (s≤s H) (s≤s K) = contradiction-le-ℕ m n H K

contradiction-leq-ℕ : (m n : ℕ) → m ≤ n → ¬ ((succ-ℕ n) ≤ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) (s≤s H) (s≤s K) = contradiction-leq-ℕ m n H K

neq-le-ℕ : {x y : ℕ} → x < y → ¬ (x ≡ y)
neq-le-ℕ {succ-ℕ x} {succ-ℕ .x} (s≤s H) refl = neq-le-ℕ H refl

--------------------------------------------------------------------------------
      
-- Finite types

is-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Set lzero
is-zero-Fin x = x ≡ zero-Fin

is-nonzero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Set lzero
is-nonzero-Fin x = ¬ (is-zero-Fin x)

is-nonzero-succ-Fin : {k : ℕ} {x : Fin k} → is-nonzero-Fin (succ-Fin x)
is-nonzero-succ-Fin ()

is-succ-Fin : {k : ℕ} (x : Fin k) → Set lzero
is-succ-Fin {succ-ℕ k} x = Σ (Fin k) (λ y → (succ-Fin y) ≡ x)

is-decidable-is-succ-Fin : {k : ℕ} (x : Fin k) → is-decidable (is-succ-Fin x)
is-decidable-is-succ-Fin zero-Fin = inj₂ α
  where
  α : is-succ-Fin zero-Fin → ⊥
  α (y , ())
is-decidable-is-succ-Fin (succ-Fin x) = inj₁ (x , refl)

is-zero-is-not-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → ¬ (is-succ-Fin x) → is-zero-Fin x
is-zero-is-not-succ-Fin zero-Fin H = refl
is-zero-is-not-succ-Fin (succ-Fin x) H = ⊥-elim (H (x , refl))

is-almost-injective-pinch :
  {k : ℕ} (x : Fin k) {y z : Fin (succ-ℕ k)} →
  ¬ (succ-Fin x ≡ y) → ¬ (succ-Fin x ≡ z) →
  pinch x y ≡ pinch x z → y ≡ z
is-almost-injective-pinch zero-Fin {zero-Fin} {zero-Fin} f g p =
  refl
is-almost-injective-pinch zero-Fin {zero-Fin} {succ-Fin z} f g p =
  ⊥-elim (g (cong succ-Fin p))
is-almost-injective-pinch zero-Fin {succ-Fin y} {zero-Fin} f g p =
  ⊥-elim (f (cong succ-Fin (sym p)))
is-almost-injective-pinch zero-Fin {succ-Fin y} {succ-Fin z} f g p =
  cong succ-Fin p
is-almost-injective-pinch (succ-Fin x) {zero-Fin} {zero-Fin} f g p =
  refl
is-almost-injective-pinch (succ-Fin x) {succ-Fin y} {succ-Fin z} f g p =
  cong
    ( succ-Fin)
    ( is-almost-injective-pinch x
      ( λ q → f (cong succ-Fin q))
      ( λ q → g (cong succ-Fin q))
      ( is-injective-succ-Fin p))

cases-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) →
  is-decidable (is-succ-Fin (map-inj f zero-Fin)) → (x : Fin k) →
  is-decidable (is-succ-Fin (map-inj f (succ-Fin x))) → Fin l
cases-map-reduce-inj-Fin f (inj₁ (t , p)) x d =
  pinch t (map-inj f (succ-Fin x))
cases-map-reduce-inj-Fin f (inj₂ g) x (inj₁ (y , p)) = y
cases-map-reduce-inj-Fin f (inj₂ g) x (inj₂ h) =
  ⊥-elim (is-nonzero-succ-Fin (is-injective-map-inj f (q ∙ sym p)))
  where
  p : is-zero-Fin (map-inj f zero-Fin)
  p = is-zero-is-not-succ-Fin (map-inj f zero-Fin) g
  q : is-zero-Fin (map-inj f (succ-Fin x))
  q = is-zero-is-not-succ-Fin (map-inj f (succ-Fin x)) h

map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-inj-Fin f x =
  cases-map-reduce-inj-Fin f
    ( is-decidable-is-succ-Fin (map-inj f zero-Fin))
    ( x)
    ( is-decidable-is-succ-Fin (map-inj f (succ-Fin x)))

is-injective-cases-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l))
  (d : is-decidable (is-succ-Fin (map-inj f zero-Fin)))
  (x : Fin k) (e : is-decidable (is-succ-Fin (map-inj f (succ-Fin x))))
  (x' : Fin k) (e' : is-decidable (is-succ-Fin (map-inj f (succ-Fin x')))) →
  cases-map-reduce-inj-Fin f d x e ≡ cases-map-reduce-inj-Fin f d x' e' →
  x ≡ x'
is-injective-cases-map-reduce-inj-Fin f (inj₁ (t , q)) x e x' e' p =
  is-injective-succ-Fin
    ( is-injective-map-inj f
      ( is-almost-injective-pinch t
        ( λ α → is-nonzero-succ-Fin (is-injective-map-inj f (sym α ∙ q))) 
        ( λ α → is-nonzero-succ-Fin (is-injective-map-inj f (sym α ∙ q))) 
        ( p)))
is-injective-cases-map-reduce-inj-Fin
  f (inj₂ g) x (inj₁ (y , q)) x' (inj₁ (y' , q')) p =
  is-injective-succ-Fin
    ( is-injective-map-inj f ((sym q) ∙ (cong succ-Fin p ∙ q')))
is-injective-cases-map-reduce-inj-Fin
  f (inj₂ g) x (inj₁ (y , q)) x' (inj₂ h) p =
  ⊥-elim
    ( is-nonzero-succ-Fin
      ( is-injective-map-inj f
        ( ( is-zero-is-not-succ-Fin (map-inj f (succ-Fin x')) h) ∙
          ( sym (is-zero-is-not-succ-Fin (map-inj f zero-Fin) g)))))
is-injective-cases-map-reduce-inj-Fin
  f (inj₂ g) x (inj₂ h) x' (inj₁ (y' , q')) p =
  ⊥-elim
    ( is-nonzero-succ-Fin
      ( is-injective-map-inj f
        ( ( is-zero-is-not-succ-Fin (map-inj f (succ-Fin x)) h) ∙
          ( sym (is-zero-is-not-succ-Fin (map-inj f zero-Fin) g)))))
is-injective-cases-map-reduce-inj-Fin f (inj₂ g) x (inj₂ h) x' (inj₂ k) p =
  ⊥-elim
    ( is-nonzero-succ-Fin
      ( is-injective-map-inj f
        ( ( is-zero-is-not-succ-Fin (map-inj f (succ-Fin x)) h) ∙
          ( sym (is-zero-is-not-succ-Fin (map-inj f zero-Fin) g)))))

is-injective-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) →
  Injective _≡_ _≡_ (map-reduce-inj-Fin f)
is-injective-map-reduce-inj-Fin f {x} {y} =
  is-injective-cases-map-reduce-inj-Fin f
    ( is-decidable-is-succ-Fin (map-inj f zero-Fin))
    ( x)
    ( is-decidable-is-succ-Fin (map-inj f (succ-Fin x)))
    ( y)
    ( is-decidable-is-succ-Fin (map-inj f (succ-Fin y)))

reduce-inj-Fin : (k l : ℕ) → Fin (succ-ℕ k) ↣ Fin (succ-ℕ l) → Fin k ↣ Fin l
map-inj (reduce-inj-Fin k l f) = map-reduce-inj-Fin f
cong-inj (reduce-inj-Fin k l f) = cong (map-reduce-inj-Fin f)
is-injective-map-inj (reduce-inj-Fin k l f) = is-injective-map-reduce-inj-Fin f

leq-inj-Fin : {k l : ℕ} → Fin k ↣ Fin l → k ≤ l
leq-inj-Fin {zero-ℕ} {zero-ℕ} f = ≤-refl
leq-inj-Fin {zero-ℕ} {succ-ℕ l} f = z≤n
leq-inj-Fin {succ-ℕ k} {zero-ℕ} f =
  ⊥-elim (¬Fin0 (map-inj f zero-Fin))
leq-inj-Fin {succ-ℕ k} {succ-ℕ l} f =
  s≤s (leq-inj-Fin (reduce-inj-Fin k l f))

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → Injective _≡_ _≡_ f → k ≤ l
  leq-is-injective-Fin {k} {l} {f} H = leq-inj-Fin inj-f
    where
    inj-f : Fin k ↣ Fin l
    map-inj inj-f = f
    cong-inj inj-f = cong f
    is-injective-map-inj inj-f = H

-- Finally, we show that there is no injection ℕ ↣ Fin k

inj-toℕ : (k : ℕ) → Fin k ↣ ℕ
map-inj (inj-toℕ k) = toℕ
cong-inj (inj-toℕ k) = cong toℕ
is-injective-map-inj (inj-toℕ k) = toℕ-injective

no-injection-ℕ-Fin : (k : ℕ) → ¬ (ℕ ↣ Fin k)
no-injection-ℕ-Fin k f =
  contradiction-leq-ℕ k k
    ( ≤-refl)
    ( leq-inj-Fin (f ∘i inj-toℕ (succ-ℕ k)))
