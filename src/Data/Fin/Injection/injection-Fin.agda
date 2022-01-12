------------------------------------------------------------------------
-- The Agda standard library
--
-- Proving that Fin m ↪ Fin n implies that m ≤ n.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Injection.injection-Fin where
            
open import Data.Empty using (⊥; ⊥-elim)

open import Data.Fin.Base using (Fin)
  renaming
    ( zero to zero-Fin;
      suc to succ-Fin)

open import Data.Nat using (ℕ) renaming (suc to succ-ℕ; zero to zero-ℕ)

open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Data.Unit using (⊤; tt)
      
open import Function.Base using (id; _∘_)

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
    {l : Level} (A : Set l)
    where
    
    is-⊥ : Set l
    is-⊥ = ¬ A

    is-non⊥ : Set l
    is-non⊥ = ¬ is-⊥


  module _
    {l1 l2 : Level} {A : Set l1} {B : Set l2}
    where

    is-injective : (A → B) → Set (l1 ⊔ l2)
    is-injective f = Injective _≡_ _≡_ f

    is-not-injective : (A → B) → Set (l1 ⊔ l2)
    is-not-injective f = ¬ (is-injective f)

  _↣_ : {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
  A ↣ B = Σ (A → B) is-injective

  module _
    {l1 l2 : Level} {A : Set l1} {B : Set l2}
    where

    map-inj : A ↣ B → A → B
    map-inj f = proj₁ f

    is-injective-map-inj : (f : A ↣ B) → is-injective (map-inj f)
    is-injective-map-inj f = proj₂ f

  module _
    {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
    where

    is-injective-comp :
      {g : B → C} {f : A → B} →
      is-injective g → is-injective f → is-injective (g ∘ f)
    is-injective-comp H K p = K (H p)

    _∘i_ : B ↣ C → A ↣ B → A ↣ C
    proj₁ (g ∘i f) = map-inj g ∘ map-inj f
    proj₂ (g ∘i f) =
      is-injective-comp (is-injective-map-inj g) (is-injective-map-inj f)

-- Decidability

is-decidable : {l : Level} (A : Set l) → Set l
is-decidable A = A ⊎ (¬ A)

-- Inequality on ℕ

leq-ℕ : ℕ → ℕ → Set lzero
leq-ℕ zero-ℕ m = ⊤
leq-ℕ (succ-ℕ n) zero-ℕ = ⊥
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ

leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = tt

refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = tt
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

-- Strict inequality on ℕ

le-ℕ : ℕ → ℕ → Set lzero
le-ℕ m zero-ℕ = ⊥
le-ℕ zero-ℕ (succ-ℕ m) = ⊤
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = tt
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = tt
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

le-succ-ℕ : {x : ℕ} → le-ℕ x (succ-ℕ x)
le-succ-ℕ {zero-ℕ} = tt
le-succ-ℕ {succ-ℕ x} = le-succ-ℕ {x}

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (x ≡ y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H ()
neq-le-ℕ {succ-ℕ x} {succ-ℕ .x} H refl = neq-le-ℕ {x} {x} H refl

--------------------------------------------------------------------------------
      
-- Finite types

is-⊥-Fin-zero-ℕ : is-⊥ (Fin 0)
is-⊥-Fin-zero-ℕ ()

is-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Set lzero
is-zero-Fin x = x ≡ zero-Fin

is-nonzero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Set lzero
is-nonzero-Fin x = ¬ (is-zero-Fin x)

is-nonzero-succ-Fin : {k : ℕ} {x : Fin k} → is-nonzero-Fin (succ-Fin x)
is-nonzero-succ-Fin ()

is-injective-succ-Fin : {k : ℕ} → is-injective (succ-Fin {k})
is-injective-succ-Fin {k} refl = refl

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

repeat-Fin : {k : ℕ} (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin zero-Fin zero-Fin = zero-Fin
repeat-Fin zero-Fin (succ-Fin y) = y
repeat-Fin (succ-Fin x) zero-Fin = zero-Fin
repeat-Fin (succ-Fin x) (succ-Fin y) = succ-Fin (repeat-Fin x y)

is-almost-injective-repeat-Fin :
  {k : ℕ} (x : Fin k) {y z : Fin (succ-ℕ k)} →
  ¬ (succ-Fin x ≡ y) → ¬ (succ-Fin x ≡ z) →
  repeat-Fin x y ≡ repeat-Fin x z → y ≡ z
is-almost-injective-repeat-Fin zero-Fin {zero-Fin} {zero-Fin} f g p =
  refl
is-almost-injective-repeat-Fin zero-Fin {zero-Fin} {succ-Fin z} f g p =
  ⊥-elim (g (cong succ-Fin p))
is-almost-injective-repeat-Fin zero-Fin {succ-Fin y} {zero-Fin} f g p =
  ⊥-elim (f (cong succ-Fin (sym p)))
is-almost-injective-repeat-Fin zero-Fin {succ-Fin y} {succ-Fin z} f g p =
  cong succ-Fin p
is-almost-injective-repeat-Fin (succ-Fin x) {zero-Fin} {zero-Fin} f g p =
  refl
is-almost-injective-repeat-Fin (succ-Fin x) {succ-Fin y} {succ-Fin z} f g p =
  cong
    ( succ-Fin)
    ( is-almost-injective-repeat-Fin x
      ( λ q → f (cong succ-Fin q))
      ( λ q → g (cong succ-Fin q))
      ( is-injective-succ-Fin p))

cases-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) →
  is-decidable (is-succ-Fin (map-inj f zero-Fin)) → (x : Fin k) →
  is-decidable (is-succ-Fin (map-inj f (succ-Fin x))) → Fin l
cases-map-reduce-inj-Fin f (inj₁ (t , p)) x d =
  repeat-Fin t (map-inj f (succ-Fin x))
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
      ( is-almost-injective-repeat-Fin t
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
  is-injective (map-reduce-inj-Fin f)
is-injective-map-reduce-inj-Fin f {x} {y} =
  is-injective-cases-map-reduce-inj-Fin f
    ( is-decidable-is-succ-Fin (map-inj f zero-Fin))
    ( x)
    ( is-decidable-is-succ-Fin (map-inj f (succ-Fin x)))
    ( y)
    ( is-decidable-is-succ-Fin (map-inj f (succ-Fin y)))

reduce-inj-Fin : (k l : ℕ) → Fin (succ-ℕ k) ↣ Fin (succ-ℕ l) → Fin k ↣ Fin l
proj₁ (reduce-inj-Fin k l f) = map-reduce-inj-Fin f
proj₂ (reduce-inj-Fin k l f) = is-injective-map-reduce-inj-Fin f

leq-inj-Fin : {k l : ℕ} → Fin k ↣ Fin l → k ≤-ℕ l
leq-inj-Fin {zero-ℕ} {zero-ℕ} (f , H) = refl-leq-ℕ 0
leq-inj-Fin {zero-ℕ} {succ-ℕ l} (f , H) = leq-zero-ℕ (succ-ℕ l)
leq-inj-Fin {succ-ℕ k} {zero-ℕ} (f , H) =
  ⊥-elim (is-⊥-Fin-zero-ℕ (f zero-Fin))
leq-inj-Fin {succ-ℕ k} {succ-ℕ l} (f , H) =
  leq-inj-Fin (reduce-inj-Fin k l (f , H))

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
  leq-is-injective-Fin H = leq-inj-Fin (_ , H)

abstract
  is-not-injective-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → is-not-injective f
  is-not-injective-le-Fin {k} {l} f p =
    (contradiction-le-ℕ l k p) ∘ leq-is-injective-Fin 

abstract
  is-not-injective-map-Fin-succ-Fin :
    {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → is-not-injective f 
  is-not-injective-map-Fin-succ-Fin {k} f =
    is-not-injective-le-Fin f (le-succ-ℕ {k})

-- Finally, we show that there is no injection ℕ ↣ Fin k

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} zero-Fin = k
nat-Fin {succ-ℕ k} (succ-Fin x) = nat-Fin x

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} zero-Fin =
  succ-le-ℕ k
strict-upper-bound-nat-Fin {succ-ℕ k} (succ-Fin x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
  
is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {succ-Fin x} {succ-Fin y} p =
  cong succ-Fin (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {succ-Fin x} {zero-Fin} p =
  ⊥-elim (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {zero-Fin} {succ-Fin y} p =
  ⊥-elim (neq-le-ℕ (strict-upper-bound-nat-Fin y) (sym p))
is-injective-nat-Fin {succ-ℕ k} {zero-Fin} {zero-Fin} p =
  refl

inj-nat-Fin : (k : ℕ) → Fin k ↣ ℕ
proj₁ (inj-nat-Fin k) = nat-Fin
proj₂ (inj-nat-Fin k) = is-injective-nat-Fin

no-injection-ℕ-Fin : (k : ℕ) → ¬ (ℕ ↣ Fin k)
no-injection-ℕ-Fin k f =
  contradiction-leq-ℕ k k
    ( refl-leq-ℕ k)
    ( leq-inj-Fin (f ∘i inj-nat-Fin (succ-ℕ k)))
