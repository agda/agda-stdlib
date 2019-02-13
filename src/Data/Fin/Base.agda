------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Base where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s)
open import Function using (_∘_; _on_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- A conversion: toℕ "n" = n.

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

-- A Fin-indexed variant of Fin.

Fin′ : ∀ {n} → Fin n → Set
Fin′ i = Fin (toℕ i)

------------------------------------------------------------------------
-- A cast that actually computes on constructors (as opposed to subst)

cast : ∀ {m n} → .(_ : m ≡ n) → Fin m → Fin n
cast {zero}  {zero}  eq k       = k
cast {suc m} {suc n} eq zero    = zero
cast {suc m} {suc n} eq (suc k) = suc (cast (cong ℕ.pred eq) k)
cast {zero}  {suc n} ()
cast {suc m} {zero}  ()

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- fromℕ n = "n".

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

-- fromℕ≤ {m} _ = "m".

fromℕ≤ : ∀ {m n} → m ℕ.< n → Fin n
fromℕ≤ (s≤s z≤n)       = zero
fromℕ≤ (s≤s (s≤s m≤n)) = suc (fromℕ≤ (s≤s m≤n))

-- fromℕ≤″ m _ = "m".

fromℕ≤″ : ∀ m {n} → m ℕ.<″ n → Fin n
fromℕ≤″ zero    (ℕ.less-than-or-equal refl) = zero
fromℕ≤″ (suc m) (ℕ.less-than-or-equal refl) =
  suc (fromℕ≤″ m (ℕ.less-than-or-equal refl))

-- raise m "n" = "m + n".

raise : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
raise zero    i = i
raise (suc n) i = suc (raise n i)

-- reduce≥ "m + n" _ = "n".

reduce≥ : ∀ {m n} (i : Fin (m ℕ.+ n)) (i≥m : toℕ i ℕ.≥ m) → Fin n
reduce≥ {zero}  i       i≥m       = i
reduce≥ {suc m} zero    ()
reduce≥ {suc m} (suc i) (s≤s i≥m) = reduce≥ i i≥m

-- inject⋆ m "n" = "n".

inject : ∀ {n} {i : Fin n} → Fin′ i → Fin n
inject {i = zero}  ()
inject {i = suc i} zero    = zero
inject {i = suc i} (suc j) = suc (inject j)

inject! : ∀ {n} {i : Fin (suc n)} → Fin′ i → Fin n
inject! {n = zero}  {i = suc ()} _
inject!             {i = zero}   ()
inject! {n = suc _} {i = suc _}  zero    = zero
inject! {n = suc _} {i = suc _}  (suc j) = suc (inject! j)

inject+ : ∀ {m} n → Fin m → Fin (m ℕ.+ n)
inject+ n zero    = zero
inject+ n (suc i) = suc (inject+ n i)

inject₁ : ∀ {m} → Fin m → Fin (suc m)
inject₁ zero    = zero
inject₁ (suc i) = suc (inject₁ i)

inject≤ : ∀ {m n} → Fin m → m ℕ.≤ n → Fin n
inject≤ zero    (s≤s le) = zero
inject≤ (suc i) (s≤s le) = suc (inject≤ i le)

-- A strengthening injection into the minimal Fin fibre.
strengthen : ∀ {n} (i : Fin n) → Fin′ (suc i)
strengthen zero    = zero
strengthen (suc i) = suc (strengthen i)

------------------------------------------------------------------------
-- Operations

-- Folds.

fold : ∀ {t} (T : ℕ → Set t) {m} →
       (∀ {n} → T n → T (suc n)) →
       (∀ {n} → T (suc n)) →
       Fin m → T m
fold T f x zero    = x
fold T f x (suc i) = f (fold T f x i)

fold′ : ∀ {n t} (T : Fin (suc n) → Set t) →
        (∀ i → T (inject₁ i) → T (suc i)) →
        T zero →
        ∀ i → T i
fold′             T f x zero     = x
fold′ {n = zero}  T f x (suc ())
fold′ {n = suc n} T f x (suc i)  =
  f i (fold′ (T ∘ inject₁) (f ∘ inject₁) x i)

-- Lifts functions.

lift : ∀ {m n} k → (Fin m → Fin n) → Fin (k ℕ.+ m) → Fin (k ℕ.+ n)
lift zero    f i       = f i
lift (suc k) f zero    = zero
lift (suc k) f (suc i) = suc (lift k f i)

-- "m" + "n" = "m + n".

infixl 6 _+_

_+_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (toℕ i ℕ.+ n)
zero  + j = j
suc i + j = suc (i + j)

-- "m" - "n" = "m ∸ n".

infixl 6 _-_

_-_ : ∀ {m} (i : Fin m) (j : Fin′ (suc i)) → Fin (m ℕ.∸ toℕ j)
i     - zero   = i
zero  - suc ()
suc i - suc j  = i - j

-- m ℕ- "n" = "m ∸ n".

infixl 6 _ℕ-_

_ℕ-_ : (n : ℕ) (j : Fin (suc n)) → Fin (suc n ℕ.∸ toℕ j)
n     ℕ- zero   = fromℕ n
zero  ℕ- suc ()
suc n ℕ- suc i  = n ℕ- i

-- m ℕ-ℕ "n" = m ∸ n.

infixl 6 _ℕ-ℕ_

_ℕ-ℕ_ : (n : ℕ) → Fin (suc n) → ℕ
n     ℕ-ℕ zero   = n
zero  ℕ-ℕ suc ()
suc n ℕ-ℕ suc i  = n ℕ-ℕ i

-- pred "n" = "pred n".

pred : ∀ {n} → Fin n → Fin n
pred zero    = zero
pred (suc i) = inject₁ i

-- The function f(i,j) = if j>i then j-1 else j
-- This is a variant of the thick function from Conor
-- McBride's "First-order unification by structural recursion".

punchOut : ∀ {m} {i j : Fin (suc m)} → i ≢ j → Fin m
punchOut {_}     {zero}   {zero}  i≢j = ⊥-elim (i≢j refl)
punchOut {_}     {zero}   {suc j} _   = j
punchOut {zero}  {suc ()}
punchOut {suc m} {suc i}  {zero}  _   = zero
punchOut {suc m} {suc i}  {suc j} i≢j = suc (punchOut (i≢j ∘ cong suc))

-- The function f(i,j) = if j≥i then j+1 else j

punchIn : ∀ {m} → Fin (suc m) → Fin m → Fin (suc m)
punchIn zero    j       = suc j
punchIn (suc i) zero    = zero
punchIn (suc i) (suc j) = suc (punchIn i j)

------------------------------------------------------------------------
-- Order relations

infix 4 _≤_ _<_

_≤_ : ∀ {n} → Rel (Fin n) ℓ₀
_≤_ = ℕ._≤_ on toℕ

_<_ : ∀ {n} → Rel (Fin n) ℓ₀
_<_ = ℕ._<_ on toℕ

data _≺_ : ℕ → ℕ → Set where
  _≻toℕ_ : ∀ n (i : Fin n) → toℕ i ≺ n

------------------------------------------------------------------------
-- An ordering view.

data Ordering {n : ℕ} : Fin n → Fin n → Set where
  less    : ∀ greatest (least : Fin′ greatest) →
            Ordering (inject least) greatest
  equal   : ∀ i → Ordering i i
  greater : ∀ greatest (least : Fin′ greatest) →
            Ordering greatest (inject least)

compare : ∀ {n} (i j : Fin n) → Ordering i j
compare zero    zero    = equal   zero
compare zero    (suc j) = less    (suc j) zero
compare (suc i) zero    = greater (suc i) zero
compare (suc i) (suc j) with compare i j
compare (suc .(inject least)) (suc .greatest) | less    greatest least =
  less    (suc greatest) (suc least)
compare (suc .greatest) (suc .(inject least)) | greater greatest least =
  greater (suc greatest) (suc least)
compare (suc .i)        (suc .i)              | equal i =
  equal (suc i)
