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
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s; _^_)
open import Data.Nat.Properties.Core using (≤-pred)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (id; _∘_; _on_; flip)
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)
open import Relation.Binary.Indexed.Heterogeneous using (IRel)

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- A conversion: toℕ "i" = i.

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

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- fromℕ n = "n".

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

-- fromℕ< {m} _ = "m".

fromℕ< : ∀ {m n} → m ℕ.< n → Fin n
fromℕ< {zero}  {suc n} m≤n = zero
fromℕ< {suc m} {suc n} m≤n = suc (fromℕ< (≤-pred m≤n))

-- fromℕ<″ m _ = "m".

fromℕ<″ : ∀ m {n} → m ℕ.<″ n → Fin n
fromℕ<″ zero    (ℕ.less-than-or-equal refl) = zero
fromℕ<″ (suc m) (ℕ.less-than-or-equal refl) =
  suc (fromℕ<″ m (ℕ.less-than-or-equal refl))

-- canonical liftings of i:Fin m to larger index

-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m ℕ.+ n)
zero    ↑ˡ n = zero
(suc i) ↑ˡ n = suc (i ↑ˡ n)

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
zero    ↑ʳ i = i
(suc n) ↑ʳ i = suc (n ↑ʳ i)

-- reduce≥ "m + i" _ = "i".

reduce≥ : ∀ {m n} (i : Fin (m ℕ.+ n)) (i≥m : toℕ i ℕ.≥ m) → Fin n
reduce≥ {zero}  i       i≥m       = i
reduce≥ {suc m} (suc i) (s≤s i≥m) = reduce≥ i i≥m

-- inject⋆ m "i" = "i".

inject : ∀ {n} {i : Fin n} → Fin′ i → Fin n
inject {i = suc i} zero    = zero
inject {i = suc i} (suc j) = suc (inject j)

inject! : ∀ {n} {i : Fin (suc n)} → Fin′ i → Fin n
inject! {n = suc _} {i = suc _}  zero    = zero
inject! {n = suc _} {i = suc _}  (suc j) = suc (inject! j)

inject₁ : ∀ {m} → Fin m → Fin (suc m)
inject₁ zero    = zero
inject₁ (suc i) = suc (inject₁ i)

inject≤ : ∀ {m n} → Fin m → m ℕ.≤ n → Fin n
inject≤ {_} {suc n} zero    le = zero
inject≤ {_} {suc n} (suc i) le = suc (inject≤ i (≤-pred le))

-- lower₁ "i" _ = "i".

lower₁ : ∀ {n} → (i : Fin (suc n)) → (n ≢ toℕ i) → Fin n
lower₁ {zero} zero ne = ⊥-elim (ne refl)
lower₁ {suc n} zero _ = zero
lower₁ {suc n} (suc i) ne = suc (lower₁ i λ x → ne (cong suc x))

-- A strengthening injection into the minimal Fin fibre.
strengthen : ∀ {n} (i : Fin n) → Fin′ (suc i)
strengthen zero    = zero
strengthen (suc i) = suc (strengthen i)

-- splitAt m "i" = inj₁ "i"      if i < m
--                 inj₂ "i - m"  if i ≥ m
-- This is dual to splitAt from Data.Vec.

splitAt : ∀ m {n} → Fin (m ℕ.+ n) → Fin m ⊎ Fin n
splitAt zero    i       = inj₂ i
splitAt (suc m) zero    = inj₁ zero
splitAt (suc m) (suc i) = Sum.map suc id (splitAt m i)

-- inverse of above function
join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]′

-- quotRem k "i" = "i % k" , "i / k"
-- This is dual to group from Data.Vec.

quotRem : ∀ {n} k → Fin (n ℕ.* k) → Fin k × Fin n
quotRem {suc n} k i with splitAt k i
... | inj₁ j = j , zero
... | inj₂ j = Product.map₂ suc (quotRem {n} k j)

-- a variant of quotRem the type of whose result matches the order of multiplication
remQuot : ∀ {n} k → Fin (n ℕ.* k) → Fin n × Fin k
remQuot k = Product.swap ∘ quotRem k

quotient : ∀ {n} k → Fin (n ℕ.* k) → Fin n
quotient {n} k = proj₁ ∘ remQuot {n} k

remainder : ∀ {n} k → Fin (n ℕ.* k) → Fin k
remainder {n} k = proj₂ ∘ remQuot {n} k

-- inverse of remQuot
combine : ∀ {n k} → Fin n → Fin k → Fin (n ℕ.* k)
combine {suc n} {k} zero    y = y ↑ˡ (n ℕ.* k)
combine {suc n} {k} (suc x) y = k ↑ʳ (combine x y)

-- Next in progression after splitAt and remQuot
finToFun : ∀ {m n} → Fin (n ^ m) → (Fin m → Fin n)
finToFun {suc m} {n} k zero    = quotient (n ^ m) k
finToFun {suc m} {n} k (suc i) = finToFun (remainder {n} (n ^ m) k) i

-- inverse of above function
funToFin : ∀ {m n} → (Fin m → Fin n) → Fin (n ^ m)
funToFin {zero}  f = zero
funToFin {suc m} f = combine (f zero) (funToFin (f ∘ suc))

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
fold′ {n = suc n} T f x (suc i)  =
  f i (fold′ (T ∘ inject₁) (f ∘ inject₁) x i)

-- Lifts functions.

lift : ∀ {m n} k → (Fin m → Fin n) → Fin (k ℕ.+ m) → Fin (k ℕ.+ n)
lift zero    f i       = f i
lift (suc k) f zero    = zero
lift (suc k) f (suc i) = suc (lift k f i)

-- "i" + "j" = "i + j".

infixl 6 _+_

_+_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (toℕ i ℕ.+ n)
zero  + j = j
suc i + j = suc (i + j)

-- "i" - "j" = "i ∸ j".

infixl 6 _-_

_-_ : ∀ {m} (i : Fin m) (j : Fin′ (suc i)) → Fin (m ℕ.∸ toℕ j)
i     - zero   = i
suc i - suc j  = i - j

-- m ℕ- "i" = "m ∸ i".

infixl 6 _ℕ-_

_ℕ-_ : (n : ℕ) (j : Fin (suc n)) → Fin (suc n ℕ.∸ toℕ j)
n     ℕ- zero   = fromℕ n
suc n ℕ- suc i  = n ℕ- i

-- m ℕ-ℕ "i" = m ∸ i.

infixl 6 _ℕ-ℕ_

_ℕ-ℕ_ : (n : ℕ) → Fin (suc n) → ℕ
n     ℕ-ℕ zero   = n
suc n ℕ-ℕ suc i  = n ℕ-ℕ i

-- pred "i" = "pred i".

pred : ∀ {n} → Fin n → Fin n
pred zero    = zero
pred (suc i) = inject₁ i

-- opposite "i" = "n - i" (i.e. the additive inverse).

opposite : ∀ {n} → Fin n → Fin n
opposite {suc n} zero    = fromℕ n
opposite {suc n} (suc i) = inject₁ (opposite i)

-- The function f(i,j) = if j>i then j-1 else j
-- This is a variant of the thick function from Conor
-- McBride's "First-order unification by structural recursion".

punchOut : ∀ {m} {i j : Fin (suc m)} → i ≢ j → Fin m
punchOut {_}     {zero}   {zero}  i≢j = ⊥-elim (i≢j refl)
punchOut {_}     {zero}   {suc j} _   = j
punchOut {suc m} {suc i}  {zero}  _   = zero
punchOut {suc m} {suc i}  {suc j} i≢j = suc (punchOut (i≢j ∘ cong suc))

-- The function f(i,j) = if j≥i then j+1 else j

punchIn : ∀ {m} → Fin (suc m) → Fin m → Fin (suc m)
punchIn zero    j       = suc j
punchIn (suc i) zero    = zero
punchIn (suc i) (suc j) = suc (punchIn i j)

-- The function f(i,j) such that f(i,j) = if j≤i then j else j-1

pinch : ∀ {n} → Fin n → Fin (suc n) → Fin n
pinch {suc n} _       zero    = zero
pinch {suc n} zero    (suc j) = j
pinch {suc n} (suc i) (suc j) = suc (pinch i j)

------------------------------------------------------------------------
-- Order relations

infix 4 _≤_ _≥_ _<_ _>_

_≤_ : IRel Fin 0ℓ
i ≤ j = toℕ i ℕ.≤ toℕ j

_≥_ : IRel Fin 0ℓ
i ≥ j = toℕ i ℕ.≥ toℕ j

_<_ : IRel Fin 0ℓ
i < j = toℕ i ℕ.< toℕ j

_>_ : IRel Fin 0ℓ
i > j = toℕ i ℕ.> toℕ j


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
... | less    greatest least = less    (suc greatest) (suc least)
... | greater greatest least = greater (suc greatest) (suc least)
... | equal   i              = equal   (suc i)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.2

fromℕ≤ = fromℕ<
{-# WARNING_ON_USAGE fromℕ≤
"Warning: fromℕ≤ was deprecated in v1.2.
Please use fromℕ< instead."
#-}
fromℕ≤″ = fromℕ<″
{-# WARNING_ON_USAGE fromℕ≤″
"Warning: fromℕ≤″ was deprecated in v1.2.
Please use fromℕ<″ instead."
#-}

-- Version 2.0

raise = _↑ʳ_
{-# WARNING_ON_USAGE raise
"Warning: raise was deprecated in v2.0.
Please use _↑_ʳ instead."
#-}
inject+ : ∀ {m} n → Fin m → Fin (m ℕ.+ n)
inject+ n i = i ↑ˡ n
{-# WARNING_ON_USAGE inject+
"Warning: inject+ was deprecated in v2.0.
Please use _↑ˡ_ instead.
NB argument order has been flipped:
the left-hand argument is the Fin m
the right-hand is the Nat index increment."
#-}
