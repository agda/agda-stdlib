------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.
{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Base where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product.Base as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (id; _∘_; _on_; flip; _$_)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; ¬[x≢x])
open import Relation.Binary.Indexed.Heterogeneous.Core using (IRel)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc  : (i : Fin n) → Fin (suc n)

-- A conversion: toℕ "i" = i.

toℕ : Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

-- A Fin-indexed variant of Fin.

Fin′ : Fin n → Set
Fin′ i = Fin (toℕ i)

------------------------------------------------------------------------
-- A cast that actually computes on constructors (as opposed to subst)

cast : .(m ≡ n) → Fin m → Fin n
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

fromℕ< : .(m ℕ.< n) → Fin n
fromℕ< {zero}  {suc _} _   = zero
fromℕ< {suc m} {suc _} m<n = suc (fromℕ< (ℕ.s<s⁻¹ m<n))

-- fromℕ<″ m _ = "m".

fromℕ<″ : ∀ m {n} → .(m ℕ.<″ n) → Fin n
fromℕ<″ zero    {suc _} _    = zero
fromℕ<″ (suc m) {suc _} m<″n = suc (fromℕ<″ m (ℕ.s<″s⁻¹ m<″n))

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

reduce≥ : ∀ (i : Fin (m ℕ.+ n)) → .(m ℕ.≤ toℕ i) → Fin n
reduce≥ {zero}  i       _   = i
reduce≥ {suc _} (suc i) m≤i = reduce≥ i (ℕ.s≤s⁻¹ m≤i)

-- inject⋆ m "i" = "i".

inject : ∀ {i : Fin n} → Fin′ i → Fin n
inject {i = suc i} zero    = zero
inject {i = suc i} (suc j) = suc (inject j)

inject! : ∀ {i : Fin (suc n)} → Fin′ i → Fin n
inject! {n = suc _} {i = suc _} zero    = zero
inject! {n = suc _} {i = suc _} (suc j) = suc (inject! j)

inject₁ : Fin n → Fin (suc n)
inject₁ zero    = zero
inject₁ (suc i) = suc (inject₁ i)

inject≤ : Fin m → .(m ℕ.≤ n) → Fin n
inject≤ {n = suc _} zero    _   = zero
inject≤ {n = suc _} (suc i) m≤n = suc (inject≤ i (ℕ.s≤s⁻¹ m≤n))

-- lower₁ "i" _ = "i".

lower₁ : ∀ (i : Fin (suc n)) → n ≢ toℕ i → Fin n
lower₁ {zero}  zero    ne = ¬[x≢x] ne
lower₁ {suc n} zero    _  = zero
lower₁ {suc n} (suc i) ne = suc (lower₁ i (ne ∘ cong suc))

lower : ∀ (i : Fin m) → .(toℕ i ℕ.< n) → Fin n
lower {n = suc n} zero    leq = zero
lower {n = suc n} (suc i) leq = suc (lower i (ℕ.s≤s⁻¹ leq))

-- A strengthening injection into the minimal Fin fibre.
strengthen : ∀ (i : Fin n) → Fin′ (suc i)
strengthen zero    = zero
strengthen (suc i) = suc (strengthen i)

-- splitAt m "i" = inj₁ "i"      if i < m
--                 inj₂ "i - m"  if i ≥ m
-- This is dual to splitAt from Data.Vec.

splitAt : ∀ m {n} → Fin (m ℕ.+ n) → Fin m ⊎ Fin n
splitAt zero    i       = inj₂ i
splitAt (suc m) zero    = inj₁ zero
splitAt (suc m) (suc i) = Sum.map₁ suc (splitAt m i)

-- inverse of above function
join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]′

-- quotRem k "i" = "i % k" , "i / k"
-- This is dual to group from Data.Vec.

quotRem : ∀ n → Fin (m ℕ.* n) → Fin n × Fin m
quotRem {suc m} n i =
  [ (_, zero)
  , Product.map₂ suc ∘ quotRem {m} n
  ]′ $ splitAt n i

-- a variant of quotRem the type of whose result matches the order of multiplication
remQuot : ∀ n → Fin (m ℕ.* n) → Fin m × Fin n
remQuot i = Product.swap ∘ quotRem i

quotient : ∀ n → Fin (m ℕ.* n) → Fin m
quotient n = proj₁ ∘ remQuot n

remainder : ∀ n → Fin (m ℕ.* n) → Fin n
remainder {m} n = proj₂ ∘ remQuot {m} n

-- inverse of remQuot
combine : Fin m → Fin n → Fin (m ℕ.* n)
combine {suc m} {n} zero    j = j ↑ˡ (m ℕ.* n)
combine {suc m} {n} (suc i) j = n ↑ʳ (combine i j)

-- Next in progression after splitAt and remQuot
finToFun : Fin (m ℕ.^ n) → (Fin n → Fin m)
finToFun {m} {suc n} i zero    = quotient (m ℕ.^ n) i
finToFun {m} {suc n} i (suc j) = finToFun (remainder {m} (m ℕ.^ n) i) j

-- inverse of above function
funToFin : (Fin m → Fin n) → Fin (n ℕ.^ m)
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

lift : ∀ k → (Fin m → Fin n) → Fin (k ℕ.+ m) → Fin (k ℕ.+ n)
lift zero    f i       = f i
lift (suc k) f zero    = zero
lift (suc k) f (suc i) = suc (lift k f i)

-- "i" + "j" = "i + j".

infixl 6 _+_

_+_ : ∀ (i : Fin m) (j : Fin n) → Fin (toℕ i ℕ.+ n)
zero  + j = j
suc i + j = suc (i + j)

-- "i" - "j" = "i ∸ j".

infixl 6 _-_

_-_ : ∀ (i : Fin n) (j : Fin′ (suc i)) → Fin (n ℕ.∸ toℕ j)
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

pred : Fin n → Fin n
pred zero    = zero
pred (suc i) = inject₁ i

-- opposite "i" = "n - i" (i.e. the additive inverse).

opposite : Fin n → Fin n
opposite {suc n} zero    = fromℕ n
opposite {suc n} (suc i) = inject₁ (opposite i)

-- The function f(i,j) = if j>i then j-1 else j
-- This is a variant of the thick function from Conor
-- McBride's "First-order unification by structural recursion".

punchOut : ∀ {i j : Fin (suc n)} → i ≢ j → Fin n
punchOut {_}     {zero}   {zero}  i≢j = ¬[x≢x] i≢j
punchOut {_}     {zero}   {suc j} _   = j
punchOut {suc _} {suc i}  {zero}  _   = zero
punchOut {suc _} {suc i}  {suc j} i≢j = suc (punchOut (i≢j ∘ cong suc))

-- The function f(i,j) = if j≥i then j+1 else j

punchIn : Fin (suc n) → Fin n → Fin (suc n)
punchIn zero    j       = suc j
punchIn (suc i) zero    = zero
punchIn (suc i) (suc j) = suc (punchIn i j)

-- The function f(i,j) such that f(i,j) = if j≤i then j else j-1

pinch : Fin n → Fin (suc n) → Fin n
pinch {suc n} _       zero    = zero
pinch {suc n} zero    (suc j) = j
pinch {suc n} (suc i) (suc j) = suc (pinch i j)

------------------------------------------------------------------------
-- Order relations

infix 4 _≤_ _≥_ _<_ _>_ _≰_ _≮_

_≤_ : IRel Fin 0ℓ
i ≤ j = toℕ i ℕ.≤ toℕ j

_≥_ : IRel Fin 0ℓ
i ≥ j = toℕ i ℕ.≥ toℕ j

_<_ : IRel Fin 0ℓ
i < j = toℕ i ℕ.< toℕ j

_>_ : IRel Fin 0ℓ
i > j = toℕ i ℕ.> toℕ j

_≰_ : ∀ {n} → Rel (Fin n) 0ℓ
i ≰ j = ¬ (i ≤ j)

_≮_ : ∀ {n} → Rel (Fin n) 0ℓ
i ≮ j = ¬ (i < j)

------------------------------------------------------------------------
-- An ordering view.

data Ordering {n : ℕ} : Fin n → Fin n → Set where
  less    : ∀ greatest (least : Fin′ greatest) →
            Ordering (inject least) greatest
  equal   : ∀ i → Ordering i i
  greater : ∀ greatest (least : Fin′ greatest) →
            Ordering greatest (inject least)

compare : ∀ (i j : Fin n) → Ordering i j
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

-- Version 2.0

raise = _↑ʳ_
{-# WARNING_ON_USAGE raise
"Warning: raise was deprecated in v2.0.
Please use _↑ʳ_ instead."
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

data _≺_ : ℕ → ℕ → Set where
  _≻toℕ_ : ∀ n (i : Fin n) → toℕ i ≺ n

{-# WARNING_ON_USAGE _≺_
"Warning: _≺_ was deprecated in v2.0.
Please use equivalent relation _<_ instead."
#-}
{-# WARNING_ON_USAGE _≻toℕ_
"Warning: _≻toℕ_ was deprecated in v2.0.
Please use toℕ<n from Data.Fin.Properties instead."
#-}
