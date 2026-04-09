------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded Natural numbers (Fin, without the runtime overhead)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded.Base where

open import Data.Bool.Base using (T; true; false)
import Data.Bool.Properties as Boolₚ
open import Data.Empty using (⊥-elim)
open import Data.Irrelevant as Irrelevant using (Irrelevant; [_]; pure; _<*>_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; z<s; s<s; s<s⁻¹; NonZero)
import Data.Nat.Properties as ℕₚ
import Data.Nat.DivMod as ℕₚ
open import Data.Product.Base as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Refinement as Refinement using (Refinement; _,_; Refinement-syntax; proof)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function.Base using (id; _$_; _∘_; _on_)
open import Function.Bundles using (Equivalence); open Equivalence using (from)

open import Level using (0ℓ)

open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Indexed.Heterogeneous.Core using (IRel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym; ≢-sym)
open import Relation.Nullary.Decidable using (recompute; T?; yes; no)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

Fin : ℕ → Set
Fin n = [ m ∈ ℕ ∣ m ℕ.< n ]

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

nonZeroIndex : Fin n → ℕ.NonZero n
nonZeroIndex {n = suc _} _ = _

-- Recovering constructors and pattern matching

fzero : ∀ {n} → Fin (suc n)
fzero = 0 , [ z<s ]

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc = Refinement.map suc s<s

data View : ∀ {n} (k : Fin n) → Set where
  zero : View {suc n} fzero
  suc  : (k : Fin n) → View (fsuc k)

view : (k : Fin n) → View k
view {suc n} (0 , prf)     = zero
view {suc n} (suc k , prf) = suc (k , (| s<s⁻¹ prf |))

unview : {k : Fin n} → View k → Fin n
unview {k = k} _ = k

-- A conversion: toℕ "i" = i.

toℕ : Fin n → ℕ
toℕ = Refinement.value

-- A Fin-indexed variant of Fin.

Fin′ : Fin n → Set
Fin′ i = Fin (toℕ i)

------------------------------------------------------------------------
-- A cast that actually computes on constructors (as opposed to subst)

cast : .(m ≡ n) → Fin m → Fin n
cast {m = m} {n = n} eq
  = Refinement.map id
  $ subst (_ ℕ.<_) (recompute (m ℕₚ.≟ n) eq)

-- Tests showing that cast does compute on constructors

module _ .(eqs : suc m ≡ suc n) where

  _ : cast eqs fzero ≡ fzero
  _ = refl

  _ : .(eq : m ≡ n) (k : Fin m) →
      cast eqs (fsuc k) ≡ fsuc (cast eq k)
  _ = λ eq k → refl

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- fromℕ n = "n".

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ n = n , [ ℕₚ.n<1+n n ]

-- fromℕ< {m} _ = "m".

fromℕ< : .(m ℕ.< n) → Fin n
fromℕ< m<n = _ , [ m<n ]

fromℕ<ᵇ : T (m ℕ.<ᵇ n) → Fin n
fromℕ<ᵇ p = fromℕ< (ℕₚ.<ᵇ⇒< _ _ p)

-- fromℕ<″ m _ = "m".

fromℕ<″ : ∀ m {n} → .(m ℕ.<″ n) → Fin n
fromℕ<″ m m<″n = m , [ ℕₚ.<″⇒< m<″n ]

-- Canonical liftings of i:Fin m to a larger index

-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m ℕ.+ n)
_↑ˡ_ {m} i n = Refinement.map id prf i where

  prf : ∀ {k} → k ℕ.< m → k ℕ.< m ℕ.+ n
  prf {k} k<m = let open ℕₚ.≤-Reasoning in begin-strict
    k       ≡⟨ ℕₚ.+-identityʳ k ⟨
    k ℕ.+ 0 <⟨ ℕₚ.+-mono-<-≤ k<m z≤n ⟩
    m ℕ.+ n ∎

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
n ↑ʳ i = Refinement.map (n ℕ.+_) (ℕₚ.+-monoʳ-< n) i

-- reduce≥ "m + i" _ = "i".

reduce≥ : ∀ (i : Fin (m ℕ.+ n)) → .(m ℕ.≤ toℕ i) → Fin n
reduce≥ {m = m} {n = n} (k , prf) m≤i
  = k ℕ.∸ m , (| go prf [ m≤i ] |) where

  go : k ℕ.< m ℕ.+ n → m ℕ.≤ k → k ℕ.∸ m ℕ.< n
  go k<m+n m≤k = let open ℕₚ.≤-Reasoning in begin-strict
    k ℕ.∸ m       <⟨ ℕₚ.∸-monoˡ-< k<m+n m≤k ⟩
    m ℕ.+ n ℕ.∸ m ≡⟨ ℕₚ.m+n∸m≡n m n ⟩
    n             ∎

-- inject⋆ m "i" = "i".

inject : ∀ {i : Fin n} → Fin′ i → Fin n
inject {i = i} (k , k<i) = k , (| ℕₚ.<-trans k<i (proof i)|)

inject! : ∀ {i : Fin (suc n)} → Fin′ i → Fin n
inject! {i = i} (k , k<i)
  = k , (| ℕₚ.<-≤-trans k<i (| ℕ.s≤s⁻¹ (proof i)|) |)

inject₁ : Fin n → Fin (suc n)
inject₁ (k , k<n) = k , (| ℕₚ.m<n⇒m<1+n k<n |)

inject≤ : Fin m → .(m ℕ.≤ n) → Fin n
inject≤ (k , k<m) m≤n
  = k , (| ℕₚ.<-≤-trans k<m [ m≤n ] |)

-- lower₁ "i" _ = "i".

lower₁ : ∀ (i : Fin (suc n)) → n ≢ toℕ i → Fin n
lower₁ (k , k<1+n) n≢i
  = k , (| (λ prf → ℕₚ.≤∧≢⇒< (ℕ.s≤s⁻¹ prf) (≢-sym n≢i)) k<1+n |)

lower : ∀ (i : Fin m) → .(toℕ i ℕ.< n) → Fin n
lower (k , _) k<n = k , [ k<n ]

-- A strengthening injection into the minimal Fin fibre.

strengthen : ∀ (i : Fin n) → Fin′ (fsuc i)
strengthen (k , prf) = (k , [ ℕₚ.≤-refl ])

-- splitAt m "i" = inj₁ "i"      if i < m
--                 inj₂ "i - m"  if i ≥ m
-- This is dual to splitAt from Data.Vec.

splitAt : ∀ m {n} → Fin (m ℕ.+ n) → Fin m ⊎ Fin n
splitAt m i@(k , prf) with T? (k ℕ.<ᵇ m)
... | yes k<ᵇm = inj₁ (k , [ ℕₚ.<ᵇ⇒< k m k<ᵇm ])
... | no  k≮ᵇm = inj₂ (reduce≥ i (ℕₚ.≮⇒≥ (k≮ᵇm ∘ ℕₚ.<⇒<ᵇ)))

-- inverse of above function
join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]′

-- quotRem n "i" = "i % n" , "i / n"
-- This is dual to group from Data.Vec.

quotRem : ∀ n → Fin (m ℕ.* n) → Fin n × Fin m
quotRem {m = m} zero i = ⊥-elim (¬Fin0 (subst Fin (ℕₚ.*-zeroʳ m) i))
quotRem {m = m} n@(suc _) (i , i<m*n)
  = (i ℕ.% n , [ ℕₚ.m%n<n i n ])
  , (i ℕ./ n , (| ℕₚ.m<n*o⇒m/o<n i<m*n |))

-- a variant of quotRem the type of whose result matches the order of multiplication
remQuot : ∀ n → Fin (m ℕ.* n) → Fin m × Fin n
remQuot i = Product.swap ∘ quotRem i

quotient : ∀ n → Fin (m ℕ.* n) → Fin m
quotient n = proj₁ ∘ remQuot n

remainder : ∀ n → Fin (m ℕ.* n) → Fin n
remainder {m} n = proj₂ ∘ remQuot {m} n

-- inverse of remQuot
combine : Fin m → Fin n → Fin (m ℕ.* n)
combine {m = suc m} {n = n} (k , k<m) (l , l<n)
  = (k ℕ.* n) ℕ.+ l , (| go (| ℕ.s≤s⁻¹ k<m |) l<n |)

  where

  go : k ℕ.≤ m → l ℕ.< n → k ℕ.* n ℕ.+ l ℕ.< suc m ℕ.* n
  go k≤m l<n = let open ℕₚ.≤-Reasoning in begin-strict
    k ℕ.* n ℕ.+ l <⟨ ℕₚ.+-mono-≤-< (ℕₚ.*-monoˡ-≤ n k≤m) l<n ⟩
    m ℕ.* n ℕ.+ n ≡⟨ ℕₚ.+-comm (m ℕ.* n) n ⟩
    n ℕ.+ m ℕ.* n ∎

-- Next in progression after splitAt and remQuot
finToFun : Fin (m ℕ.^ n) → (Fin n → Fin m)
finToFun {m = m} {n = suc n} i j with view j
... | zero    = quotient (m ℕ.^ n) i
... | (suc j) = finToFun (remainder {m} (m ℕ.^ n) i) j

-- inverse of above function
funToFin : (Fin m → Fin n) → Fin (n ℕ.^ m)
funToFin {zero}  f = fzero
funToFin {suc m} f = combine (f fzero) (funToFin (f ∘ fsuc))

------------------------------------------------------------------------
-- Operations

-- Folds.

fold : ∀ {t} (T : ℕ → Set t) {m} →
       (∀ {n} → T n → T (suc n)) →
       (∀ {n} → T (suc n)) →
       Fin m → T m
fold T f x k with view k
... | zero    = x
... | (suc i) = f (fold T f x i)

fold′ : ∀ {n t} (T : Fin (suc n) → Set t) →
        (∀ i → T (inject₁ i) → T (fsuc i)) →
        T fzero →
        ∀ i → T i
fold′ T f x k with view k
... | zero = x
fold′ {n = suc n} T f x k | (suc i)  =
  f i (fold′ (T ∘ inject₁) (f ∘ inject₁) x i)

-- Lifts functions.

lift : ∀ k → (Fin m → Fin n) → Fin (k ℕ.+ m) → Fin (k ℕ.+ n)
lift {n = n} k f i = [ _↑ˡ n , (k ↑ʳ_) ∘ f ]′ (splitAt k i)

-- "i" + "j" = "i + j".

infixl 6 _+_
_+_ : ∀ (i : Fin m) (j : Fin n) → Fin (toℕ i ℕ.+ n)
_+_ {m = m} {n = n} (i , i<m) (j , j<n)
  = i ℕ.+ j , (| (ℕₚ.+-monoʳ-< i) j<n |)

-- "i" - "j" = "i ∸ j".

infixl 6 _-_
_-_ : ∀ (i : Fin n) (j : Fin′ (fsuc i)) → Fin (n ℕ.∸ toℕ j)
(i , i<n) - (j , j<1+i)
  = i ℕ.∸ j
  , (| (λ i<n → ℕₚ.∸-monoˡ-< i<n ∘ ℕ.s≤s⁻¹) i<n j<1+i |)

-- m ℕ- "i" = "m ∸ i".

infixl 6 _ℕ-_
_ℕ-_ : (n : ℕ) (j : Fin (suc n)) → Fin (suc n ℕ.∸ toℕ j)
n ℕ- (j , j<1+n)
  = n ℕ.∸ j
  , (| (λ j<1+n → ℕₚ.≤-reflexive $ sym $ ℕₚ.∸-suc (ℕ.s≤s⁻¹ j<1+n)) j<1+n |)

-- m ℕ-ℕ "i" = m ∸ i.

infixl 6 _ℕ-ℕ_
_ℕ-ℕ_ : (n : ℕ) → Fin (suc n) → ℕ
n ℕ-ℕ (i , i<1+m) = n ℕ.∸ i

-- pred "i" = "pred i".

pred : Fin n → Fin n
pred (k , k<n) = ℕ.pred k , (| (ℕₚ.≤-<-trans ℕₚ.pred[n]≤n) k<n |)

-- opposite "i" = "pred n - i" (i.e. the additive inverse).

opposite : Fin n → Fin n
opposite {n} i@(k , prf)
  = n ℕ.∸ suc k
  , [ ℕₚ.m<n+o⇒m∸n<o n (suc k) {n} {{ nonZero i}} (ℕₚ.m<n+m n z<s) ]


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
