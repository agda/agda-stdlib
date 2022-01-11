------------------------------------------------------------------------
-- The Agda standard library
--
-- Proving that Fin m ↪ Fin n implies that m ≤ n.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Injection.injection-Fin where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function.Base
open import Data.Nat using (ℕ) renaming (suc to succ-ℕ; zero to zero-ℕ)
open import Data.Unit renaming (⊤ to unit; tt to star)
open import Data.Empty renaming (⊥ to empty)
open import Data.Sum.Base renaming (_⊎_ to coprod; inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality.Core
  renaming
    ( _≡_ to Id;
      sym to inv;
      trans to _∙_)
open import Relation.Binary.PropositionalEquality.Properties
  renaming
    ( cong-∘ to cong-comp)
open import Data.Product renaming (_,_ to pair; proj₁ to pr1; proj₂ to pr2)

module _
  {l : Level} {A : Set l}
  where
  
  concat : {x y : A} → Id x y → (z : A) → Id y z → Id x z
  concat p z q = p ∙ q
  
  assoc :
    {x y z w : A} (p : Id x y) (q : Id y z)
    (r : Id z w) → Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
  assoc refl q r = refl

  left-unit : {x y : A} {p : Id x y} → Id (refl ∙ p) p
  left-unit = refl

  right-unit : {x y : A} {p : Id x y} → Id (p ∙ refl) p
  right-unit {p = refl} = refl

  left-inv : {x y : A} (p : Id x y) → Id ((inv p) ∙ p) refl
  left-inv refl = refl

  right-inv : {x y : A} (p : Id x y) → Id (p ∙ (inv p)) refl
  right-inv refl = refl

tr :
  {i j : Level} {A : Set i} (B : A → Set j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

tr-concat :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} {x y z : A} (p : Id x y)
  (q : Id y z) (b : B x) → Id (tr B (p ∙ q) b) (tr B q (tr B p b))
tr-concat refl q b = refl

inv-con :
  {i : Level} {A : Set i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id q ((inv p) ∙ r)
inv-con refl q r = id 

con-inv :
  {i : Level} {A : Set i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id p (r ∙ (inv q))
con-inv p refl r =
  ( λ α → α ∙ (inv right-unit)) ∘ (concat (inv right-unit) r)

square :
  {l1 : Level} {A : Set l1} {x y1 y2 z : A}
  (p-left : Id x y1) (p-bottom : Id y1 z)
  (p-top : Id x y2) (p-right : Id y2 z) → Set l1
square p-left p-bottom p-top p-right = Id (p-left ∙ p-bottom) (p-top ∙ p-right)

is-injective : {l1 l2 : Level} {A : Set l1} {B : Set l2} → (A → B) → Set (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = ({x y : A} → Id (f x) (f y) → Id x y)

¬ : {l : Level} → Set l → Set l
¬ A = A → empty

is-empty : {l : Level} → Set l → Set l
is-empty = ¬

is-nonempty : {l : Level} → Set l → Set l
is-nonempty A = ¬ (is-empty A)

functor-neg : {l1 l2 : Level} {P : Set l1} {Q : Set l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

ex-falso : {l : Level} {A : Set l} → empty → A
ex-falso ()

terminal-map : {l : Level} {A : Set l} → A → unit
terminal-map a = star

one-ℕ : ℕ
one-ℕ = succ-ℕ zero-ℕ

two-ℕ : ℕ
two-ℕ = succ-ℕ one-ℕ

Eq-ℕ : ℕ → ℕ → Set lzero
Eq-ℕ zero-ℕ zero-ℕ = unit
Eq-ℕ zero-ℕ (succ-ℕ n) = empty
Eq-ℕ (succ-ℕ m) zero-ℕ = empty
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

Eq-eq-ℕ : {x y : ℕ} → Id x y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → Id x y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = cong succ-ℕ (eq-Eq-ℕ x y e)

is-zero-ℕ : ℕ → Set lzero
is-zero-ℕ n = Id n zero-ℕ

is-zero-ℕ' : ℕ → Set lzero
is-zero-ℕ' n = Id zero-ℕ n

is-successor-ℕ : ℕ → Set lzero
is-successor-ℕ n = Σ ℕ (λ y → Id n (succ-ℕ y))

is-nonzero-ℕ : ℕ → Set lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → Set lzero
is-one-ℕ n = Id n one-ℕ

is-one-ℕ' : ℕ → Set lzero
is-one-ℕ' n = Id one-ℕ n

is-not-one-ℕ : ℕ → Set lzero
is-not-one-ℕ n = ¬ (is-one-ℕ n)

is-not-one-ℕ' : ℕ → Set lzero
is-not-one-ℕ' n = ¬ (is-one-ℕ' n)

Peano-8 : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
Peano-8 x = Eq-eq-ℕ

is-nonzero-succ-ℕ : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
is-nonzero-succ-ℕ = Peano-8

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ {.succ-ℕ x} (pair x refl) = Peano-8 x

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
pr1 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = x
pr2 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = refl

is-nonzero-one-ℕ : is-nonzero-ℕ one-ℕ
is-nonzero-one-ℕ = Peano-8 zero-ℕ

is-not-one-zero-ℕ : is-not-one-ℕ zero-ℕ
is-not-one-zero-ℕ = is-nonzero-one-ℕ ∘ inv

is-not-one-two-ℕ : is-not-one-ℕ two-ℕ
is-not-one-two-ℕ = Eq-eq-ℕ

map-coprod :
  {l1 l2 l1' l2' : Level} {A : Set l1} {B : Set l2} {A' : Set l1'} {B' : Set l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
map-coprod f g (inl x) = inl (f x)
map-coprod f g (inr y) = inr (g y)

{- Definition 8.1.1 -}

is-decidable : {l : Level} (A : Set l) → Set l
is-decidable A = coprod A (¬ A)

is-decidable-fam :
  {l1 l2 : Level} {A : Set l1} (P : A → Set l2) → Set (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)

{- Example 8.1.2 -}

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

{- Example 8.1.3 -}

is-decidable-coprod :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} →
  is-decidable A → is-decidable B → is-decidable (coprod A B)
is-decidable-coprod (inl a) y = inl (inl a)
is-decidable-coprod (inr na) (inl b) = inl (inr b)
is-decidable-coprod (inr na) (inr nb) =
  inr (λ { (inl x) → na x ; (inr y) → nb y})

is-decidable-prod :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-prod (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-prod (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-function-type :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-neg :
  {l : Level} {A : Set l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty

{- Example 8.1.4 -}

leq-ℕ : ℕ → ℕ → Set lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ

data leq-ℕ' : ℕ → ℕ → Set lzero where
  refl-leq-ℕ' : (n : ℕ) → leq-ℕ' n n
  propagate-leq-ℕ' : {x y z : ℕ} → Id (succ-ℕ y) z → (leq-ℕ' x y) → (leq-ℕ' x z) 

-- Some trivialities that will be useful later

leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star

is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ x
is-zero-leq-zero-ℕ zero-ℕ star = refl

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ' x
is-zero-leq-zero-ℕ' zero-ℕ star = refl

succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → Id x' x → x ≤-ℕ y → Id y y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → Id n n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → Id m' m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H

decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ (succ-ℕ n) → coprod (m ≤-ℕ n) (Id m (succ-ℕ n))
decide-leq-succ-ℕ zero-ℕ zero-ℕ l = inl star
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = inl star
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l =
  inr (cong succ-ℕ (is-zero-leq-zero-ℕ m l))
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l =
  map-coprod id (cong succ-ℕ) (decide-leq-succ-ℕ m n l)

-- Exercise 6.3 (a)

refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

leq-eq-ℕ : (m n : ℕ) → Id m n → m ≤-ℕ n
leq-eq-ℕ m .m refl = refl-leq-ℕ m

transitive-leq-ℕ :
  (n m l : ℕ) → (n ≤-ℕ m) → (m ≤-ℕ l) → (n ≤-ℕ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q

preserves-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ (succ-ℕ n)
preserves-leq-succ-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) p (succ-leq-ℕ n)

antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → Id m n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  cong succ-ℕ (antisymmetric-leq-ℕ m n p q)

le-ℕ : ℕ → ℕ → Set lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ ()
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

preserves-le-succ-ℕ :
  (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)

anti-symmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → Id m n
anti-symmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  cong succ-ℕ (anti-symmetric-le-ℕ m n p q)

contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

contradiction-le-ℕ' : (m n : ℕ) → n ≤-ℕ m → ¬ (le-ℕ m n)
contradiction-le-ℕ' m n K H = contradiction-le-ℕ m n H K

leq-not-le-ℕ : (m n : ℕ) → ¬ (le-ℕ m n) → n ≤-ℕ m
leq-not-le-ℕ zero-ℕ zero-ℕ H = star
leq-not-le-ℕ zero-ℕ (succ-ℕ n) H = ex-falso (H star)
leq-not-le-ℕ (succ-ℕ m) zero-ℕ H = star
leq-not-le-ℕ (succ-ℕ m) (succ-ℕ n) H = leq-not-le-ℕ m n H

is-nonzero-le-ℕ : (m n : ℕ) → le-ℕ m n → is-nonzero-ℕ n
is-nonzero-le-ℕ m n H p = tr (le-ℕ m) p H

contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

contradiction-leq-ℕ' : (m n : ℕ) → (succ-ℕ n) ≤-ℕ m → ¬ (m ≤-ℕ n)
contradiction-leq-ℕ' m n K H = contradiction-leq-ℕ m n H K

leq-le-ℕ :
  {x y : ℕ} → le-ℕ x y → x ≤-ℕ y
leq-le-ℕ {zero-ℕ} {succ-ℕ y} H = star
leq-le-ℕ {succ-ℕ x} {succ-ℕ y} H = leq-le-ℕ {x} {y} H

concatenate-leq-le-ℕ :
  {x y z : ℕ} → x ≤-ℕ y → le-ℕ y z → le-ℕ x z
concatenate-leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-leq-le-ℕ {x} {y} {z} H K

concatenate-le-leq-ℕ :
  {x y z : ℕ} → le-ℕ x y → y ≤-ℕ z → le-ℕ x z
concatenate-le-leq-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-le-leq-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-le-leq-ℕ {x} {y} {z} H K

concatenate-eq-le-eq-ℕ :
  {x y z w : ℕ} → Id x y → le-ℕ y z → Id z w → le-ℕ x w
concatenate-eq-le-eq-ℕ refl p refl = p

concatenate-eq-le-ℕ :
  {x y z : ℕ} → Id x y → le-ℕ y z → le-ℕ x z
concatenate-eq-le-ℕ refl p = p

concatenate-le-eq-ℕ :
  {x y z : ℕ} → le-ℕ x y → Id y z → le-ℕ x z
concatenate-le-eq-ℕ p refl = p

le-succ-ℕ : {x : ℕ} → le-ℕ x (succ-ℕ x)
le-succ-ℕ {zero-ℕ} = star
le-succ-ℕ {succ-ℕ x} = le-succ-ℕ {x}

le-leq-neq-ℕ : {x y : ℕ} → x ≤-ℕ y → ¬ (Id x y) → le-ℕ x y
le-leq-neq-ℕ {zero-ℕ} {zero-ℕ} l f = ex-falso (f refl)
le-leq-neq-ℕ {zero-ℕ} {succ-ℕ y} l f = star
le-leq-neq-ℕ {succ-ℕ x} {succ-ℕ y} l f =
  le-leq-neq-ℕ {x} {y} l (λ p → f (cong succ-ℕ p))

linear-le-ℕ : (x y : ℕ) → coprod (le-ℕ x y) (coprod (Id x y) (le-ℕ y x))
linear-le-ℕ zero-ℕ zero-ℕ = inr (inl refl)
linear-le-ℕ zero-ℕ (succ-ℕ y) = inl star
linear-le-ℕ (succ-ℕ x) zero-ℕ = inr (inr star)
linear-le-ℕ (succ-ℕ x) (succ-ℕ y) =
  map-coprod id (map-coprod (cong succ-ℕ) id) (linear-le-ℕ x y)

-- Exercise 6.3 (b)

decide-leq-ℕ :
  (m n : ℕ) → coprod (m ≤-ℕ n) (n ≤-ℕ m)
decide-leq-ℕ zero-ℕ zero-ℕ = inl star
decide-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
decide-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) = decide-leq-ℕ m n

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n

{- Definition 8.1.5 -}
   
has-decidable-equality : {l : Level} (A : Set l) → Set l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

{- Proposition 8.1.6 -}

is-decidable-iff :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  map-coprod f (functor-neg g)

{- Proposition 8.1.7 -}

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

-- We record some immediate corollaries

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n one-ℕ

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ one-ℕ n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)

{- Proposition 8.1.8 -}

-- Bureaucracy

has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

_~_ :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → Id (f x) (g x)

refl-htpy :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

inv-htpy :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
inv-htpy H x = inv (H x)

_∙h_ :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

htpy-left-whisk :
  {i j k : Level} {A : Set i} {B : Set j} {C : Set k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = cong h (H x)

_·l_ = htpy-left-whisk

-- Definition 9.1.7 (ii)

htpy-right-whisk :
  {i j k : Level} {A : Set i} {B : Set j} {C : Set k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

sq-left-whisk :
  {i : Level} {A : Set i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : Set i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where
  
  -- Definition 9.2.1 (i)

  sec : (f : A → B) → Set (l1 ⊔ l2)
  sec f = Σ (B → A) (λ g → (f ∘ g) ~ id)

  -- Definition 9.2.1 (ii)
  
  retr : (f : A → B) → Set (l1 ⊔ l2)
  retr f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → Set i → Set j → Set (i ⊔ j)
A retract-of B = Σ (A → B) retr

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where
  
  section-retract-of : A retract-of B → A → B
  section-retract-of = pr1

  retr-section-retract-of : (R : A retract-of B) → retr (section-retract-of R)
  retr-section-retract-of = pr2

  retraction-retract-of : (A retract-of B) → B → A
  retraction-retract-of R = pr1 (retr-section-retract-of R)

  is-retr-retraction-retract-of :
    (R : A retract-of B) →
    (retraction-retract-of R ∘ section-retract-of R) ~ id
  is-retr-retraction-retract-of R = pr2 (retr-section-retract-of R)

  -- Definition 9.2.1 (ii)
  
  is-equiv : (A → B) → Set (l1 ⊔ l2)
  is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : Set i) (B : Set j) → Set (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

module _
  {l : Level} {A : Set l}
  where

  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = id
  pr2 (pr1 is-equiv-id) = refl-htpy
  pr1 (pr2 is-equiv-id) = id
  pr2 (pr2 is-equiv-id) = refl-htpy
  
  id-equiv : A ≃ A
  pr1 id-equiv = id
  pr2 id-equiv = is-equiv-id

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  map-equiv : (A ≃ B) → (A → B)
  map-equiv e = pr1 e

  is-equiv-map-equiv : (e : A ≃ B) → is-equiv (map-equiv e)
  is-equiv-map-equiv e = pr2 e

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  has-inverse : (A → B) → Set (l1 ⊔ l2)
  has-inverse f = Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

-- Proposition 9.2.7

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
  where

  is-equiv-has-inverse' : has-inverse f → is-equiv f
  pr1 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = g
  pr2 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = H
  pr1 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = g
  pr2 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = K

  is-equiv-has-inverse :
    (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
  is-equiv-has-inverse g H K =
    is-equiv-has-inverse' (pair g (pair H K))

  -- Corollary 9.2.8

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
  where
  
  htpy-section-retraction : (H : is-equiv f) → ((pr1 (pr1 H))) ~ (pr1 (pr2 H))
  htpy-section-retraction (pair (pair g G) (pair h H)) =
    (inv-htpy (H ·r g)) ∙h (h ·l G)

  has-inverse-is-equiv : is-equiv f → has-inverse f
  pr1 (has-inverse-is-equiv  (pair (pair g G) (pair h H))) = g
  pr1 (pr2 (has-inverse-is-equiv (pair (pair g G) (pair h H)))) = G
  pr2 (pr2 (has-inverse-is-equiv (pair (pair g G) (pair h H)))) =
    (((inv-htpy (H ·r g)) ∙h (h ·l G)) ·r f) ∙h H

  map-inv-is-equiv : is-equiv f → B → A
  map-inv-is-equiv H = pr1 (has-inverse-is-equiv H)

  issec-map-inv-is-equiv' :
    (H : is-equiv f) → (f ∘ (map-inv-is-equiv H)) ~ id
  issec-map-inv-is-equiv' H = pr1 (pr2 (has-inverse-is-equiv H))

  isretr-map-inv-is-equiv' :
    (H : is-equiv f) → ((map-inv-is-equiv H) ∘ f) ~ id
  isretr-map-inv-is-equiv' H = pr2 (pr2 (has-inverse-is-equiv H))

  is-equiv-map-inv-is-equiv : (H : is-equiv f) → is-equiv (map-inv-is-equiv H)
  is-equiv-map-inv-is-equiv H =
    is-equiv-has-inverse f
      ( isretr-map-inv-is-equiv' H)
      ( issec-map-inv-is-equiv' H)

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (e : A ≃ B)
  where

  map-inv-equiv' : (B → A)
  map-inv-equiv' = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv' : (map-equiv e ∘ map-inv-equiv') ~ id
  issec-map-inv-equiv' = issec-map-inv-is-equiv' (is-equiv-map-equiv e)

  isretr-map-inv-equiv' : (map-inv-equiv' ∘ map-equiv e) ~ id
  isretr-map-inv-equiv' = isretr-map-inv-is-equiv' (is-equiv-map-equiv e)

  is-equiv-map-inv-equiv : is-equiv map-inv-equiv'
  is-equiv-map-inv-equiv = is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

  inv-equiv : (B ≃ A)
  pr1 inv-equiv = map-inv-equiv'
  pr2 inv-equiv = is-equiv-map-inv-equiv

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {X : Set l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  -- Exercise 9.4(a)
  
  {- Exercise 9.4 (a) asks to show that, given a commuting triangle f ~ g ∘ h 
     and a section s of h, we get a new commuting triangle g ~ f ∘ s. Moreover, 
     under the same assumptions it follows that f has a section if and only if g
     has a section. -}

  triangle-section : (S : sec h) → g ~ (f ∘ (pr1 S))
  triangle-section (pair s issec) = inv-htpy ((H ·r s) ∙h (g ·l issec))

  section-comp : sec h → sec f → sec g
  pr1 (section-comp sec-h sec-f) = h ∘ (pr1 sec-f)
  pr2 (section-comp sec-h sec-f) = (inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f)
  
  section-comp' : sec h → sec g → sec f
  pr1 (section-comp' sec-h sec-g) = (pr1 sec-h) ∘ (pr1 sec-g)
  pr2 (section-comp' sec-h sec-g) =
    ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
    ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g)))

  -- Exercise 9.4(b)
  
  {- Exercise 9.4 (b) is dual to exercise 9.4 (a). It asks to show that, given a
     commuting triangle f ~ g ∘ h and a retraction r of g, we get a new 
     commuting triangle h ~ r ∘ f. Moreover, under these assumptions it also 
     follows that f has a retraction if and only if h has a retraction. -}

  triangle-retraction : (R : retr g) → h ~ ((pr1 R) ∘ f)
  triangle-retraction (pair r isretr) = inv-htpy ((r ·l H) ∙h (isretr ·r h))

  retraction-comp : retr g → retr f → retr h
  pr1 (retraction-comp retr-g retr-f) = (pr1 retr-f) ∘ g
  pr2 (retraction-comp retr-g retr-f) =
    (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f)

  retraction-comp' : retr g → retr h → retr f
  pr1 (retraction-comp' retr-g retr-h) = (pr1 retr-h) ∘ (pr1 retr-g)
  pr2 (retraction-comp' retr-g retr-h) =
    ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
    ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h))

  -- Exercise 9.4(c)
  
  {- In Exercise 9.4 (c) we use the constructions of parts (a) and (b) to derive
     the 3-for-2 property of equivalences. -}

  abstract
    is-equiv-comp : is-equiv h → is-equiv g → is-equiv f
    pr1 (is-equiv-comp (pair sec-h retr-h) (pair sec-g retr-g)) =
      section-comp' sec-h sec-g
    pr2 (is-equiv-comp (pair sec-h retr-h) (pair sec-g retr-g)) =
      retraction-comp' retr-g retr-h

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {X : Set l3}
  where

  abstract
    is-equiv-comp' :
      (g : B → X) (h : A → B) → is-equiv h → is-equiv g → is-equiv (g ∘ h)
    is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

  equiv-comp : (B ≃ X) → (A ≃ B) → (A ≃ X)
  pr1 (equiv-comp g h) = (pr1 g) ∘ (pr1 h)
  pr2 (equiv-comp g h) = is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g)

  _∘e_ : (B ≃ X) → (A ≃ B) → (A ≃ X)
  _∘e_ = equiv-comp

abstract
  is-equiv-left-factor :
    {i j k : Level} {A : Set i} {B : Set j} {X : Set k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv f → is-equiv h → is-equiv g
  pr1
    ( is-equiv-left-factor f g h H
      ( pair sec-f retr-f)
      ( pair (pair sh sh-issec) retr-h)) =
    section-comp f g h H (pair sh sh-issec) sec-f
  pr2
    ( is-equiv-left-factor f g h H
      ( pair sec-f retr-f)
      ( pair (pair sh sh-issec) retr-h)) =
    retraction-comp' g f sh
      ( triangle-section f g h H (pair sh sh-issec))
      ( retr-f)
      ( pair h sh-issec)

abstract
  is-equiv-left-factor' :
    {i j k : Level} {A : Set i} {B : Set j} {X : Set k} (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor' g h =
    is-equiv-left-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-right-factor :
    {i j k : Level} {A : Set i} {B : Set j} {X : Set k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv g → is-equiv f → is-equiv h
  pr1
    ( is-equiv-right-factor f g h H
      ( pair sec-g (pair rg rg-isretr))
      ( pair sec-f retr-f)) =
    section-comp' h rg f
      ( triangle-retraction f g h H (pair rg rg-isretr))
      ( sec-f)
      ( pair g rg-isretr)
  pr2
    ( is-equiv-right-factor f g h H
      ( pair sec-g (pair rg rg-isretr))
      ( pair sec-f retr-f)) =
    retraction-comp f g h H (pair rg rg-isretr) retr-f

module _
  {l : Level} {A : Set l}
  where

  {- We show that inv is an equivalence. -}
  
  inv-inv : {x y : A} (p : Id x y) → Id (inv (inv p)) p
  inv-inv refl = refl

  abstract
    is-equiv-inv : (x y : A) → is-equiv (λ (p : Id x y) → inv p)
    is-equiv-inv x y = is-equiv-has-inverse inv inv-inv inv-inv

  equiv-inv : (x y : A) → (Id x y) ≃ (Id y x)
  pr1 (equiv-inv x y) = inv
  pr2 (equiv-inv x y) = is-equiv-inv x y

  {- We show that concat p is an equivalence, for any path p. -}
  
  inv-concat : {x y : A} (p : Id x y) (z : A) → Id x z → Id y z
  inv-concat p = concat (inv p)

  isretr-inv-concat :
    {x y : A} (p : Id x y) (z : A) → (inv-concat p z ∘ concat p z) ~ id
  isretr-inv-concat refl z q = refl

  issec-inv-concat :
    {x y : A} (p : Id x y) (z : A) → (concat p z ∘ inv-concat p z) ~ id
  issec-inv-concat refl z refl = refl

  abstract
    is-equiv-concat :
      {x y : A} (p : Id x y) (z : A) → is-equiv (concat p z)
    is-equiv-concat p z =
      is-equiv-has-inverse
        ( inv-concat p z)
        ( issec-inv-concat p z)
        ( isretr-inv-concat p z)

  equiv-concat :
    {x y : A} (p : Id x y) (z : A) → Id y z ≃ Id x z
  pr1 (equiv-concat p z) = concat p z
  pr2 (equiv-concat p z) = is-equiv-concat p z

  {- We show that concat' q is an equivalence, for any path q. -}
  
  concat' : (x : A) {y z : A} → Id y z → Id x y → Id x z
  concat' x q p = p ∙ q
  
  inv-concat' : (x : A) {y z : A} → Id y z → Id x z → Id x y
  inv-concat' x q = concat' x (inv q)

  isretr-inv-concat' :
    (x : A) {y z : A} (q : Id y z) → (inv-concat' x q ∘ concat' x q) ~ id
  isretr-inv-concat' x refl refl = refl

  issec-inv-concat' :
    (x : A) {y z : A} (q : Id y z) → (concat' x q ∘ inv-concat' x q) ~ id
  issec-inv-concat' x refl refl = refl

  abstract
    is-equiv-concat' :
      (x : A) {y z : A} (q : Id y z) → is-equiv (concat' x q)
    is-equiv-concat' x q =
      is-equiv-has-inverse
        ( inv-concat' x q)
        ( issec-inv-concat' x q)
        ( isretr-inv-concat' x q)
  
  equiv-concat' :
    (x : A) {y z : A} (q : Id y z) → Id x y ≃ Id x z
  pr1 (equiv-concat' x q) = concat' x q
  pr2 (equiv-concat' x q) = is-equiv-concat' x q

abstract
  is-equiv-right-factor' :
    {i j k : Level} {A : Set i} {B : Set j} {X : Set k} (g : B → X) (h : A → B) → 
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor' g h =
    is-equiv-right-factor (g ∘ h) g h refl-htpy


-- Equivalences are injective

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-injective-is-equiv : {f : A → B} → is-equiv f → is-injective f
    is-injective-is-equiv H {x} {y} p =
      ( inv (isretr-map-inv-is-equiv' H x)) ∙
      ( ( cong (map-inv-is-equiv H) p) ∙
        ( isretr-map-inv-is-equiv' H y))

  abstract
    is-injective-map-equiv : (e : A ≃ B) → is-injective (map-equiv e)
    is-injective-map-equiv (pair f H) = is-injective-is-equiv H

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where
  
  abstract
    is-injective-map-inv-equiv : (e : A ≃ B) → is-injective (map-inv-equiv' e)
    is-injective-map-inv-equiv e =
      is-injective-is-equiv (is-equiv-map-inv-equiv e)

  is-equiv-is-injective : {f : A → B} → sec f → is-injective f → is-equiv f
  is-equiv-is-injective {f} (pair g G) H =
    is-equiv-has-inverse g G (λ x → H (G (f x)))

-- Left unit law of coproducts

map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → is-empty B → coprod A B → A
map-right-unit-law-coprod-is-empty A B nb (inl a) = a
map-right-unit-law-coprod-is-empty A B nb (inr b) = ex-falso (nb b)

map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → is-empty A → coprod A B → B
map-left-unit-law-coprod-is-empty A B na (inl a) = ex-falso (na a)
map-left-unit-law-coprod-is-empty A B na (inr b) = b

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2) (H : is-empty A)
  where

  map-inv-left-unit-law-coprod-is-empty : B → coprod A B
  map-inv-left-unit-law-coprod-is-empty = inr

  issec-map-inv-left-unit-law-coprod-is-empty :
    ( map-left-unit-law-coprod-is-empty A B H ∘
      map-inv-left-unit-law-coprod-is-empty) ~ id
  issec-map-inv-left-unit-law-coprod-is-empty = refl-htpy

  isretr-map-inv-left-unit-law-coprod-is-empty :
    ( map-inv-left-unit-law-coprod-is-empty ∘
      map-left-unit-law-coprod-is-empty A B H) ~ id
  isretr-map-inv-left-unit-law-coprod-is-empty (inl a) = ex-falso (H a)
  isretr-map-inv-left-unit-law-coprod-is-empty (inr b) = refl

  is-equiv-map-left-unit-law-coprod-is-empty :
    is-equiv (map-left-unit-law-coprod-is-empty A B H)
  is-equiv-map-left-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      map-inv-left-unit-law-coprod-is-empty
      issec-map-inv-left-unit-law-coprod-is-empty
      isretr-map-inv-left-unit-law-coprod-is-empty

  left-unit-law-coprod-is-empty : coprod A B ≃ B
  pr1 left-unit-law-coprod-is-empty = map-left-unit-law-coprod-is-empty A B H
  pr2 left-unit-law-coprod-is-empty = is-equiv-map-left-unit-law-coprod-is-empty

  inv-left-unit-law-coprod-is-empty : B ≃ coprod A B
  pr1 inv-left-unit-law-coprod-is-empty = map-inv-left-unit-law-coprod-is-empty
  pr2 inv-left-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      ( map-left-unit-law-coprod-is-empty A B H)
      ( isretr-map-inv-left-unit-law-coprod-is-empty)
      ( issec-map-inv-left-unit-law-coprod-is-empty)

module _
  {l : Level} (B : Set l)
  where

  map-left-unit-law-coprod : coprod empty B → B
  map-left-unit-law-coprod = map-left-unit-law-coprod-is-empty empty B id

  map-inv-left-unit-law-coprod : B → coprod empty B
  map-inv-left-unit-law-coprod = inr

  issec-map-inv-left-unit-law-coprod :
    ( map-left-unit-law-coprod ∘ map-inv-left-unit-law-coprod) ~ id
  issec-map-inv-left-unit-law-coprod =
    issec-map-inv-left-unit-law-coprod-is-empty empty B id

  isretr-map-inv-left-unit-law-coprod :
    ( map-inv-left-unit-law-coprod ∘ map-left-unit-law-coprod) ~ id
  isretr-map-inv-left-unit-law-coprod =
    isretr-map-inv-left-unit-law-coprod-is-empty empty B id

  is-equiv-map-left-unit-law-coprod : is-equiv map-left-unit-law-coprod
  is-equiv-map-left-unit-law-coprod =
    is-equiv-map-left-unit-law-coprod-is-empty empty B id
  
  left-unit-law-coprod : coprod empty B ≃ B
  left-unit-law-coprod = left-unit-law-coprod-is-empty empty B id

  inv-left-unit-law-coprod : B ≃ (coprod empty B)
  inv-left-unit-law-coprod = inv-left-unit-law-coprod-is-empty empty B id

-- The right unit law for coproducts

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2) (H : is-empty B)
  where
  
  map-inv-right-unit-law-coprod-is-empty : A → coprod A B
  map-inv-right-unit-law-coprod-is-empty = inl

  issec-map-inv-right-unit-law-coprod-is-empty :
    ( map-right-unit-law-coprod-is-empty A B H ∘
      map-inv-right-unit-law-coprod-is-empty) ~ id
  issec-map-inv-right-unit-law-coprod-is-empty a = refl

  isretr-map-inv-right-unit-law-coprod-is-empty :
    ( map-inv-right-unit-law-coprod-is-empty ∘
      map-right-unit-law-coprod-is-empty A B H) ~ id
  isretr-map-inv-right-unit-law-coprod-is-empty (inl a) = refl
  isretr-map-inv-right-unit-law-coprod-is-empty (inr b) = ex-falso (H b)

  is-equiv-map-right-unit-law-coprod-is-empty :
    is-equiv (map-right-unit-law-coprod-is-empty A B H)
  is-equiv-map-right-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      map-inv-right-unit-law-coprod-is-empty
      issec-map-inv-right-unit-law-coprod-is-empty
      isretr-map-inv-right-unit-law-coprod-is-empty

  is-equiv-inl-is-empty : is-equiv (inl {l1} {l2} {A} {B})
  is-equiv-inl-is-empty =
    is-equiv-has-inverse
      ( map-right-unit-law-coprod-is-empty A B H)
      ( isretr-map-inv-right-unit-law-coprod-is-empty)
      ( issec-map-inv-right-unit-law-coprod-is-empty)

  right-unit-law-coprod-is-empty : coprod A B ≃ A
  pr1 right-unit-law-coprod-is-empty = map-right-unit-law-coprod-is-empty A B H
  pr2 right-unit-law-coprod-is-empty =
    is-equiv-map-right-unit-law-coprod-is-empty

  inv-right-unit-law-coprod-is-empty : A ≃ (coprod A B)
  pr1 inv-right-unit-law-coprod-is-empty = inl
  pr2 inv-right-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      ( map-right-unit-law-coprod-is-empty A B H)
      ( isretr-map-inv-right-unit-law-coprod-is-empty)
      ( issec-map-inv-right-unit-law-coprod-is-empty)

module _
  {l : Level} (A : Set l)
  where

  map-right-unit-law-coprod : coprod A empty → A
  map-right-unit-law-coprod = map-right-unit-law-coprod-is-empty A empty id

  map-inv-right-unit-law-coprod : A → coprod A empty
  map-inv-right-unit-law-coprod = inl

  issec-map-inv-right-unit-law-coprod :
    ( map-right-unit-law-coprod ∘ map-inv-right-unit-law-coprod) ~ id
  issec-map-inv-right-unit-law-coprod =
    issec-map-inv-right-unit-law-coprod-is-empty A empty id

  isretr-map-inv-right-unit-law-coprod :
    ( map-inv-right-unit-law-coprod ∘ map-right-unit-law-coprod) ~ id
  isretr-map-inv-right-unit-law-coprod =
    isretr-map-inv-right-unit-law-coprod-is-empty A empty id

  is-equiv-map-right-unit-law-coprod : is-equiv map-right-unit-law-coprod
  is-equiv-map-right-unit-law-coprod =
    is-equiv-map-right-unit-law-coprod-is-empty A empty id

  right-unit-law-coprod : coprod A empty ≃ A
  right-unit-law-coprod = right-unit-law-coprod-is-empty A empty id

  inv-right-unit-law-coprod : A ≃ coprod A empty
  inv-right-unit-law-coprod =
    inv-right-unit-law-coprod-is-empty A empty id

-- Commutativity of coproducts

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  map-commutative-coprod : coprod A B → coprod B A
  map-commutative-coprod (inl a) = inr a
  map-commutative-coprod (inr b) = inl b
  
  map-inv-commutative-coprod : coprod B A → coprod A B
  map-inv-commutative-coprod (inl b) = inr b
  map-inv-commutative-coprod (inr a) = inl a
  
  issec-map-inv-commutative-coprod :
    ( map-commutative-coprod ∘ map-inv-commutative-coprod) ~ id
  issec-map-inv-commutative-coprod (inl b) = refl
  issec-map-inv-commutative-coprod (inr a) = refl
  
  isretr-map-inv-commutative-coprod :
    ( map-inv-commutative-coprod ∘ map-commutative-coprod) ~ id
  isretr-map-inv-commutative-coprod (inl a) = refl
  isretr-map-inv-commutative-coprod (inr b) = refl

  is-equiv-map-commutative-coprod : is-equiv map-commutative-coprod
  is-equiv-map-commutative-coprod =
    is-equiv-has-inverse
      map-inv-commutative-coprod
      issec-map-inv-commutative-coprod
      isretr-map-inv-commutative-coprod

-- Associativity of coproducts

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
  where
  
  map-assoc-coprod : coprod (coprod A B) C → coprod A (coprod B C)
  map-assoc-coprod (inl (inl x)) = inl x
  map-assoc-coprod (inl (inr x)) = inr (inl x)
  map-assoc-coprod (inr x) = inr (inr x)

  map-inv-assoc-coprod : coprod A (coprod B C) → coprod (coprod A B) C
  map-inv-assoc-coprod (inl x) = inl (inl x)
  map-inv-assoc-coprod (inr (inl x)) = inl (inr x)
  map-inv-assoc-coprod (inr (inr x)) = inr x

  issec-map-inv-assoc-coprod : (map-assoc-coprod ∘ map-inv-assoc-coprod) ~ id
  issec-map-inv-assoc-coprod (inl x) = refl
  issec-map-inv-assoc-coprod (inr (inl x)) = refl
  issec-map-inv-assoc-coprod (inr (inr x)) = refl

  isretr-map-inv-assoc-coprod : (map-inv-assoc-coprod ∘ map-assoc-coprod) ~ id
  isretr-map-inv-assoc-coprod (inl (inl x)) = refl
  isretr-map-inv-assoc-coprod (inl (inr x)) = refl
  isretr-map-inv-assoc-coprod (inr x) = refl

  is-equiv-map-assoc-coprod : is-equiv map-assoc-coprod
  is-equiv-map-assoc-coprod =
    is-equiv-has-inverse
      map-inv-assoc-coprod
      issec-map-inv-assoc-coprod
      isretr-map-inv-assoc-coprod

  is-equiv-map-inv-assoc-coprod : is-equiv map-inv-assoc-coprod
  is-equiv-map-inv-assoc-coprod =
    is-equiv-has-inverse
      map-assoc-coprod
      isretr-map-inv-assoc-coprod
      issec-map-inv-assoc-coprod

  assoc-coprod : coprod (coprod A B) C ≃ coprod A (coprod B C)
  pr1 assoc-coprod = map-assoc-coprod
  pr2 assoc-coprod = is-equiv-map-assoc-coprod
  
  inv-assoc-coprod : coprod A (coprod B C) ≃ coprod (coprod A B) C
  pr1 inv-assoc-coprod = map-inv-assoc-coprod
  pr2 inv-assoc-coprod = is-equiv-map-inv-assoc-coprod

{- We prove a left zero law for cartesian products. -}

module _
  {l : Level} (X : Set l)
  where

  inv-pr1-prod-empty : empty → empty × X
  inv-pr1-prod-empty ()

  issec-inv-pr1-prod-empty : (pr1 ∘ inv-pr1-prod-empty) ~ id
  issec-inv-pr1-prod-empty ()

  isretr-inv-pr1-prod-empty : (inv-pr1-prod-empty ∘ pr1) ~ id
  isretr-inv-pr1-prod-empty (pair () x)

  is-equiv-pr1-prod-empty : is-equiv (pr1 {A = empty} {B = λ t → X})
  is-equiv-pr1-prod-empty =
    is-equiv-has-inverse
      inv-pr1-prod-empty
      issec-inv-pr1-prod-empty
      isretr-inv-pr1-prod-empty

  left-zero-law-prod : (empty × X) ≃ empty
  pr1 left-zero-law-prod = pr1
  pr2 left-zero-law-prod = is-equiv-pr1-prod-empty

{- We prove the right zero law for cartesian products. -}

module _
  {l : Level} (X : Set l)
  where

  inv-pr2-prod-empty : empty → (X × empty)
  inv-pr2-prod-empty ()

  issec-inv-pr2-prod-empty : (pr2 ∘ inv-pr2-prod-empty) ~ id
  issec-inv-pr2-prod-empty ()

  isretr-inv-pr2-prod-empty : (inv-pr2-prod-empty ∘ pr2) ~ id
  isretr-inv-pr2-prod-empty (pair x ())

  is-equiv-pr2-prod-empty : is-equiv (pr2 {A = X} {B = λ x → empty})
  is-equiv-pr2-prod-empty =
    is-equiv-has-inverse
      inv-pr2-prod-empty
      issec-inv-pr2-prod-empty
      isretr-inv-pr2-prod-empty

  right-zero-law-prod : (X × empty) ≃ empty
  pr1 right-zero-law-prod = pr2
  pr2 right-zero-law-prod = is-equiv-pr2-prod-empty

-- Right absorption law for Σ-types and cartesian products

abstract
  is-equiv-is-empty :
    {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) →
    is-empty B → is-equiv f
  is-equiv-is-empty f H =
    is-equiv-has-inverse
      ( ex-falso ∘ H)
      ( λ y → ex-falso (H y))
      ( λ x → ex-falso (H (f x)))

abstract
  is-equiv-is-empty' :
    {l : Level} {A : Set l} (f : is-empty A) → is-equiv f
  is-equiv-is-empty' f = is-equiv-is-empty f id

module _
  {l : Level} (A : Set l)
  where
  
  map-right-absorption-Σ : Σ A (λ x → empty) → empty
  map-right-absorption-Σ (pair x ())
  
  map-right-absorption-prod : A × empty → empty
  map-right-absorption-prod = map-right-absorption-Σ

  is-equiv-map-right-absorption-Σ : is-equiv map-right-absorption-Σ
  is-equiv-map-right-absorption-Σ = is-equiv-is-empty' map-right-absorption-Σ

  is-equiv-map-right-absorption-prod : is-equiv map-right-absorption-prod
  is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ
  
  right-absorption-Σ : Σ A (λ x → empty) ≃ empty
  right-absorption-Σ =
    pair map-right-absorption-Σ is-equiv-map-right-absorption-Σ
  
  right-absorption-prod : (A × empty) ≃ empty
  right-absorption-prod = right-absorption-Σ

-- Left absorption law for Σ and cartesian products

module _
  {l : Level} (A : empty → Set l)
  where

  map-left-absorption-Σ : Σ empty A → empty
  map-left-absorption-Σ = pr1
  
  is-equiv-map-left-absorption-Σ : is-equiv map-left-absorption-Σ
  is-equiv-map-left-absorption-Σ =
    is-equiv-is-empty' map-left-absorption-Σ
  
  left-absorption-Σ : Σ empty A ≃ empty
  pr1 left-absorption-Σ = map-left-absorption-Σ
  pr2 left-absorption-Σ = is-equiv-map-left-absorption-Σ
  
-- Unit laws for Σ-types and cartesian products

module _
  {l : Level} (A : unit → Set l)
  where

  map-left-unit-law-Σ : Σ unit A → A star
  map-left-unit-law-Σ (pair star a) = a

  map-inv-left-unit-law-Σ : A star → Σ unit A
  pr1 (map-inv-left-unit-law-Σ a) = star
  pr2 (map-inv-left-unit-law-Σ a) = a

  issec-map-inv-left-unit-law-Σ :
    ( map-left-unit-law-Σ ∘ map-inv-left-unit-law-Σ) ~ id
  issec-map-inv-left-unit-law-Σ a = refl

  isretr-map-inv-left-unit-law-Σ :
    ( map-inv-left-unit-law-Σ ∘ map-left-unit-law-Σ) ~ id
  isretr-map-inv-left-unit-law-Σ (pair star a) = refl

  is-equiv-map-left-unit-law-Σ : is-equiv map-left-unit-law-Σ
  is-equiv-map-left-unit-law-Σ =
    is-equiv-has-inverse
      map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ

  left-unit-law-Σ : Σ unit A ≃ A star
  pr1 left-unit-law-Σ = map-left-unit-law-Σ
  pr2 left-unit-law-Σ = is-equiv-map-left-unit-law-Σ
  
  is-equiv-map-inv-left-unit-law-Σ : is-equiv map-inv-left-unit-law-Σ
  is-equiv-map-inv-left-unit-law-Σ =
    is-equiv-has-inverse
      map-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ

  inv-left-unit-law-Σ : A star ≃ Σ unit A
  pr1 inv-left-unit-law-Σ = map-inv-left-unit-law-Σ
  pr2 inv-left-unit-law-Σ = is-equiv-map-inv-left-unit-law-Σ

module _
  {l1 l2 l3 : Level} (A : Set l1) (B : Set l2) (C : coprod A B → Set l3)
  where
  
  map-right-distributive-Σ-coprod :
    Σ (coprod A B) C → coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
  map-right-distributive-Σ-coprod (pair (inl x) z) = inl (pair x z)
  map-right-distributive-Σ-coprod (pair (inr y) z) = inr (pair y z)

  map-inv-right-distributive-Σ-coprod :
    coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
  pr1 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = inl x
  pr2 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = z
  pr1 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = inr y
  pr2 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = z

  issec-map-inv-right-distributive-Σ-coprod :
    ( map-right-distributive-Σ-coprod ∘ map-inv-right-distributive-Σ-coprod) ~
    ( id)
  issec-map-inv-right-distributive-Σ-coprod (inl (pair x z)) = refl
  issec-map-inv-right-distributive-Σ-coprod (inr (pair y z)) = refl

  isretr-map-inv-right-distributive-Σ-coprod :
    ( map-inv-right-distributive-Σ-coprod ∘ map-right-distributive-Σ-coprod) ~
    ( id)
  isretr-map-inv-right-distributive-Σ-coprod (pair (inl x) z) = refl
  isretr-map-inv-right-distributive-Σ-coprod (pair (inr y) z) = refl

  abstract
    is-equiv-map-right-distributive-Σ-coprod :
      is-equiv map-right-distributive-Σ-coprod
    is-equiv-map-right-distributive-Σ-coprod =
      is-equiv-has-inverse
        map-inv-right-distributive-Σ-coprod
        issec-map-inv-right-distributive-Σ-coprod
        isretr-map-inv-right-distributive-Σ-coprod

  right-distributive-Σ-coprod :
    Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
  pr1 right-distributive-Σ-coprod = map-right-distributive-Σ-coprod
  pr2 right-distributive-Σ-coprod = is-equiv-map-right-distributive-Σ-coprod

-- Left distributivity of Σ over coproducts

module _
  {l1 l2 l3 : Level} (A : Set l1) (B : A → Set l2) (C : A → Set l3)
  where

  map-left-distributive-Σ-coprod :
    Σ A (λ x → coprod (B x) (C x)) → coprod (Σ A B) (Σ A C)
  map-left-distributive-Σ-coprod (pair x (inl y)) = inl (pair x y)
  map-left-distributive-Σ-coprod (pair x (inr z)) = inr (pair x z)

  map-inv-left-distributive-Σ-coprod :
    coprod (Σ A B) (Σ A C) → Σ A (λ x → coprod (B x) (C x))
  pr1 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = inl y
  pr1 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = inr z

  issec-map-inv-left-distributive-Σ-coprod :
    ( map-left-distributive-Σ-coprod ∘ map-inv-left-distributive-Σ-coprod) ~ id
  issec-map-inv-left-distributive-Σ-coprod (inl (pair x y)) = refl
  issec-map-inv-left-distributive-Σ-coprod (inr (pair x z)) = refl

  isretr-map-inv-left-distributive-Σ-coprod :
    ( map-inv-left-distributive-Σ-coprod ∘ map-left-distributive-Σ-coprod) ~ id
  isretr-map-inv-left-distributive-Σ-coprod (pair x (inl y)) = refl
  isretr-map-inv-left-distributive-Σ-coprod (pair x (inr z)) = refl

  is-equiv-map-left-distributive-Σ-coprod :
    is-equiv map-left-distributive-Σ-coprod
  is-equiv-map-left-distributive-Σ-coprod =
    is-equiv-has-inverse
      map-inv-left-distributive-Σ-coprod
      issec-map-inv-left-distributive-Σ-coprod
      isretr-map-inv-left-distributive-Σ-coprod

  left-distributive-Σ-coprod :
    Σ A (λ x → coprod (B x) (C x)) ≃ coprod (Σ A B) (Σ A C)
  pr1 left-distributive-Σ-coprod = map-left-distributive-Σ-coprod
  pr2 left-distributive-Σ-coprod = is-equiv-map-left-distributive-Σ-coprod

-- Right distributivity of products over coproducts

module _
  {l1 l2 l3 : Level} (A : Set l1) (B : Set l2) (C : Set l3)
  where

  map-right-distributive-prod-coprod : (coprod A B) × C → coprod (A × C) (B × C)
  map-right-distributive-prod-coprod =
    map-right-distributive-Σ-coprod A B (λ x → C)

  map-inv-right-distributive-prod-coprod :
    coprod (A × C) (B × C) → (coprod A B) × C
  map-inv-right-distributive-prod-coprod =
    map-inv-right-distributive-Σ-coprod A B (λ x → C)

  issec-map-inv-right-distributive-prod-coprod :
    ( map-right-distributive-prod-coprod ∘
      map-inv-right-distributive-prod-coprod) ~ id
  issec-map-inv-right-distributive-prod-coprod =
    issec-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  isretr-map-inv-right-distributive-prod-coprod :
    ( map-inv-right-distributive-prod-coprod ∘
      map-right-distributive-prod-coprod) ~ id
  isretr-map-inv-right-distributive-prod-coprod =
    isretr-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  abstract
    is-equiv-map-right-distributive-prod-coprod :
      is-equiv map-right-distributive-prod-coprod
    is-equiv-map-right-distributive-prod-coprod =
      is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)
  
  right-distributive-prod-coprod : ((coprod A B) × C) ≃ coprod (A × C) (B × C)
  right-distributive-prod-coprod = right-distributive-Σ-coprod A B (λ x → C)

-- Left distributivity of products over coproducts

module _
  {l1 l2 l3 : Level} (A : Set l1) (B : Set l2) (C : Set l3)
  where

  map-left-distributive-prod-coprod : A × (coprod B C) → coprod (A × B) (A × C)
  map-left-distributive-prod-coprod =
    map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  map-inv-left-distributive-prod-coprod :
    coprod (A × B) (A × C) → A × (coprod B C)
  map-inv-left-distributive-prod-coprod =
    map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  issec-map-inv-left-distributive-prod-coprod :
    ( map-left-distributive-prod-coprod ∘
      map-inv-left-distributive-prod-coprod) ~ id
  issec-map-inv-left-distributive-prod-coprod =
    issec-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  isretr-map-inv-left-distributive-prod-coprod :
    ( map-inv-left-distributive-prod-coprod ∘
      map-left-distributive-prod-coprod) ~ id
  isretr-map-inv-left-distributive-prod-coprod =
    isretr-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  is-equiv-map-left-distributive-prod-coprod :
    is-equiv map-left-distributive-prod-coprod
  is-equiv-map-left-distributive-prod-coprod =
    is-equiv-map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  left-distributive-prod-coprod : (A × (coprod B C)) ≃ coprod (A × B) (A × C)
  left-distributive-prod-coprod =
    left-distributive-Σ-coprod A (λ x → B) (λ x → C)

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  where

  -- Definition 9.3.1
  
  Eq-Σ : (s t : Σ A B) → Set (l1 ⊔ l2)
  Eq-Σ s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

  -- Lemma 9.3.2
    
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  pr1 (refl-Eq-Σ (pair a b)) = refl
  pr2 (refl-Eq-Σ (pair a b)) = refl

  -- Definition 9.3.3
  
  pair-eq-Σ : {s t : Σ A B} → Id s t → Eq-Σ s t
  pair-eq-Σ {s} refl = refl-Eq-Σ s

  -- Theorem 9.3.4
  
  eq-pair-Σ :
    {s t : Σ A B} →
    (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
  eq-pair-Σ {pair x y} {pair .x .y} refl refl = refl

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → Id s t
  eq-pair-Σ' (pair α β) = eq-pair-Σ α β

  isretr-pair-eq-Σ :
    (s t : Σ A B) →
    ((pair-eq-Σ {s} {t}) ∘ (eq-pair-Σ' {s} {t})) ~ id {A = Eq-Σ s t}
  isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

  issec-pair-eq-Σ :
    (s t : Σ A B) → ((eq-pair-Σ' {s} {t}) ∘ (pair-eq-Σ {s} {t})) ~ id
  issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t =
      is-equiv-has-inverse
        ( pair-eq-Σ)
        ( issec-pair-eq-Σ s t)
        ( isretr-pair-eq-Σ s t)

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ Id s t
  equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t =
      is-equiv-has-inverse
        ( eq-pair-Σ')
        ( isretr-pair-eq-Σ s t)
        ( issec-pair-eq-Σ s t)

  equiv-pair-eq-Σ : (s t : Σ A B) → Id s t ≃ Eq-Σ s t
  equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

  η-pair : (t : Σ A B) → Id (pair (pr1 t) (pr2 t)) t
  η-pair t = eq-pair-Σ refl refl

{- For our convenience, we repeat the above argument for cartesian products. -}

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where
  
  Eq-prod : (s t : A × B) → Set (l1 ⊔ l2)
  Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))

  eq-pair' : {s t : A × B} → Eq-prod s t → Id s t
  eq-pair' {pair x y} {pair .x .y} (pair refl refl) = refl

  eq-pair : {s t : A × B} → Id (pr1 s) (pr1 t) → Id (pr2 s) (pr2 t) → Id s t
  eq-pair p q = eq-pair' (pair p q)

{- Ideally, we would use the 3-for-2 property of equivalences to show that 
   eq-pair-triv is an equivalence, using that eq-pair-Σ is an equivalence. 
   Indeed, there is an equivalence 
   
     (Id x x') × (Id y y') → Σ (Id x x') (λ p → Id (tr (λ x → B) p y) y'). 

   However, to show that this map is an equivalence we either give a direct 
   proof (in which case we might as well have given a direct proof that 
   eq-pair-triv is an equivalence), or we use the fact that it is the induced 
   map on total spaces of a fiberwise equivalence (the topic of Lecture 8). 
   Thus it seems that a direct proof showing that eq-pair-triv is an 
   equivalence is quickest for now. 
-}

  pair-eq : {s t : A × B} → Id s t → Eq-prod s t
  pr1 (pair-eq α) = cong pr1 α
  pr2 (pair-eq α) = cong pr2 α

  isretr-pair-eq : {s t : A × B} → ((pair-eq {s} {t}) ∘ (eq-pair' {s} {t})) ~ id
  isretr-pair-eq {pair x y} {pair .x .y} (pair refl refl) = refl

  issec-pair-eq : {s t : A × B} → ((eq-pair' {s} {t}) ∘ (pair-eq {s} {t})) ~ id
  issec-pair-eq {pair x y} {pair .x .y} refl = refl

  abstract
    is-equiv-eq-pair : (s t : A × B) → is-equiv (eq-pair' {s} {t})
    is-equiv-eq-pair s t =
      is-equiv-has-inverse pair-eq issec-pair-eq isretr-pair-eq

  equiv-eq-pair : (s t : A × B) → Eq-prod s t ≃ Id s t
  pr1 (equiv-eq-pair s t) = eq-pair'
  pr2 (equiv-eq-pair s t) = is-equiv-eq-pair s t

  abstract
    is-equiv-pair-eq :
      (s t : A × B) → is-equiv (pair-eq {s} {t})
    is-equiv-pair-eq s t =
      is-equiv-has-inverse eq-pair' isretr-pair-eq issec-pair-eq

  equiv-pair-eq :
    (s t : A × B) → Id s t ≃ Eq-prod s t
  pr1 (equiv-pair-eq s t) = pair-eq
  pr2 (equiv-pair-eq s t) = is-equiv-pair-eq s t

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  -- Exercise 9.3(a)
  
  abstract
    is-equiv-htpy :
      {f : A → B} (g : A → B) → f ~ g → is-equiv g → is-equiv f
    pr1 (pr1 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) = gs
    pr2 (pr1 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) =
      (H ·r gs) ∙h issec
    pr1 (pr2 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) = gr
    pr2 (pr2 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) =
      (gr ·l H) ∙h isretr

  is-equiv-htpy-equiv : {f : A → B} (e : A ≃ B) → f ~ map-equiv e → is-equiv f
  is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

  abstract
    is-equiv-htpy' : (f : A → B) {g : A → B} → f ~ g → is-equiv f → is-equiv g
    is-equiv-htpy' f H = is-equiv-htpy f (inv-htpy H)

  is-equiv-htpy-equiv' : (e : A ≃ B) {g : A → B} → map-equiv e ~ g → is-equiv g
  is-equiv-htpy-equiv' e H =
    is-equiv-htpy' (map-equiv e) H (is-equiv-map-equiv e)

  -- Exercise 9.3(b)
  
  inv-htpy-is-equiv :
    {f g : A → B} (G : f ~ g) (H : is-equiv f) (K : is-equiv g) →
    (map-inv-is-equiv H) ~ (map-inv-is-equiv K)
  inv-htpy-is-equiv G H K b =
    ( inv
      ( isretr-map-inv-is-equiv' K (map-inv-is-equiv H b))) ∙
    ( cong (map-inv-is-equiv K)
      ( ( inv (G (map-inv-is-equiv H b))) ∙
        ( issec-map-inv-is-equiv' H b)))

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : A → B → Set l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  pr1 (map-left-swap-Σ (pair a (pair b c))) = b
  pr1 (pr2 (map-left-swap-Σ (pair a (pair b c)))) = a
  pr2 (pr2 (map-left-swap-Σ (pair a (pair b c)))) = c
  
  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  pr1 (map-inv-left-swap-Σ (pair b (pair a c))) = a
  pr1 (pr2 (map-inv-left-swap-Σ (pair b (pair a c)))) = b
  pr2 (pr2 (map-inv-left-swap-Σ (pair b (pair a c)))) = c
  
  isretr-map-inv-left-swap-Σ : (map-inv-left-swap-Σ ∘ map-left-swap-Σ) ~ id
  isretr-map-inv-left-swap-Σ (pair a (pair b c)) = refl

  issec-map-inv-left-swap-Σ : (map-left-swap-Σ ∘ map-inv-left-swap-Σ) ~ id
  issec-map-inv-left-swap-Σ (pair b (pair a c)) = refl
  
  abstract
    is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
    is-equiv-map-left-swap-Σ =
      is-equiv-has-inverse
        map-inv-left-swap-Σ
        issec-map-inv-left-swap-Σ
        isretr-map-inv-left-swap-Σ
  
  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  pr1 equiv-left-swap-Σ = map-left-swap-Σ
  pr2 equiv-left-swap-Σ = is-equiv-map-left-swap-Σ

-- We also define swap on the right

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  pr1 (pr1 (map-right-swap-Σ (pair (pair a b) c))) = a
  pr2 (pr1 (map-right-swap-Σ (pair (pair a b) c))) = c
  pr2 (map-right-swap-Σ (pair (pair a b) c)) = b

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  pr1 (pr1 (map-inv-right-swap-Σ (pair (pair a c) b))) = a
  pr2 (pr1 (map-inv-right-swap-Σ (pair (pair a c) b))) = b
  pr2 (map-inv-right-swap-Σ (pair (pair a c) b)) = c

  issec-map-inv-right-swap-Σ : (map-right-swap-Σ ∘ map-inv-right-swap-Σ) ~ id
  issec-map-inv-right-swap-Σ (pair (pair x y) z) = refl

  isretr-map-inv-right-swap-Σ : (map-inv-right-swap-Σ ∘ map-right-swap-Σ) ~ id
  isretr-map-inv-right-swap-Σ (pair (pair x z) y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-has-inverse
      map-inv-right-swap-Σ
      issec-map-inv-right-swap-Σ
      isretr-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  pr1 equiv-right-swap-Σ = map-right-swap-Σ
  pr2 equiv-right-swap-Σ = is-equiv-map-right-swap-Σ
  
is-contr :
  {l : Level} → Set l → Set l
is-contr A = Σ A (λ a → (x : A) → Id a x)

abstract
  center :
    {l : Level} {A : Set l} → is-contr A → A
  center (pair c is-contr-A) = c
  
-- We make sure that the contraction is coherent in a straightforward way
eq-is-contr' :
  {l : Level} {A : Set l} → is-contr A → (x y : A) → Id x y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : Set l} → is-contr A → {x y : A} → Id x y
eq-is-contr C {x} {y} = eq-is-contr' C x y

abstract
  contraction :
    {l : Level} {A : Set l} (is-contr-A : is-contr A) →
    (const (center is-contr-A) ~ id)
  contraction C x = eq-is-contr C
  
  coh-contraction :
    {l : Level} {A : Set l} (is-contr-A : is-contr A) →
    Id (contraction is-contr-A (center is-contr-A)) refl
  coh-contraction (pair c C) = left-inv (C c)

ev-pt :
  {l1 l2 : Level} {A : Set l1} (a : A) (B : A → Set l2) → ((x : A) → B x) → B a
ev-pt a B f = f a

is-singleton :
  (l : Level) {i : Level} (A : Set i) → A → Set (lsuc l ⊔ i)
is-singleton l A a = (B : A → Set l) → sec (ev-pt a B)

ind-is-singleton :
  {l1 l2 : Level} {A : Set l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → Set l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

comp-is-singleton :
  {l1 l2 : Level} {A : Set l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → Set l2) → (ev-pt a B ∘ ind-is-singleton a H B) ~ id
comp-is-singleton a H B = pr2 (H B)

{- Theorem 10.2.3 -}

abstract
  ind-singleton-is-contr :
    {i j : Level} {A : Set i} (a : A) (is-contr-A : is-contr A) (B : A → Set j) →
    B a → (x : A) → B x
  ind-singleton-is-contr a is-contr-A B b x =
    tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b
  
  comp-singleton-is-contr :
    {i j : Level} {A : Set i} (a : A) (is-contr-A : is-contr A) (B : A → Set j) →
    ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
  comp-singleton-is-contr a is-contr-A B b =
    cong (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-singleton-is-contr :
  {l1 l2 : Level} {A : Set l1} (a : A) → is-contr A → is-singleton l2 A a
pr1 (is-singleton-is-contr a is-contr-A B) =
  ind-singleton-is-contr a is-contr-A B
pr2 (is-singleton-is-contr a is-contr-A B) =
  comp-singleton-is-contr a is-contr-A B

abstract
  is-contr-ind-singleton :
    {i : Level} (A : Set i) (a : A) →
    ({l : Level} (P : A → Set l) → P a → (x : A) → P x) → is-contr A
  pr1 (is-contr-ind-singleton A a S) = a
  pr2 (is-contr-ind-singleton A a S) = S (λ x → Id a x) refl

abstract
  is-contr-is-singleton :
    {i : Level} (A : Set i) (a : A) →
    ({l : Level} → is-singleton l A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))

abstract
  is-singleton-unit : {l : Level} → is-singleton l unit star
  pr1 (is-singleton-unit B) b star = b
  pr2 (is-singleton-unit B) = refl-htpy

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-singleton unit star (is-singleton-unit)

abstract
  is-singleton-total-path :
    {i l : Level} (A : Set i) (a : A) →
    is-singleton l (Σ A (λ x → Id a x)) (pair a refl)
  pr1 (is-singleton-total-path A a B) b (pair .a refl) = b
  pr2 (is-singleton-total-path A a B) = refl-htpy

abstract
  is-contr-total-path :
    {i : Level} {A : Set i} (a : A) → is-contr (Σ A (λ x → Id a x))
  is-contr-total-path {A = A} a =
    is-contr-is-singleton _ _ (is-singleton-total-path A a)
  
module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B)
  where
  
  {- Definition 10.3.1 -}
  
  fib : Set (l1 ⊔ l2)
  fib = Σ A (λ x → Id (f x) b)

  fib' : Set (l1 ⊔ l2)
  fib' = Σ A (λ x → Id b (f x))

  {- Definition 10.3.2 -}
  
  Eq-fib : fib → fib → Set (l1 ⊔ l2)
  Eq-fib s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((cong f α) ∙ (pr2 t)) (pr2 s))

  {- Proposition 10.3.3 -}
  
  refl-Eq-fib : (s : fib) → Eq-fib s s
  pr1 (refl-Eq-fib s) = refl
  pr2 (refl-Eq-fib s) = refl

  Eq-eq-fib : {s t : fib} → Id s t → Eq-fib s t
  Eq-eq-fib {s} refl = refl-Eq-fib s

  eq-Eq-fib' : {s t : fib} → Eq-fib s t → Id s t
  eq-Eq-fib' {pair x p} {pair .x .p} (pair refl refl) = refl

  eq-Eq-fib :
    {s t : fib} (α : Id (pr1 s) (pr1 t)) →
    Id ((cong f α) ∙ (pr2 t)) (pr2 s) → Id s t
  eq-Eq-fib α β = eq-Eq-fib' (pair α β)

  issec-eq-Eq-fib : {s t : fib} → (Eq-eq-fib {s} {t} ∘ eq-Eq-fib' {s} {t}) ~ id
  issec-eq-Eq-fib {pair x p} {pair .x .p} (pair refl refl) = refl

  isretr-eq-Eq-fib : {s t : fib} → (eq-Eq-fib' {s} {t} ∘ Eq-eq-fib {s} {t}) ~ id
  isretr-eq-Eq-fib {pair x p} {.(pair x p)} refl = refl

  abstract
    is-equiv-Eq-eq-fib : {s t : fib} → is-equiv (Eq-eq-fib {s} {t})
    is-equiv-Eq-eq-fib {s} {t} =
      is-equiv-has-inverse
        eq-Eq-fib'
        issec-eq-Eq-fib
        isretr-eq-Eq-fib

  equiv-Eq-eq-fib : {s t : fib} → Id s t ≃ Eq-fib s t
  pr1 (equiv-Eq-eq-fib {s} {t}) = Eq-eq-fib
  pr2 (equiv-Eq-eq-fib {s} {t}) = is-equiv-Eq-eq-fib

  abstract
    is-equiv-eq-Eq-fib :
      {s t : fib} → is-equiv (eq-Eq-fib' {s} {t})
    is-equiv-eq-Eq-fib {s} {t} =
      is-equiv-has-inverse
        Eq-eq-fib
        isretr-eq-Eq-fib
        issec-eq-Eq-fib

  equiv-eq-Eq-fib : {s t : fib} → Eq-fib s t ≃ Id s t
  pr1 (equiv-eq-Eq-fib {s} {t}) = eq-Eq-fib'
  pr2 (equiv-eq-Eq-fib {s} {t}) = is-equiv-eq-Eq-fib

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  is-contr-map : (A → B) → Set (l1 ⊔ l2)
  is-contr-map f = (y : B) → is-contr (fib f y)

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
  where
  
  map-inv-is-contr-map : is-contr-map f → B → A
  map-inv-is-contr-map H y = pr1 (center (H y))

  issec-map-inv-is-contr-map :
    (H : is-contr-map f) → (f ∘ (map-inv-is-contr-map H)) ~ id
  issec-map-inv-is-contr-map H y = pr2 (center (H y))

  isretr-map-inv-is-contr-map :
    (H : is-contr-map f) → ((map-inv-is-contr-map H) ∘ f) ~ id
  isretr-map-inv-is-contr-map H x =
    cong
      ( pr1 {B = λ z → Id (f z) (f x)})
      ( ( inv
          ( contraction
            ( H (f x))
            ( pair
              ( map-inv-is-contr-map H (f x))
              ( issec-map-inv-is-contr-map H (f x))))) ∙
        ( contraction (H (f x)) (pair x refl)))

  abstract
    is-equiv-is-contr-map : is-contr-map f → is-equiv f
    is-equiv-is-contr-map H =
      is-equiv-has-inverse
        ( map-inv-is-contr-map H)
        ( issec-map-inv-is-contr-map H)
        ( isretr-map-inv-is-contr-map H)

module _
  {l : Level} {A : Set l}
  where

  abstract
    is-equiv-terminal-map-is-contr :
      is-contr A → is-equiv (terminal-map {A = A})
    pr1 (pr1 (is-equiv-terminal-map-is-contr H)) star = center H
    pr2 (pr1 (is-equiv-terminal-map-is-contr H)) star = refl
    pr1 (pr2 (is-equiv-terminal-map-is-contr H)) x = center H
    pr2 (pr2 (is-equiv-terminal-map-is-contr H)) = contraction H

  abstract
    is-contr-is-equiv-const : is-equiv (terminal-map {A = A}) → is-contr A
    pr1 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = h star
    pr2 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = isretr

module _
  {l1 l2 : Level} {A : Set l1} (B : Set l2)
  where
  
  abstract
    is-contr-is-equiv :
      (f : A → B) → is-equiv f → is-contr B → is-contr A
    is-contr-is-equiv f is-equiv-f is-contr-B =
      is-contr-is-equiv-const
        ( is-equiv-comp'
          ( terminal-map)
          ( f)
          ( is-equiv-f)
          ( is-equiv-terminal-map-is-contr is-contr-B))

  abstract
    is-contr-equiv : (e : A ≃ B) → is-contr B → is-contr A
    is-contr-equiv (pair e is-equiv-e) is-contr-B =
      is-contr-is-equiv e is-equiv-e is-contr-B

module _
  {l1 l2 : Level} (A : Set l1) {B : Set l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' f is-equiv-f is-contr-A =
      is-contr-is-equiv A
        ( map-inv-is-equiv is-equiv-f)
        ( is-equiv-map-inv-is-equiv is-equiv-f)
        ( is-contr-A)

  abstract
    is-contr-equiv' : (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' (pair e is-equiv-e) is-contr-A =
      is-contr-is-equiv' e is-equiv-e is-contr-A

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-equiv-is-contr :
      (f : A → B) → is-contr A → is-contr B → is-equiv f
    is-equiv-is-contr f is-contr-A is-contr-B =
      is-equiv-has-inverse
        ( const (center is-contr-A))
        ( ind-singleton-is-contr _ is-contr-B _
          ( inv (contraction is-contr-B (f (center is-contr-A)))))
        ( contraction is-contr-A)

  equiv-is-contr : is-contr A → is-contr B → A ≃ B
  pr1 (equiv-is-contr is-contr-A is-contr-B) a = center is-contr-B
  pr2 (equiv-is-contr is-contr-A is-contr-B) =
    is-equiv-is-contr _ is-contr-A is-contr-B
    
module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B)
  where
  
  coherence-is-coherently-invertible :
    (g : B → A) (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → Set (l1 ⊔ l2)
  coherence-is-coherently-invertible g G H = (G ·r f) ~ (f ·l H)

  is-coherently-invertible : Set (l1 ⊔ l2)
  is-coherently-invertible =
    Σ ( B → A)
      ( λ g → Σ ((f ∘ g) ~ id)
        ( λ G → Σ ((g ∘ f) ~ id)
          (λ H → coherence-is-coherently-invertible g G H)))

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
  where

  inv-is-coherently-invertible : is-coherently-invertible f → B → A
  inv-is-coherently-invertible = pr1

  issec-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
  issec-inv-is-coherently-invertible H = pr1 (pr2 H)
  
  isretr-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
  isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

  coh-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) →
    coherence-is-coherently-invertible f
      ( inv-is-coherently-invertible H)
      ( issec-inv-is-coherently-invertible H)
      ( isretr-inv-is-coherently-invertible H)
  coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))

  has-inverse-is-coherently-invertible :
    is-coherently-invertible f → has-inverse f
  pr1 (has-inverse-is-coherently-invertible H) =
    inv-is-coherently-invertible H
  pr1 (pr2 (has-inverse-is-coherently-invertible H)) =
    issec-inv-is-coherently-invertible H
  pr2 (pr2 (has-inverse-is-coherently-invertible H)) =
    isretr-inv-is-coherently-invertible H

  {- Proposition 10.4.2 -}
  
  abstract
    center-fib-is-coherently-invertible :
      is-coherently-invertible f → (y : B) → fib f y
    pr1 (center-fib-is-coherently-invertible H y) =
      inv-is-coherently-invertible H y
    pr2 (center-fib-is-coherently-invertible H y) =
      issec-inv-is-coherently-invertible H y

    contraction-fib-is-coherently-invertible :
      (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
      Id (center-fib-is-coherently-invertible H y) t
    contraction-fib-is-coherently-invertible H y (pair x refl) =
      eq-Eq-fib f y
        ( isretr-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-inv-is-coherently-invertible H x)))

  is-contr-map-is-coherently-invertible : 
    is-coherently-invertible f → is-contr-map f
  pr1 (is-contr-map-is-coherently-invertible H y) =
    center-fib-is-coherently-invertible H y
  pr2 (is-contr-map-is-coherently-invertible H y) =
    contraction-fib-is-coherently-invertible H y
  
{- Definition 10.4.3 -}

htpy-nat :
  {i j : Level} {A : Set i} {B : Set j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (cong g p)) ((cong f p) ∙ (H y))
htpy-nat H refl = right-unit

{- Definition 10.4.4 -}

left-unwhisk :
  {i : Level} {A : Set i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : Set i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : Set i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (cong f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( cong (concat (H (f x)) x) (inv (cong-id (H x)))) ∙
      ( htpy-nat H (H x)))

{- Lemma 10.4.5 -}

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} (H : has-inverse f)
  where
  
  inv-has-inverse : B → A
  inv-has-inverse = pr1 H
  
  issec-inv-has-inverse : (f ∘ inv-has-inverse) ~ id
  issec-inv-has-inverse y =
    ( inv (pr1 (pr2 H) (f (inv-has-inverse y)))) ∙
    ( cong f (pr2 (pr2 H) (inv-has-inverse y)) ∙ (pr1 (pr2 H) y))
  
  isretr-inv-has-inverse : (inv-has-inverse ∘ f) ~ id
  isretr-inv-has-inverse = pr2 (pr2 H)
  
  coherence-inv-has-inverse :
    (issec-inv-has-inverse ·r f) ~ (f ·l isretr-inv-has-inverse)
  coherence-inv-has-inverse x =
    inv
      ( inv-con
        ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
        ( cong f (pr2 (pr2 H) x))
        ( (cong f (pr2 (pr2 H) (inv-has-inverse (f x)))) ∙ (pr1 (pr2 H) (f x)))
        ( sq-top-whisk
          ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
          ( cong f (pr2 (pr2 H) x))
          ( (cong (f ∘ (inv-has-inverse ∘ f)) (pr2 (pr2 H) x)))
          ( ( cong-comp (pr2 (pr2 H) x)) ∙
            ( inv (cong (cong f) (htpy-red (pr2 (pr2 H)) x))))
          ( pr1 (pr2 H) (f x))
          ( htpy-nat (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  is-coherently-invertible-has-inverse : is-coherently-invertible f
  pr1 is-coherently-invertible-has-inverse = inv-has-inverse
  pr1 (pr2 is-coherently-invertible-has-inverse) = issec-inv-has-inverse
  pr1 (pr2 (pr2 is-coherently-invertible-has-inverse)) = isretr-inv-has-inverse
  pr2 (pr2 (pr2 is-coherently-invertible-has-inverse)) =
    coherence-inv-has-inverse
  
{- Theorem 10.4.6 -}

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
  where
  
  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv = 
      is-contr-map-is-coherently-invertible ∘
        ( is-coherently-invertible-has-inverse ∘
          has-inverse-is-equiv)

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} (H : is-equiv f)
  where

  issec-map-inv-is-equiv : (f ∘ map-inv-is-equiv H) ~ id
  issec-map-inv-is-equiv = issec-inv-has-inverse (has-inverse-is-equiv H)

  isretr-map-inv-is-equiv : (map-inv-is-equiv H ∘ f) ~ id
  isretr-map-inv-is-equiv =
    isretr-inv-has-inverse (has-inverse-is-equiv H)
  
  coherence-map-inv-is-equiv :
    ( issec-map-inv-is-equiv ·r f) ~ (f ·l isretr-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coherence-inv-has-inverse (has-inverse-is-equiv H)

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv : ((map-equiv e) ∘ map-inv-equiv) ~ id
  issec-map-inv-equiv = issec-map-inv-is-equiv (is-equiv-map-equiv e)

  isretr-map-inv-equiv : (map-inv-equiv ∘ (map-equiv e)) ~ id
  isretr-map-inv-equiv =
    isretr-map-inv-is-equiv (is-equiv-map-equiv e)
  
  coherence-map-inv-equiv :
    ( issec-map-inv-equiv ·r (map-equiv e)) ~
    ( (map-equiv e) ·l isretr-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

module _
  {l : Level} {A : Set l}
  where
  
  contraction-is-prop-is-contr :
    (H : is-contr A) {x y : A} (p : Id x y) → Id (eq-is-contr H) p
  contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

  abstract
    is-prop-is-contr :
      is-contr A → (x y : A) → is-contr (Id x y)
    pr1 (is-prop-is-contr H x y) = eq-is-contr H
    pr2 (is-prop-is-contr H x y) = contraction-is-prop-is-contr H

module _
  {l1 l2 : Level} {A : Set l1} (B : A → Set l2) (a : A)
  where

  map-fib-pr1 : fib (pr1 {B = B}) a → B a
  map-fib-pr1 (pair (pair x y) p) = tr B p y

  map-inv-fib-pr1 : B a → fib (pr1 {B = B}) a
  map-inv-fib-pr1 b = pair (pair a b) refl

  issec-map-inv-fib-pr1 : (map-inv-fib-pr1 ∘ map-fib-pr1) ~ id
  issec-map-inv-fib-pr1 (pair (pair .a y) refl) = refl

  isretr-map-inv-fib-pr1 : (map-fib-pr1 ∘ map-inv-fib-pr1) ~ id
  isretr-map-inv-fib-pr1 b = refl

  abstract
    is-equiv-map-fib-pr1 : is-equiv map-fib-pr1
    is-equiv-map-fib-pr1 =
      is-equiv-has-inverse
        map-inv-fib-pr1
        isretr-map-inv-fib-pr1
        issec-map-inv-fib-pr1

  equiv-fib-pr1 : fib (pr1 {B = B}) a ≃ B a
  pr1 equiv-fib-pr1 = map-fib-pr1
  pr2 equiv-fib-pr1 = is-equiv-map-fib-pr1

  abstract
    is-equiv-map-inv-fib-pr1 : is-equiv map-inv-fib-pr1
    is-equiv-map-inv-fib-pr1 =
      is-equiv-has-inverse
        map-fib-pr1
        issec-map-inv-fib-pr1
        isretr-map-inv-fib-pr1

  inv-equiv-fib-pr1 : B a ≃ fib (pr1 {B = B}) a
  pr1 inv-equiv-fib-pr1 = map-inv-fib-pr1
  pr2 inv-equiv-fib-pr1 = is-equiv-map-inv-fib-pr1

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (C : is-contr A) (a : A)
  where

  map-inv-left-unit-law-Σ-is-contr : B a → Σ A B
  pr1 (map-inv-left-unit-law-Σ-is-contr b) = a
  pr2 (map-inv-left-unit-law-Σ-is-contr b) = b

  map-left-unit-law-Σ-is-contr : Σ A B → B a
  map-left-unit-law-Σ-is-contr (pair x b) = tr B (eq-is-contr C) b

  issec-map-inv-left-unit-law-Σ-is-contr :
    ( map-left-unit-law-Σ-is-contr ∘ map-inv-left-unit-law-Σ-is-contr) ~ id
  issec-map-inv-left-unit-law-Σ-is-contr b =
    cong (λ t → tr B t b) (eq-is-contr (is-prop-is-contr C a a))

  isretr-map-inv-left-unit-law-Σ-is-contr :
    ( map-inv-left-unit-law-Σ-is-contr ∘ map-left-unit-law-Σ-is-contr) ~ id
  isretr-map-inv-left-unit-law-Σ-is-contr (pair x b) =
    eq-pair-Σ
      ( inv (eq-is-contr C))
      ( ( inv (tr-concat {B = B} (eq-is-contr C) (inv (eq-is-contr C)) b)) ∙
        ( cong (λ t → tr B t b) (right-inv (eq-is-contr C))))

  abstract
    is-equiv-map-left-unit-law-Σ-is-contr :
      is-equiv map-left-unit-law-Σ-is-contr
    is-equiv-map-left-unit-law-Σ-is-contr =
      is-equiv-has-inverse
        map-inv-left-unit-law-Σ-is-contr
        issec-map-inv-left-unit-law-Σ-is-contr
        isretr-map-inv-left-unit-law-Σ-is-contr

  left-unit-law-Σ-is-contr : Σ A B ≃ B a
  pr1 left-unit-law-Σ-is-contr = map-left-unit-law-Σ-is-contr
  pr2 left-unit-law-Σ-is-contr = is-equiv-map-left-unit-law-Σ-is-contr

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contr :
      is-equiv map-inv-left-unit-law-Σ-is-contr
    is-equiv-map-inv-left-unit-law-Σ-is-contr =
      is-equiv-has-inverse
        map-left-unit-law-Σ-is-contr
        isretr-map-inv-left-unit-law-Σ-is-contr
        issec-map-inv-left-unit-law-Σ-is-contr
  
  inv-left-unit-law-Σ-is-contr : B a ≃ Σ A B
  pr1 inv-left-unit-law-Σ-is-contr = map-inv-left-unit-law-Σ-is-contr
  pr2 inv-left-unit-law-Σ-is-contr = is-equiv-map-inv-left-unit-law-Σ-is-contr

  abstract
    is-contr-Σ :
      is-contr (B a) → is-contr (Σ A B)
    is-contr-Σ is-contr-B =
      is-contr-equiv
        ( B a)
        ( left-unit-law-Σ-is-contr)
        ( is-contr-B)

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  where

  abstract
    is-contr-Σ' :
      is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
    is-contr-Σ' is-contr-A is-contr-B =
      is-contr-equiv
        ( B (center is-contr-A))
        ( left-unit-law-Σ-is-contr is-contr-A (center is-contr-A))
        ( is-contr-B (center is-contr-A))

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (C : is-contr A)
  where
  
  left-unit-law-prod-is-contr : (A × B) ≃ B
  left-unit-law-prod-is-contr =
    left-unit-law-Σ-is-contr C (center C)
  
module _
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
  (f : (x : A) → B x → C x)
  where

  {- Any family of maps induces a map on the total spaces. -}
  
  tot : Σ A B → Σ A C
  pr1 (tot t) = pr1 t
  pr2 (tot t) = f (pr1 t) (pr2 t)

  {- We show that for any family of maps, the fiber of the induced map on total
     spaces are equivalent to the fibers of the maps in the family. -}
   
  fib-ftr-fib-tot : (t : Σ A C) → fib tot t → fib (f (pr1 t)) (pr2 t)
  pr1 (fib-ftr-fib-tot .(tot (pair x y)) (pair (pair x y) refl)) = y
  pr2 (fib-ftr-fib-tot .(tot (pair x y)) (pair (pair x y) refl)) = refl

  fib-tot-fib-ftr : (t : Σ A C) → fib (f (pr1 t)) (pr2 t) → fib tot t
  pr1 (pr1 (fib-tot-fib-ftr (pair a .(f a y)) (pair y refl))) = a
  pr2 (pr1 (fib-tot-fib-ftr (pair a .(f a y)) (pair y refl))) = y
  pr2 (fib-tot-fib-ftr (pair a .(f a y)) (pair y refl)) = refl

  issec-fib-tot-fib-ftr :
    (t : Σ A C) → (fib-ftr-fib-tot t ∘ fib-tot-fib-ftr t) ~ id
  issec-fib-tot-fib-ftr (pair x .(f x y)) (pair y refl) = refl

  isretr-fib-tot-fib-ftr :
    (t : Σ A C) → (fib-tot-fib-ftr t ∘ fib-ftr-fib-tot t) ~ id
  isretr-fib-tot-fib-ftr .(pair x (f x y)) (pair (pair x y) refl) = refl

  abstract
    is-equiv-fib-ftr-fib-tot : (t : Σ A C) → is-equiv (fib-ftr-fib-tot t)
    is-equiv-fib-ftr-fib-tot t =
      is-equiv-has-inverse
        ( fib-tot-fib-ftr t)
        ( issec-fib-tot-fib-ftr t)
        ( isretr-fib-tot-fib-ftr t)

  abstract
    is-equiv-fib-tot-fib-ftr : (t : Σ A C) → is-equiv (fib-tot-fib-ftr t)
    is-equiv-fib-tot-fib-ftr t =
      is-equiv-has-inverse
        ( fib-ftr-fib-tot t)
        ( isretr-fib-tot-fib-ftr t)
        ( issec-fib-tot-fib-ftr t)

  {- Now that we have shown that the fibers of the induced map on total spaces
     are equivalent to the fibers of the maps in the family, it follows that
     the induced map on total spaces is an equivalence if and only if each map
     in the family is an equivalence. -}

  is-fiberwise-equiv : Set (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-equiv = (x : A) → is-equiv (f x)

tot-htpy :
  {i j k : Level} {A : Set i} {B : A → Set j} {C : A → Set k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair-Σ refl (H x y)

tot-id :
  {i j : Level} {A : Set i} (B : A → Set j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (pair x y) = refl

tot-comp :
  {i j j' j'' : Level}
  {A : Set i} {B : A → Set j} {B' : A → Set j'} {B'' : A → Set j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (pair x y) = refl

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-equiv-tot-is-fiberwise-equiv : is-fiberwise-equiv f → is-equiv (tot f )
    is-equiv-tot-is-fiberwise-equiv H =
      is-equiv-is-contr-map
        ( λ t →
          is-contr-is-equiv
            ( fib (f (pr1 t)) (pr2 t))
            ( fib-ftr-fib-tot f t)
            ( is-equiv-fib-ftr-fib-tot f t)
            ( is-contr-map-is-equiv (H (pr1 t)) (pr2 t)))

  abstract
    is-fiberwise-equiv-is-equiv-tot : is-equiv (tot f) → is-fiberwise-equiv f
    is-fiberwise-equiv-is-equiv-tot is-equiv-tot-f x =
      is-equiv-is-contr-map
        ( λ z →
          is-contr-is-equiv'
            ( fib (tot f) (pair x z))
            ( fib-ftr-fib-tot f (pair x z))
            ( is-equiv-fib-ftr-fib-tot f (pair x z))
            ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

module _
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
  where

  equiv-tot : ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
  pr1 (equiv-tot e) = tot (λ x → map-equiv (e x))
  pr2 (equiv-tot e) =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x))

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (a : A) (b : B a)
  where

  -- The general form of the fundamental theorem of identity types
  
  abstract
    fundamental-theorem-id :
      is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id is-contr-AB f =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

  abstract
    fundamental-theorem-id' :
      (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f → is-contr (Σ A B)
    fundamental-theorem-id' f is-fiberwise-equiv-f =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot f)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
        ( is-contr-total-path a)

module _
  {l1 l2 : Level} {A : Set l1} (B : Set l2)
  where

  abstract
    is-contr-retract-of : A retract-of B → is-contr B → is-contr A
    pr1 (is-contr-retract-of (pair i (pair r isretr)) H) = r (center H)
    pr2 (is-contr-retract-of (pair i (pair r isretr)) H) x =
      cong r (contraction H (i x)) ∙ (isretr x)

module _
  {i j : Level} {A : Set i} {B : A → Set j} (a : A)
  where

  abstract
    fundamental-theorem-id-retr :
      (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
      is-fiberwise-equiv i
    fundamental-theorem-id-retr i R =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot i)
          ( is-contr-retract-of (Σ _ (λ y → Id a y))
            ( pair (tot i)
              ( pair (tot λ x → pr1 (R x))
                ( ( inv-htpy (tot-comp i (λ x → pr1 (R x)))) ∙h
                  ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
            ( is-contr-total-path a))
          ( is-contr-total-path a))

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B)
  where

  abstract
    is-equiv-sec-is-equiv : (sec-f : sec f) → is-equiv (pr1 sec-f) → is-equiv f
    is-equiv-sec-is-equiv (pair g issec-g) is-equiv-sec-f =
      is-equiv-htpy h
        ( ( htpy-left-whisk f
            ( inv-htpy (issec-map-inv-is-equiv is-equiv-sec-f))) ∙h
          ( htpy-right-whisk issec-g h))
        ( is-equiv-map-inv-is-equiv is-equiv-sec-f)
      where
      h : A → B
      h = map-inv-is-equiv is-equiv-sec-f

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (a : A)
  where

  abstract
    fundamental-theorem-id-sec :
      (f : (x : A) → Id a x → B x) → ((x : A) → sec (f x)) →
      is-fiberwise-equiv f
    fundamental-theorem-id-sec f sec-f x =
      is-equiv-sec-is-equiv (f x) (sec-f x) (is-fiberwise-equiv-i x)
      where
        i : (x : A) → B x → Id a x
        i = λ x → pr1 (sec-f x)
        retr-i : (x : A) → retr (i x)
        pr1 (retr-i x) = f x
        pr2 (retr-i x) = pr2 (sec-f x)
        is-fiberwise-equiv-i : is-fiberwise-equiv i
        is-fiberwise-equiv-i = fundamental-theorem-id-retr a i retr-i

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  is-emb : (A → B) → Set (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (cong f {x} {y})

_↪_ :
  {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  map-emb : A ↪ B → A → B
  map-emb f = pr1 f

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb f = pr2 f

  equiv-ap-emb : (e : A ↪ B) {x y : A} → Id x y ≃ Id (map-emb e x) (map-emb e y)
  pr1 (equiv-ap-emb e {x} {y}) = cong (map-emb e)
  pr2 (equiv-ap-emb e {x} {y}) = is-emb-map-emb e x y

  is-injective-is-emb : {f : A → B} → is-emb f → is-injective f
  is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

  is-injective-emb : (e : A ↪ B) → is-injective (map-emb e)
  is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)

  is-emb-is-equiv : {f : A → B} → is-equiv f → is-emb f
  is-emb-is-equiv {f} is-equiv-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-contr-map-is-equiv is-equiv-f (f x)))
      ( λ y p → cong f p)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)

  equiv-ap :
    (e : A ≃ B) (x y : A) → (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
  pr1 (equiv-ap e x y) = cong (map-equiv e) {x} {y}
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y

is-prop :
  {i : Level} (A : Set i) → Set i
is-prop A = (x y : A) → is-contr (Id x y)

Set-Prop :
  (l : Level) → Set (lsuc l)
Set-Prop l = Σ (Set l) is-prop

module _
  {l : Level}
  where

  type-Prop : Set-Prop l → Set l
  type-Prop P = pr1 P

  abstract
    is-prop-type-Prop : (P : Set-Prop l) → is-prop (type-Prop P)
    is-prop-type-Prop P = pr2 P

{- Example 12.1.2 -}

abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : Set-Prop lzero
pr1 unit-Prop = unit
pr2 unit-Prop = is-prop-unit

abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : Set-Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty

{- Proposition 12.1.3 -}

module _
  {l : Level} (A : Set l)
  where
  
  all-elements-equal : Set l
  all-elements-equal = (x y : A) → Id x y
  
  is-proof-irrelevant : Set l
  is-proof-irrelevant = A → is-contr A
  
  is-subterminal : Set l
  is-subterminal = is-emb (terminal-map {A = A})

module _
  {l : Level} {A : Set l}
  where
  
  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = (inv (H x x)) ∙ (H x y)
    pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = pr1 (H x y)

  abstract
    eq-is-prop : is-prop A → {x y : A} → Id x y
    eq-is-prop H {x} {y} = eq-is-prop' H x y

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    pr1 (is-proof-irrelevant-all-elements-equal H a) = a
    pr2 (is-proof-irrelevant-all-elements-equal H a) = H a

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop =
      is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant H = eq-is-prop' (is-prop-is-proof-irrelevant H)

  abstract
    is-emb-is-emb :
      {l2 : Level} {B : Set l2} {f : A → B} → (A → is-emb f) → is-emb f
    is-emb-is-emb H x y = H x x y

  abstract
    is-subterminal-is-proof-irrelevant :
      is-proof-irrelevant A → is-subterminal A
    is-subterminal-is-proof-irrelevant H =
      is-emb-is-emb
        ( λ x → is-emb-is-equiv (is-equiv-is-contr _ (H x) is-contr-unit))

  abstract
    is-subterminal-all-elements-equal : all-elements-equal A → is-subterminal A
    is-subterminal-all-elements-equal =
      is-subterminal-is-proof-irrelevant ∘
      is-proof-irrelevant-all-elements-equal

  abstract
    is-subterminal-is-prop : is-prop A → is-subterminal A
    is-subterminal-is-prop = is-subterminal-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-subterminal : is-subterminal A → is-prop A
    is-prop-is-subterminal H x y =
      is-contr-is-equiv
        ( Id star star)
        ( cong terminal-map)
        ( H x y)
        ( is-prop-is-contr is-contr-unit star star)

  abstract
    eq-is-subterminal : is-subterminal A → all-elements-equal A
    eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

  abstract
    is-proof-irrelevant-is-subterminal :
      is-subterminal A → is-proof-irrelevant A
    is-proof-irrelevant-is-subterminal H =
      is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)

{- Proposition 12.1.4 -}

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-equiv-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-is-prop is-prop-A is-prop-B {f} g =
      is-equiv-has-inverse
        ( g)
        ( λ y → center (is-prop-B (f (g y)) y))
        ( λ x → center (is-prop-A (g (f x)) x))

  abstract
    equiv-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-prop is-prop-A is-prop-B f g) = f
    pr2 (equiv-prop is-prop-A is-prop-B f g) =
      is-equiv-is-prop is-prop-A is-prop-B g

-- Section 12.2 Subtypes

{- Definition 12.2.1 -}

module _
  {l1 l2 : Level} {A : Set l1} (B : A → Set l2)
  where

  is-subtype : Set (l1 ⊔ l2)
  is-subtype = (x : A) → is-prop (B x)

  is-property : Set (l1 ⊔ l2)
  is-property = is-subtype

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  is-prop-map : (A → B) → Set (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fib f b)

module _
  {l1 l2 : Level} {A : Set l1}
  where

  total-subtype : (A → Set-Prop l2) → Set (l1 ⊔ l2)
  total-subtype P = Σ A (λ x → pr1 (P x))

{- Lemma 12.2.2 -}

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H x y =
      is-contr-is-equiv _
        ( cong f {x} {y})
        ( is-emb-is-equiv E x y)
        ( H (f x) (f y))

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (pair f is-equiv-f) = is-prop-is-equiv is-equiv-f

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H =
      is-prop-is-equiv (is-equiv-map-inv-is-equiv E) H

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (pair f is-equiv-f) = is-prop-is-equiv' is-equiv-f

{- Theorem 12.2.3 -}

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
  where

  abstract
    is-emb-is-prop-map : is-prop-map f → is-emb f
    is-emb-is-prop-map is-prop-map-f x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( fib f (f x))
          ( equiv-tot (λ y → equiv-inv (f x) (f y)))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
        ( λ y → cong f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fib f y) → is-contr (fib f y)
      α (pair x refl) =
        fundamental-theorem-id' x refl
          ( λ y → inv ∘ cong f)
          ( λ y →
            is-equiv-comp' inv (cong f)
              ( is-emb-f x y)
              ( is-equiv-inv (f x) (f y)))

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-prop-map-emb : (f : B ↪ A) → is-prop-map (map-emb f)
    is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

  fib-emb-Prop : A ↪ B → B → Set-Prop (l1 ⊔ l2)
  pr1 (fib-emb-Prop f y) = fib (map-emb f) y
  pr2 (fib-emb-Prop f y) = is-prop-map-is-emb (is-emb-map-emb f) y

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  where

  abstract
    is-emb-pr1 : is-subtype B → is-emb (pr1 {B = B})
    is-emb-pr1 H =
      is-emb-is-prop-map (λ x → is-prop-equiv (equiv-fib-pr1 B x) (H x))

  emb-pr1 : is-subtype B → Σ A B ↪ A
  pr1 (emb-pr1 H) = pr1
  pr2 (emb-pr1 H) = is-emb-pr1 H

  equiv-ap-pr1 : is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
  pr1 (equiv-ap-pr1 is-subtype-B {s} {t}) = cong pr1
  pr2 (equiv-ap-pr1 is-subtype-B {s} {t}) = is-emb-pr1 is-subtype-B s t

  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 H x =
      is-prop-equiv' (equiv-fib-pr1 B x) (is-prop-map-is-emb H x)

{- Remark 12.2.5 -}

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  where

{- The following is a general construction that will help us show that
   the identity type of a subtype agrees with the identity type of the 
   original type. We already know that the first projection of a family of
   propositions is an embedding, but the following lemma still has its uses. -}

  abstract
    is-contr-total-Eq-substructure :
      {l3 : Level} {P : A → Set l3} →
      is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
      is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
    is-contr-total-Eq-substructure {l3} {P}
      is-contr-AB is-subtype-P a b p =
      is-contr-equiv
        ( Σ (Σ A B) (λ t → P (pr1 t)))
        ( equiv-right-swap-Σ)
        ( is-contr-equiv
          ( P a)
          ( left-unit-law-Σ-is-contr
            ( is-contr-AB)
            ( pair a b))
          ( is-proof-irrelevant-is-prop (is-subtype-P a) p))

module _
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (H : is-subtype B)
  where

  Eq-total-subtype : (Σ A B) → (Σ A B) → Set l1
  Eq-total-subtype p p' = Id (pr1 p) (pr1 p') 

  refl-Eq-total-subtype : (p : Σ A B) → Eq-total-subtype p p
  refl-Eq-total-subtype (pair x y) = refl

  Eq-eq-total-subtype : (p p' : Σ A B) → Id p p' → Eq-total-subtype p p'
  Eq-eq-total-subtype p .p refl = refl-Eq-total-subtype p

  abstract
    is-contr-total-Eq-total-subtype :
      (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype p))
    is-contr-total-Eq-total-subtype (pair x y) =
      is-contr-total-Eq-substructure (is-contr-total-path x) H x refl y

  abstract
    is-equiv-Eq-eq-total-subtype :
      (p p' : Σ A B) → is-equiv (Eq-eq-total-subtype p p')
    is-equiv-Eq-eq-total-subtype p =
      fundamental-theorem-id p
        ( refl-Eq-total-subtype p)
        ( is-contr-total-Eq-total-subtype p)
        ( Eq-eq-total-subtype p)

  equiv-Eq-eq-total-subtype :
    (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype p p')
  pr1 (equiv-Eq-eq-total-subtype p p') = Eq-eq-total-subtype p p'
  pr2 (equiv-Eq-eq-total-subtype p p') = is-equiv-Eq-eq-total-subtype p p'

  eq-subtype :
    {p p' : Σ A B} → Eq-total-subtype p p' → Id p p'
  eq-subtype {p} {p'} =
    map-inv-is-equiv (is-equiv-Eq-eq-total-subtype p p')
      
is-set :
  {i : Level} → Set i → Set i
is-set A = (x y : A) → is-prop (Id x y)

Set-Set :
  (i : Level) → Set (lsuc i)
Set-Set i = Σ (Set i) is-set

module _
  {l : Level} (X : Set-Set l)
  where

  type-Set : Set l
  type-Set = pr1 X

  abstract
    is-set-type-Set : is-set type-Set
    is-set-type-Set = pr2 X

  Id-Prop : (x y : type-Set) → Set-Prop l
  pr1 (Id-Prop x y) = Id x y
  pr2 (Id-Prop x y) = is-set-type-Set x y

axiom-K :
  {i : Level} → Set i → Set i
axiom-K A = (x : A) (p : Id x x) → Id refl p

module _
  {l : Level} {A : Set l}
  where

  abstract
    is-set-axiom-K' : axiom-K A → (x y : A) → all-elements-equal (Id x y)
    is-set-axiom-K' K x .x refl q with K x q
    ... | refl = refl

  abstract
    is-set-axiom-K : axiom-K A → is-set A
    is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y) 

  abstract
    axiom-K-is-set : is-set A → axiom-K A
    axiom-K-is-set H x p =
      ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙ 
      ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)

module _
  {l1 l2 : Level} {A : Set l1} (R : A → A → Set l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x =
      fundamental-theorem-id-retr x (i x)
        ( λ y →
          pair
            ( α y)
            ( λ r → eq-is-prop (p x y)))
      where
      α : (z : A) → Id x z → R x z
      α .x refl = ρ x

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x y = is-prop-is-equiv' (is-equiv-prop-in-id x y) (p x y)

abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ =
    is-set-prop-in-id
      Eq-ℕ
      is-prop-Eq-ℕ
      refl-Eq-ℕ
      eq-Eq-ℕ

ℕ-Set : Set-Set lzero
pr1 ℕ-Set = ℕ
pr2 ℕ-Set = is-set-ℕ

module _
  {l : Level} {A : Set l}
  where

  {- Next, we show that types with decidable equality are sets. To see this, we 
     will construct a fiberwise equivalence with the binary relation R that is
     defined by R x y := unit if (x = y), and empty otherwise. In order to
     define this relation, we first define a type family over
     ((x = y) + ¬(x = y)) that returns unit on the left and empty on the right.   -}
   
  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (Id x y) → Set lzero
  Eq-has-decidable-equality' x y (inl p) = unit
  Eq-has-decidable-equality' x y (inr f) = empty

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → Set lzero
  Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

  abstract
    is-prop-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (Id x y)) →
      is-prop (Eq-has-decidable-equality' x y t)
    is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
    is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

  abstract
    is-prop-Eq-has-decidable-equality :
      (d : has-decidable-equality A)
      {x y : A} → is-prop (Eq-has-decidable-equality d x y)
    is-prop-Eq-has-decidable-equality d {x} {y} =
      is-prop-Eq-has-decidable-equality' x y (d x y)

  abstract
    refl-Eq-has-decidable-equality :
      (d : has-decidable-equality A) (x : A) →
      Eq-has-decidable-equality d x x 
    refl-Eq-has-decidable-equality d x with d x x
    ... | inl α = star
    ... | inr f = f refl

  abstract
    Eq-has-decidable-equality-eq :
      (d : has-decidable-equality A) {x y : A} →
      Id x y → Eq-has-decidable-equality d x y
    Eq-has-decidable-equality-eq d {x} {.x} refl =
      refl-Eq-has-decidable-equality d x

  abstract
    eq-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (Id x y)) →
      Eq-has-decidable-equality' x y t → Id x y
    eq-Eq-has-decidable-equality' x y (inl p) t = p
    eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

  abstract
    eq-Eq-has-decidable-equality :
      (d : has-decidable-equality A) {x y : A} →
      Eq-has-decidable-equality d x y → Id x y
    eq-Eq-has-decidable-equality d {x} {y} =
      eq-Eq-has-decidable-equality' x y (d x y)

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality d =
      is-set-prop-in-id
        ( λ x y → Eq-has-decidable-equality d x y)
        ( λ x y → is-prop-Eq-has-decidable-equality d)
        ( λ x → refl-Eq-has-decidable-equality d x)
        ( λ x y → eq-Eq-has-decidable-equality d)

abstract
  is-emb-is-injective' : {l1 l2 : Level} {A : Set l1} (is-set-A : is-set A)
    {B : Set l2} (is-set-B : is-set B) (f : A → B) →
    is-injective f → is-emb f
  is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
    is-equiv-is-prop
      ( is-set-A x y)
      ( is-set-B (f x) (f y))
      ( is-injective-f)

  is-set-is-injective :
    {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} →
    is-set B → is-injective f → is-set A
  is-set-is-injective {f = f} H I =
    is-set-prop-in-id
      ( λ x y → Id (f x) (f y))
      ( λ x y → H (f x) (f y))
      ( λ x → refl)
      ( λ x y → I)

  is-emb-is-injective :
    {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} →
    is-set B → is-injective f → is-emb f
  is-emb-is-injective {f = f} H I =
    is-emb-is-injective' (is-set-is-injective H I) H f I

  is-prop-map-is-injective :
    {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} →
    is-set B → is-injective f → is-prop-map f
  is-prop-map-is-injective {f = f} H I =
    is-prop-map-is-emb (is-emb-is-injective H I)

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  data
    Eq-coprod : coprod A B → coprod A B → Set (l1 ⊔ l2)
    where
    Eq-eq-coprod-inl : (x y : A) → Id x y → Eq-coprod (inl x) (inl y)
    Eq-eq-coprod-inr : (x y : B) → Id x y → Eq-coprod (inr x) (inr y)

  refl-Eq-coprod : (x : coprod A B) → Eq-coprod x x
  refl-Eq-coprod (inl x) = Eq-eq-coprod-inl x x refl
  refl-Eq-coprod (inr x) = Eq-eq-coprod-inr x x refl

  Eq-eq-coprod : (x y : coprod A B) → Id x y → Eq-coprod x y
  Eq-eq-coprod x .x refl = refl-Eq-coprod x

  is-contr-total-Eq-coprod :
    (x : coprod A B) → is-contr (Σ (coprod A B) (Eq-coprod x))
  pr1 (pr1 (is-contr-total-Eq-coprod (inl x))) = inl x
  pr2 (pr1 (is-contr-total-Eq-coprod (inl x))) = Eq-eq-coprod-inl x x refl
  pr2
    ( is-contr-total-Eq-coprod (inl x))
    ( pair (inl .x) (Eq-eq-coprod-inl .x .x refl)) = refl
  pr1 (pr1 (is-contr-total-Eq-coprod (inr x))) = inr x
  pr2 (pr1 (is-contr-total-Eq-coprod (inr x))) = Eq-eq-coprod-inr x x refl
  pr2
    ( is-contr-total-Eq-coprod (inr x))
    ( pair .(inr x) (Eq-eq-coprod-inr .x .x refl)) = refl

  is-equiv-Eq-eq-coprod : (x y : coprod A B) → is-equiv (Eq-eq-coprod x y)
  is-equiv-Eq-eq-coprod x =
    fundamental-theorem-id x
      ( refl-Eq-coprod x)
      ( is-contr-total-Eq-coprod x)
      ( Eq-eq-coprod x)

  extensionality-coprod : (x y : coprod A B) → Id x y ≃ Eq-coprod x y
  pr1 (extensionality-coprod x y) = Eq-eq-coprod x y
  pr2 (extensionality-coprod x y) = is-equiv-Eq-eq-coprod x y

  module _
    (x y : A)
    where
    
    map-compute-Eq-coprod-inl-inl : Eq-coprod (inl x) (inl y) → Id x y
    map-compute-Eq-coprod-inl-inl (Eq-eq-coprod-inl .x .y p) = p

    issec-Eq-eq-coprod-inl :
      (map-compute-Eq-coprod-inl-inl ∘ Eq-eq-coprod-inl x y) ~ id
    issec-Eq-eq-coprod-inl p = refl

    isretr-Eq-eq-coprod-inl :
      (Eq-eq-coprod-inl x y ∘ map-compute-Eq-coprod-inl-inl) ~ id
    isretr-Eq-eq-coprod-inl (Eq-eq-coprod-inl .x .y p) = refl

    is-equiv-map-compute-Eq-coprod-inl-inl :
      is-equiv map-compute-Eq-coprod-inl-inl
    is-equiv-map-compute-Eq-coprod-inl-inl =
      is-equiv-has-inverse
        ( Eq-eq-coprod-inl x y)
        ( issec-Eq-eq-coprod-inl)
        ( isretr-Eq-eq-coprod-inl)

    compute-Eq-coprod-inl-inl : Eq-coprod (inl x) (inl y) ≃ Id x y
    pr1 compute-Eq-coprod-inl-inl = map-compute-Eq-coprod-inl-inl
    pr2 compute-Eq-coprod-inl-inl = is-equiv-map-compute-Eq-coprod-inl-inl

    compute-eq-coprod-inl-inl : Id {A = coprod A B} (inl x) (inl y) ≃ Id x y
    compute-eq-coprod-inl-inl =
      compute-Eq-coprod-inl-inl ∘e extensionality-coprod (inl x) (inl y)
      
    map-compute-eq-coprod-inl-inl : Id {A = coprod A B} (inl x) (inl y) → Id x y
    map-compute-eq-coprod-inl-inl = map-equiv compute-eq-coprod-inl-inl

  module _
    (x : A) (y : B)
    where

    map-compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) → empty
    map-compute-Eq-coprod-inl-inr ()

    is-equiv-map-compute-Eq-coprod-inl-inr :
      is-equiv map-compute-Eq-coprod-inl-inr
    is-equiv-map-compute-Eq-coprod-inl-inr =
      is-equiv-is-empty' map-compute-Eq-coprod-inl-inr

    compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) ≃ empty
    pr1 compute-Eq-coprod-inl-inr = map-compute-Eq-coprod-inl-inr
    pr2 compute-Eq-coprod-inl-inr = is-equiv-map-compute-Eq-coprod-inl-inr

    compute-eq-coprod-inl-inr : Id {A = coprod A B} (inl x) (inr y) ≃ empty
    compute-eq-coprod-inl-inr =
      compute-Eq-coprod-inl-inr ∘e extensionality-coprod (inl x) (inr y)
      
    is-empty-eq-coprod-inl-inr : is-empty (Id {A = coprod A B} (inl x) (inr y))
    is-empty-eq-coprod-inl-inr = map-equiv compute-eq-coprod-inl-inr

  module _
    (x : B) (y : A)
    where

    map-compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) → empty
    map-compute-Eq-coprod-inr-inl ()

    is-equiv-map-compute-Eq-coprod-inr-inl :
      is-equiv map-compute-Eq-coprod-inr-inl
    is-equiv-map-compute-Eq-coprod-inr-inl =
      is-equiv-is-empty' map-compute-Eq-coprod-inr-inl

    compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) ≃ empty
    pr1 compute-Eq-coprod-inr-inl = map-compute-Eq-coprod-inr-inl
    pr2 compute-Eq-coprod-inr-inl = is-equiv-map-compute-Eq-coprod-inr-inl

    compute-eq-coprod-inr-inl : Id {A = coprod A B} (inr x) (inl y) ≃ empty
    compute-eq-coprod-inr-inl =
      compute-Eq-coprod-inr-inl ∘e extensionality-coprod (inr x) (inl y)
      
    is-empty-eq-coprod-inr-inl : is-empty (Id {A = coprod A B} (inr x) (inl y))
    is-empty-eq-coprod-inr-inl = map-equiv compute-eq-coprod-inr-inl

  module _
    (x y : B)
    where
    
    map-compute-Eq-coprod-inr-inr : Eq-coprod (inr x) (inr y) → Id x y
    map-compute-Eq-coprod-inr-inr (Eq-eq-coprod-inr .x .y p) = p

    issec-Eq-eq-coprod-inr :
      (map-compute-Eq-coprod-inr-inr ∘ Eq-eq-coprod-inr x y) ~ id
    issec-Eq-eq-coprod-inr p = refl

    isretr-Eq-eq-coprod-inr :
      (Eq-eq-coprod-inr x y ∘ map-compute-Eq-coprod-inr-inr) ~ id
    isretr-Eq-eq-coprod-inr (Eq-eq-coprod-inr .x .y p) = refl

    is-equiv-map-compute-Eq-coprod-inr-inr :
      is-equiv map-compute-Eq-coprod-inr-inr
    is-equiv-map-compute-Eq-coprod-inr-inr =
      is-equiv-has-inverse
        ( Eq-eq-coprod-inr x y)
        ( issec-Eq-eq-coprod-inr)
        ( isretr-Eq-eq-coprod-inr)

    compute-Eq-coprod-inr-inr : Eq-coprod (inr x) (inr y) ≃ Id x y
    pr1 compute-Eq-coprod-inr-inr = map-compute-Eq-coprod-inr-inr
    pr2 compute-Eq-coprod-inr-inr = is-equiv-map-compute-Eq-coprod-inr-inr

    compute-eq-coprod-inr-inr : Id {A = coprod A B} (inr x) (inr y) ≃ Id x y
    compute-eq-coprod-inr-inr =
      compute-Eq-coprod-inr-inr ∘e extensionality-coprod (inr x) (inr y)

    map-compute-eq-coprod-inr-inr : Id {A = coprod A B} (inr x) (inr y) → Id x y
    map-compute-eq-coprod-inr-inr = map-equiv compute-eq-coprod-inr-inr

  is-injective-inl : is-injective (inl {A = A} {B = B})
  is-injective-inl {x} {y} = map-compute-eq-coprod-inl-inl x y
  
  is-injective-inr : is-injective (inr {A = A} {B = B})
  is-injective-inr {x} {y} =
    map-compute-eq-coprod-inr-inr x y

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where
  
  id-map-coprod : (map-coprod (id {A = A}) (id {A = B})) ~ id
  id-map-coprod (inl x) = refl
  id-map-coprod (inr x) = refl

module _
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : Set l1} {B : Set l2} {A' : Set l1'} {B' : Set l2'}
  {A'' : Set l1''} {B'' : Set l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
  where
  
  compose-map-coprod :
    (map-coprod (f' ∘ f) (g' ∘ g)) ~ ((map-coprod f' g') ∘ (map-coprod f g))
  compose-map-coprod (inl x) = refl
  compose-map-coprod (inr y) = refl

module _
  {l1 l2 l1' l2' : Level} {A : Set l1} {B : Set l2} {A' : Set l1'} {B' : Set l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g')
  where
  
  htpy-map-coprod : (map-coprod f g) ~ (map-coprod f' g')
  htpy-map-coprod (inl x) = cong inl (H x)
  htpy-map-coprod (inr y) = cong inr (K y)

module _
  {l1 l2 l1' l2' : Level} {A : Set l1} {B : Set l2} {A' : Set l1'} {B' : Set l2'}
  {f : A → A'} {g : B → B'}
  where

  abstract
    is-equiv-map-coprod : is-equiv f → is-equiv g → is-equiv (map-coprod f g)
    pr1
      ( pr1
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-coprod sf sg
    pr2
      ( pr1
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
        ( htpy-map-coprod Sf Sg)) ∙h
      ( id-map-coprod A' B')
    pr1
      ( pr2
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-coprod rf rg
    pr2
      ( pr2
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
        ( htpy-map-coprod Rf Rg)) ∙h
      ( id-map-coprod A B)
  
equiv-coprod :
  {l1 l2 l1' l2' : Level} {A : Set l1} {B : Set l2} {A' : Set l1'} {B' : Set l2'} →
  (A ≃ A') → (B ≃ B') → ((coprod A B) ≃ (coprod A' B'))
pr1 (equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f)) = map-coprod e f
pr2 (equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f)) =
  is-equiv-map-coprod is-equiv-e is-equiv-f

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where
  
  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coprod-inl-inl x))
          ( is-contr-total-path x))
        ( λ y → cong inl)

  emb-inl : A ↪ coprod A B
  pr1 emb-inl = inl
  pr2 emb-inl = is-emb-inl

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ B (Id x))
          ( equiv-tot (compute-eq-coprod-inr-inr x))
          ( is-contr-total-path x))
        ( λ y → cong inr)

  emb-inr : B ↪ coprod A B
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr

Fin : ℕ → Set lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

is-neg-one-Fin : {k : ℕ} → Fin k → Set lzero
is-neg-one-Fin {succ-ℕ k} x = Id x neg-one-Fin

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

is-zero-Fin : {k : ℕ} → Fin k → Set lzero
is-zero-Fin {succ-ℕ k} x = Id x zero-Fin

is-zero-Fin' : {k : ℕ} → Fin k → Set lzero
is-zero-Fin' {succ-ℕ k} x = Id zero-Fin x

is-nonzero-Fin : {k : ℕ} → Fin k → Set lzero
is-nonzero-Fin {succ-ℕ k} x = ¬ (is-zero-Fin x)

skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-zero-Fin {succ-ℕ k} (inl x) = inl (skip-zero-Fin x)
skip-zero-Fin {succ-ℕ k} (inr star) = inr star

-- We define the successor function on Fin k.

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ k} (inl x) = skip-zero-Fin x
succ-Fin {succ-ℕ k} (inr star) = zero-Fin

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (mod-succ-ℕ k n)

mod-two-ℕ : ℕ → Fin two-ℕ
mod-two-ℕ = mod-succ-ℕ one-ℕ

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

is-one-Fin : {k : ℕ} → Fin k → Set lzero
is-one-Fin {succ-ℕ k} x = Id x one-Fin

is-zero-or-one-Fin-two-ℕ :
  (x : Fin two-ℕ) → coprod (is-zero-Fin x) (is-one-Fin x)
is-zero-or-one-Fin-two-ℕ (inl (inr star)) = inl refl
is-zero-or-one-Fin-two-ℕ (inr star) = inr refl

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (one-Fin {succ-ℕ k}))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k

Eq-Fin : (k : ℕ) → Fin k → Fin k → Set lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

-- Exercise 7.5 (a)

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = cong inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

has-decidable-equality-Fin :
  {k : ℕ} (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin {k} x y =
  map-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x zero-Fin

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x neg-one-Fin

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin x)
is-decidable-is-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x one-Fin

is-set-empty : is-set empty
is-set-empty ()

empty-Set : Set-Set lzero
pr1 empty-Set = empty
pr2 empty-Set = is-set-empty

module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2}
  where

  abstract
    is-not-contractible-coprod-is-contr :
      is-contr A → is-contr B → ¬ (is-contr (coprod A B))
    is-not-contractible-coprod-is-contr HA HB HAB =
      is-empty-eq-coprod-inl-inr (center HA) (center HB) (eq-is-contr HAB)

-- Exercise 12.3 (b)

module _
  {l1 l2 : Level} {P : Set l1} {Q : Set l2}
  where

  abstract
    all-elements-equal-coprod :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (coprod P Q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inl p') =
      cong inl (is-prop-P p p')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inr q') =
      ex-falso (f p q')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inl p') =
      ex-falso (f p' q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inr q') =
      cong inr (is-prop-Q q q')
  
  abstract
    is-prop-coprod : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
    is-prop-coprod f is-prop-P is-prop-Q =
      is-prop-all-elements-equal
        ( all-elements-equal-coprod f
          ( eq-is-prop' is-prop-P)
          ( eq-is-prop' is-prop-Q))

data 𝕋 : Set lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 (zero-𝕋)

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ zero-ℕ = zero-𝕋
truncation-level-ℕ (succ-ℕ k) = succ-𝕋 (truncation-level-ℕ k)

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ zero-ℕ = neg-one-𝕋
truncation-level-minus-one-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-one-ℕ k)

truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = neg-two-𝕋
truncation-level-minus-two-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-two-ℕ k)

is-trunc : {i : Level} (k : 𝕋) → Set i → Set i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

module _
  {l1 l2 : Level} (k : 𝕋)
  where

  is-trunc-map : {A : Set l1} {B : Set l2} → (A → B) → Set (l1 ⊔ l2)
  is-trunc-map f = (y : _) → is-trunc k (fib f y)
  
  trunc-map : (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  trunc-map A B = Σ (A → B) is-trunc-map

module _
  {l1 l2 : Level} {k : 𝕋} {A : Set l1} {B : Set l2}
  where

  map-trunc-map : trunc-map k A B → A → B
  map-trunc-map = pr1

  abstract
    is-trunc-map-map-trunc-map :
      (f : trunc-map k A B) → is-trunc-map k (map-trunc-map f)
    is-trunc-map-map-trunc-map = pr2

-- We introduce some notation for the special case of 1-types --

is-1-type : {l : Level} → Set l → Set l
is-1-type = is-trunc one-𝕋

Set-1-Type : (l : Level) → Set (lsuc l)
Set-1-Type l = Σ (Set l) is-1-type

type-1-Type : {l : Level} → Set-1-Type l → Set l
type-1-Type = pr1

abstract
  is-1-type-type-1-Type :
    {l : Level} (A : Set-1-Type l) → is-1-type (type-1-Type A)
  is-1-type-type-1-Type = pr2

Id-Set : {l : Level} (X : Set-1-Type l) (x y : type-1-Type X) → Set-Set l
pr1 (Id-Set X x y) = Id x y
pr2 (Id-Set X x y) = is-1-type-type-1-Type X x y

-- We introduce some notation for the special case of 2-types --

is-2-type : {l : Level} → Set l → Set l
is-2-type = is-trunc (succ-𝕋 one-𝕋)

Set-2-Type : (l : Level) → Set (lsuc l)
Set-2-Type l = Σ (Set l) is-2-type

type-2-Type :
  {l : Level} → Set-2-Type l → Set l
type-2-Type = pr1

abstract
  is-2-type-type-2-Type :
    {l : Level} (A : Set-2-Type l) → is-2-type (type-2-Type A)
  is-2-type-type-2-Type = pr2

-- We introduce some notation for the universe of k-truncated types --

Set-Truncated-Type : 𝕋 → (l : Level) → Set (lsuc l)
Set-Truncated-Type k l = Σ (Set l) (is-trunc k)

module _
  {k : 𝕋} {l : Level}
  where
  
  type-Truncated-Type : Set-Truncated-Type k l → Set l
  type-Truncated-Type = pr1

  abstract
    is-trunc-type-Truncated-Type :
      (A : Set-Truncated-Type k l) → is-trunc k (type-Truncated-Type A)
    is-trunc-type-Truncated-Type = pr2

{- Remark 12.4.2

We can't formalise this remark in Agda, because universes are handled 
differently. -}

-- Proposition 12.4.3

-- We show that if a type is k-truncated, then it is (k+1)-truncated. --

abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {i : Level} {A : Set i} →
    is-trunc k A → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-trunc neg-two-𝕋 H =
    is-prop-is-contr H
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y =
    is-trunc-succ-is-trunc k (H x y)

abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : Set l1} {B : Set l2}
    (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
    is-trunc-succ-is-trunc k (is-trunc-f b)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → Set-Truncated-Type k l → Set-Truncated-Type (succ-𝕋 k) l
pr1 (truncated-type-succ-Truncated-Type k A) = type-Truncated-Type A
pr2 (truncated-type-succ-Truncated-Type k A) =
  is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A)

abstract
  is-set-is-prop :
    {l : Level} {P : Set l} → is-prop P → is-set P
  is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

set-Prop :
  {l : Level} → Set-Prop l → Set-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P

1-type-Set :
  {l : Level} → Set-Set l → Set-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A

-- We conclude that a contractible type is k-truncated for any k

abstract
  is-trunc-is-contr :
    {l : Level} (k : 𝕋) {A : Set l} → is-contr A → is-trunc k A
  is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
  is-trunc-is-contr (succ-𝕋 k) is-contr-A =
    is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)

abstract
  is-set-is-contr :
    {l : Level} {A : Set l} → is-contr A → is-set A
  is-set-is-contr = is-trunc-is-contr zero-𝕋

-- We also conclude that a proposition is (k+1)-truncated for any k

abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : Set l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

abstract
  is-trunc-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-empty k ()

abstract
  is-trunc-is-empty :
    {l : Level} (k : 𝕋) {A : Set l} → is-empty A → is-trunc (succ-𝕋 k) A
  is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))

-- Corollary 12.4.4

abstract
  is-trunc-Id : {l : Level} (k : 𝕋) {A : Set l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id neg-two-𝕋 is-trunc-A = is-prop-is-contr is-trunc-A
  is-trunc-Id (succ-𝕋 k) is-trunc-A x y =
    is-trunc-succ-is-trunc k {A = Id x y} (is-trunc-A x y)

-- Proposition 12.4.5

-- We show that k-truncated types are closed under equivalences --

abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : Set i} (B : Set j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
    is-contr-is-equiv B f is-equiv-f H
  is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (cong f {x} {y})
      ( is-emb-is-equiv is-equiv-f x y) (H (f x) (f y))

abstract
  is-set-is-equiv :
    {i j : Level} {A : Set i} (B : Set j) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-trunc-equiv :
    {i j : Level} (k : 𝕋) {A : Set i} (B : Set  j) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-set-equiv :
    {i j : Level} {A : Set i} (B : Set j) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : Set i) {B : Set j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-set-is-equiv' :
    {i j : Level} (A : Set i) {B : Set j} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-trunc-equiv' :
    {i j : Level} (k : 𝕋) (A : Set i) {B : Set j} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f

abstract
  is-set-equiv' :
    {i j : Level} (A : Set i) {B : Set j} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋

-- Corollary 12.4.6

-- We show that if A embeds into a (k+1)-type B, then A is a (k+1)-type. --

abstract
  is-trunc-is-emb :
    {i j : Level} (k : 𝕋) {A : Set i} {B : Set j} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k
      ( Id (f x) (f y))
      ( cong f {x} {y})
      ( Ef x y)
      ( H (f x) (f y))

abstract
  is-trunc-emb :
    {i j : Level} (k : 𝕋) {A : Set i} {B : Set j} (f : A ↪ B) →
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)


module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {b : B}
  where

  -- Characterizing the identity type of a fiber as the fiber of the action on
  -- paths

  fib-ap-eq-fib-fiberwise :
    (s t : fib f b) (p : Id (pr1 s) (pr1 t)) →
    (Id (tr (λ (a : A) → Id (f a) b) p (pr2 s)) (pr2 t)) →
    (Id (cong f p) ((pr2 s) ∙ (inv (pr2 t))))
  fib-ap-eq-fib-fiberwise (pair .x' p) (pair x' refl) refl =
    inv ∘ (concat right-unit refl)

  abstract
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
      (s t : fib f b) → is-fiberwise-equiv (fib-ap-eq-fib-fiberwise s t)
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise (pair x y) (pair .x refl) refl =
      is-equiv-comp
        ( fib-ap-eq-fib-fiberwise (pair x y) (pair x refl) refl)
        ( inv)
        ( concat right-unit refl)
        ( refl-htpy)
        ( is-equiv-concat right-unit refl)
        ( is-equiv-inv (y ∙ refl) refl)

  fib-ap-eq-fib :
    (s t : fib f b) → Id s t →
    fib (cong f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (fib-ap-eq-fib s .s refl) = refl
  pr2 (fib-ap-eq-fib s .s refl) = inv (right-inv (pr2 s))

  triangle-fib-ap-eq-fib :
    (s t : fib f b) →
    ( fib-ap-eq-fib s t) ~
    ( (tot (fib-ap-eq-fib-fiberwise s t)) ∘ (pair-eq-Σ {s = s} {t}))
  triangle-fib-ap-eq-fib (pair x refl) .(pair x refl) refl = refl

  abstract
    is-equiv-fib-ap-eq-fib : (s t : fib f b) → is-equiv (fib-ap-eq-fib s t)
    is-equiv-fib-ap-eq-fib s t =
      is-equiv-comp
        ( fib-ap-eq-fib s t)
        ( tot (fib-ap-eq-fib-fiberwise s t))
        ( pair-eq-Σ {s = s} {t})
        ( triangle-fib-ap-eq-fib s t)
        ( is-equiv-pair-eq-Σ s t)
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise s t))

module _
  {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x y : A}
  where

  {- We show that tr B p is an equivalence, for an path p and any type family B.
  -}
   
  inv-tr : Id x y → B y → B x
  inv-tr p = tr B (inv p)

  isretr-inv-tr : (p : Id x y) → ((inv-tr p ) ∘ (tr B p)) ~ id
  isretr-inv-tr refl b = refl

  issec-inv-tr : (p : Id x y) → ((tr B p) ∘ (inv-tr p)) ~ id
  issec-inv-tr refl b = refl

  abstract
    is-equiv-tr : (p : Id x y) → is-equiv (tr B p)
    is-equiv-tr p =
      is-equiv-has-inverse
        ( inv-tr p)
        ( issec-inv-tr p)
        ( isretr-inv-tr p)

  equiv-tr : Id x y → (B x) ≃ (B y)
  pr1 (equiv-tr p) = tr B p
  pr2 (equiv-tr p) = is-equiv-tr p
  
module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (x y : A)
  where
  
  eq-fib-fib-ap :
    (q : Id (f x) (f y)) → Id (pair x q) (pair y refl) → fib (cong f {x} {y}) q
  eq-fib-fib-ap q =
    (tr (fib (cong f)) right-unit) ∘ (fib-ap-eq-fib f (pair x q) (pair y refl))

  abstract
    is-equiv-eq-fib-fib-ap :
      (q : Id (f x) (f y)) → is-equiv (eq-fib-fib-ap q)
    is-equiv-eq-fib-fib-ap q =
      is-equiv-comp
        ( eq-fib-fib-ap q)
        ( tr (fib (cong f)) right-unit)
        ( fib-ap-eq-fib f (pair x q) (pair y refl))
        ( refl-htpy)
        ( is-equiv-fib-ap-eq-fib f (pair x q) (pair y refl))
        ( is-equiv-tr (fib (cong f)) right-unit)
        
module _
  {l1 l2 : Level} (k : 𝕋) {A : Set l1} {B : Set l2} (f : A → B)
  where
  
  abstract
    is-trunc-map-is-trunc-ap :
      ((x y : A) → is-trunc-map k (cong f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-is-trunc-ap is-trunc-ap-f b (pair x p) (pair x' p') =
      is-trunc-is-equiv k
        ( fib (cong f) (p ∙ (inv p')))
        ( fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-trunc-ap-f x x' (p ∙ (inv p')))

  abstract
    is-trunc-ap-is-trunc-map :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (cong f {x} {y})
    is-trunc-ap-is-trunc-map is-trunc-map-f x y p =
      is-trunc-is-equiv' k
        ( Id (pair x p) (pair y refl))
        ( eq-fib-fib-ap f x y p)
        ( is-equiv-eq-fib-fib-ap f x y p)
        ( is-trunc-map-f (f y) (pair x p) (pair y refl))

-- 

abstract
  is-trunc-pr1-is-trunc-fam :
    {i j : Level} (k : 𝕋) {A : Set i} (B : A → Set j) →
    ((x : A) → is-trunc k (B x)) → is-trunc-map k (pr1 {i} {j} {A} {B})
  is-trunc-pr1-is-trunc-fam k B H x =
    is-trunc-equiv k (B x) (equiv-fib-pr1 B x) (H x)

trunc-pr1 :
  {i j : Level} (k : 𝕋) {A : Set i} (B : A → Set-Truncated-Type k j) →
  trunc-map k (Σ A (λ x → pr1 (B x))) A
pr1 (trunc-pr1 k B) = pr1
pr2 (trunc-pr1 k B) =
  is-trunc-pr1-is-trunc-fam k (λ x → pr1 (B x)) (λ x → pr2 (B x))

abstract
  is-trunc-fam-is-trunc-pr1 : {i j : Level} (k : 𝕋) {A : Set i} (B : A → Set j) →
    is-trunc-map k (pr1 {i} {j} {A} {B}) → ((x : A) → is-trunc k (B x))
  is-trunc-fam-is-trunc-pr1 k B is-trunc-pr1 x =
    is-trunc-equiv k (fib pr1 x) (inv-equiv-fib-pr1 B x) (is-trunc-pr1 x)
    
abstract
  is-trunc-succ-subtype :
    {i j : Level} (k : 𝕋) {A : Set i} {P : A → Set j} →
    ((x : A) → is-prop (P x)) →
    is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (Σ A P)
  is-trunc-succ-subtype k H is-trunc-A =
    is-trunc-is-emb k pr1 (is-emb-pr1 H) is-trunc-A

abstract
  is-prop-subtype :
    {i j : Level} {A : Set i} {P : A → Set j} →
    ((x : A) → is-prop (P x)) → is-prop A → is-prop (Σ A P)
  is-prop-subtype = is-trunc-succ-subtype neg-two-𝕋

abstract
  is-set-subtype :
    {i j : Level} {A : Set i} {P : A → Set j} →
    ((x : A) → is-prop (P x)) → is-set A → is-set (Σ A P)
  is-set-subtype = is-trunc-succ-subtype neg-one-𝕋
  
module _
  {l1 l2 : Level} (k : 𝕋) {A : Set l1} {B : Set l2}
  where

  abstract
    is-trunc-coprod :
      is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
      is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inl y) =
      is-trunc-equiv (succ-𝕋 k)
        ( Id x y)
        ( compute-eq-coprod-inl-inl x y)
        ( is-trunc-A x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inr y) =
      is-trunc-is-empty k (is-empty-eq-coprod-inl-inr x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inr x) (inl y) =
      is-trunc-is-empty k (is-empty-eq-coprod-inr-inl x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inr x) (inr y) =
      is-trunc-equiv (succ-𝕋 k)
        ( Id x y)
        ( compute-eq-coprod-inr-inr x y)
        ( is-trunc-B x y)

abstract
  is-set-coprod : {l1 l2 : Level} {A : Set l1} {B : Set l2} →
    is-set A → is-set B → is-set (coprod A B)
  is-set-coprod = is-trunc-coprod neg-two-𝕋

coprod-Set :
  {l1 l2 : Level} (A : Set-Set l1) (B : Set-Set l2) → Set-Set (l1 ⊔ l2)
pr1 (coprod-Set (pair A is-set-A) (pair B is-set-B)) = coprod A B
pr2 (coprod-Set (pair A is-set-A) (pair B is-set-B)) =
  is-set-coprod is-set-A is-set-B

abstract
  is-set-unit : is-set unit
  is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

unit-Set : Set-Set lzero
pr1 unit-Set = unit
pr2 unit-Set = is-set-unit

abstract
  is-set-Fin : (n : ℕ) → is-set (Fin n)
  is-set-Fin zero-ℕ = is-set-empty
  is-set-Fin (succ-ℕ n) =
    is-set-coprod (is-set-Fin n) is-set-unit

Fin-Set : (n : ℕ) → Set-Set lzero
pr1 (Fin-Set n) = Fin n
pr2 (Fin-Set n) = is-set-Fin n


leq-Fin :
  {k : ℕ} → Fin k → Fin k → Set lzero
leq-Fin {succ-ℕ k} (inl x) (inl y) = leq-Fin x y
leq-Fin {succ-ℕ k} (inr x) (inl y) = empty
leq-Fin {succ-ℕ k} (inl x) (inr y) = unit
leq-Fin {succ-ℕ k} (inr x) (inr y) = unit

leq-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → leq-Fin x neg-one-Fin
leq-neg-one-Fin (inl x) = star
leq-neg-one-Fin (inr x) = star

refl-leq-Fin :
  {k : ℕ} (x : Fin k) → leq-Fin x x
refl-leq-Fin {succ-ℕ k} (inl x) = refl-leq-Fin x
refl-leq-Fin {succ-ℕ k} (inr star) = star

antisymmetric-leq-Fin :
  {k : ℕ} {x y : Fin k} → leq-Fin x y → leq-Fin y x → Id x y
antisymmetric-leq-Fin {succ-ℕ k} {inl x} {inl y} H K =
  cong inl (antisymmetric-leq-Fin H K)
antisymmetric-leq-Fin {succ-ℕ k} {inr star} {inr star} H K = refl

transitive-leq-Fin :
  {k : ℕ} {x y z : Fin k} → leq-Fin x y → leq-Fin {k} y z → leq-Fin {k} x z
transitive-leq-Fin {succ-ℕ k} {inl x} {inl y} {inl z} H K =
  transitive-leq-Fin {k} H K
transitive-leq-Fin {succ-ℕ k} {inl x} {inl y} {inr star} H K = star
transitive-leq-Fin {succ-ℕ k} {inl x} {inr star} {inr star} H K = star
transitive-leq-Fin {succ-ℕ k} {inr star} {inr star} {inr star} H K = star

concatenate-eq-leq-eq-Fin :
  {k : ℕ} {x1 x2 x3 x4 : Fin k} →
  Id x1 x2 → leq-Fin x2 x3 → Id x3 x4 → leq-Fin x1 x4
concatenate-eq-leq-eq-Fin refl H refl = H

leq-succ-Fin :
  {k : ℕ} (x : Fin k) → leq-Fin (inl-Fin k x) (succ-Fin (inl-Fin k x))
leq-succ-Fin {succ-ℕ k} (inl x) = leq-succ-Fin x
leq-succ-Fin {succ-ℕ k} (inr star) = star

abstract
  is-prop-leq-Fin :
    {k : ℕ} (x y : Fin k) → is-prop (leq-Fin x y)
  is-prop-leq-Fin {succ-ℕ k} (inl x) (inl y) = is-prop-leq-Fin x y
  is-prop-leq-Fin {succ-ℕ k} (inl x) (inr star) = is-prop-unit
  is-prop-leq-Fin {succ-ℕ k} (inr star) (inl y) = is-prop-empty
  is-prop-leq-Fin {succ-ℕ k} (inr star) (inr star) = is-prop-unit


emb-inl-Fin : (k : ℕ) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-inl-Fin k) = inl-Fin k
pr2 (emb-inl-Fin k) = is-emb-inl (Fin k) unit

is-inl-Fin : {k : ℕ} → Fin (succ-ℕ k) → Set lzero
is-inl-Fin {k} x = Σ (Fin k) (λ y → Id (inl y) x)

is-star-Fin : {k : ℕ} → Fin (succ-ℕ k) → Set lzero
is-star-Fin x = Id (inr star) x

is-star-is-not-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → ¬ (is-inl-Fin x) → is-star-Fin x
is-star-is-not-inl-Fin (inl x) H = ex-falso (H (pair x refl))
is-star-is-not-inl-Fin (inr star) H = refl

skip-Fin :
  {k : ℕ} → Fin (succ-ℕ k) → Fin k → Fin (succ-ℕ k)
skip-Fin {succ-ℕ k} (inl x) (inl y) = inl (skip-Fin x y)
skip-Fin {succ-ℕ k} (inl x) (inr y) = inr star
skip-Fin {succ-ℕ k} (inr x) y = inl y

abstract
  is-injective-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-injective (skip-Fin x)
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inl y} {inl z} p =
    cong
      ( inl)
      ( is-injective-skip-Fin x
        ( is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p))
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin {succ-ℕ k} (inr star) {y} {z} p =
    is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p

abstract
  is-emb-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-emb (skip-Fin x)
  is-emb-skip-Fin {k} x =
    is-emb-is-injective
      ( is-set-Fin (succ-ℕ k))
      ( is-injective-skip-Fin x)

emb-skip-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-skip-Fin x) = skip-Fin x
pr2 (emb-skip-Fin x) = is-emb-skip-Fin x

repeat-Fin :
  {k : ℕ} (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin {succ-ℕ k} (inl x) (inl y) = inl (repeat-Fin x y)
repeat-Fin {succ-ℕ k} (inl x) (inr star) = inr star
repeat-Fin {succ-ℕ k} (inr star) (inl y) = y
repeat-Fin {succ-ℕ k} (inr star) (inr star) = inr star

abstract
  is-almost-injective-repeat-Fin :
    {k : ℕ} (x : Fin k) {y z : Fin (succ-ℕ k)} →
    ¬ (Id (inl x) y) → ¬ (Id (inl x) z) →
    Id (repeat-Fin x y) (repeat-Fin x z) → Id y z
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inl z} f g p =
    cong
      ( inl)
      ( is-almost-injective-repeat-Fin x
        ( λ q → f (cong inl q))
        ( λ q → g (cong inl q))
        ( is-injective-inl p))
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inr star} f g p =
    ex-falso (Eq-Fin-eq p)
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inr star} {inl z} f g p =
    ex-falso (Eq-Fin-eq p)
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inl x) {inr star} {inr star} f g p =
    refl
  is-almost-injective-repeat-Fin {succ-ℕ k} (inr star) {inl y} {inl z} f g p =
    cong inl p
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inl y} {inr star} f g p =
    ex-falso (f (cong inl (inv p)))
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inr star} {inl z} f g p =
    ex-falso (g (cong inl p))
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inr star} {inr star} f g p = refl

is-decidable-is-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin x)
is-decidable-is-inl-Fin (inl x) = inl (pair x refl)
is-decidable-is-inl-Fin (inr star) = inr α
  where
  α : is-inl-Fin (inr star) → empty
  α (pair y p) = Eq-Fin-eq p 

cases-map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
  is-decidable (is-inl-Fin (map-emb f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin (map-emb f (inl x))) → Fin l
cases-map-reduce-emb-Fin f (inl (pair t p)) x d = repeat-Fin t (map-emb f (inl x))
cases-map-reduce-emb-Fin f (inr g) x (inl (pair y p)) = y
cases-map-reduce-emb-Fin f (inr g) x (inr h) =
  ex-falso (Eq-Fin-eq (is-injective-emb f ((inv p) ∙ q)))
  where
  p : is-star-Fin (map-emb f (inr star))
  p = is-star-is-not-inl-Fin (map-emb f (inr star)) g
  q : is-star-Fin (map-emb f (inl x))
  q = is-star-is-not-inl-Fin (map-emb f (inl x)) h

map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-emb-Fin f x =
  cases-map-reduce-emb-Fin f
    ( is-decidable-is-inl-Fin (map-emb f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin (map-emb f (inl x)))

abstract
  is-injective-cases-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l))
    (d : is-decidable (is-inl-Fin (map-emb f (inr star))))
    (x : Fin k) (e : is-decidable (is-inl-Fin (map-emb f (inl x))))
    (x' : Fin k) (e' : is-decidable  (is-inl-Fin (map-emb f (inl x')))) →
    Id (cases-map-reduce-emb-Fin f d x e) (cases-map-reduce-emb-Fin f d x' e') →
    Id x x'
  is-injective-cases-map-reduce-emb-Fin f (inl (pair t q)) x e x' e' p =
    is-injective-inl
      ( is-injective-is-emb
        ( is-emb-map-emb f)
        ( is-almost-injective-repeat-Fin t
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( p)))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p =
    is-injective-inl (is-injective-emb f ((inv q) ∙ (cong inl p ∙ q')))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inr h) p =
    ex-falso
    ( Eq-Fin-eq
      ( is-injective-emb f
        ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
          ( is-star-is-not-inl-Fin (pr1 f (inl x')) h))))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inr h) x' (inl (pair y' q')) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
            ( is-star-is-not-inl-Fin (pr1 f (inl x)) h))))
  is-injective-cases-map-reduce-emb-Fin f (inr g) x (inr h) x' (inr k) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
            ( is-star-is-not-inl-Fin (pr1 f (inl x)) h))))

abstract
  is-injective-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-injective (map-reduce-emb-Fin f)
  is-injective-map-reduce-emb-Fin f {x} {y} =
    is-injective-cases-map-reduce-emb-Fin f
      ( is-decidable-is-inl-Fin (map-emb f (inr star)))
      ( x)
      ( is-decidable-is-inl-Fin (map-emb f (inl x)))
      ( y)
      ( is-decidable-is-inl-Fin (map-emb f (inl y)))

abstract
  is-emb-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-emb (map-reduce-emb-Fin f)
  is-emb-map-reduce-emb-Fin f =
    is-emb-is-injective (is-set-Fin _) (is-injective-map-reduce-emb-Fin f)

reduce-emb-Fin :
  (k l : ℕ) → Fin (succ-ℕ k) ↪ Fin (succ-ℕ l) → Fin k ↪ Fin l
pr1 (reduce-emb-Fin k l f) = map-reduce-emb-Fin f
pr2 (reduce-emb-Fin k l f) = is-emb-map-reduce-emb-Fin f

-- We now come to the main result

abstract
  leq-emb-Fin :
    {k l : ℕ} → Fin k ↪ Fin l → k ≤-ℕ l
  leq-emb-Fin {zero-ℕ} {zero-ℕ} f = refl-leq-ℕ zero-ℕ
  leq-emb-Fin {succ-ℕ k} {zero-ℕ} f = ex-falso (map-emb f (inr star))
  leq-emb-Fin {zero-ℕ} {succ-ℕ l} f = leq-zero-ℕ (succ-ℕ l)
  leq-emb-Fin {succ-ℕ k} {succ-ℕ l} f = leq-emb-Fin (reduce-emb-Fin k l f)

abstract
  leq-is-emb-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-emb f → k ≤-ℕ l
  leq-is-emb-Fin {f = f} H = leq-emb-Fin (pair f H)

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
  leq-is-injective-Fin H = leq-is-emb-Fin (is-emb-is-injective (is-set-Fin _) H)

abstract
  is-not-emb-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-emb f)
  is-not-emb-le-Fin {k} {l} f p =
    functor-neg (leq-is-emb-Fin) (contradiction-le-ℕ l k p)

is-not-injective :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → Set (l1 ⊔ l2)
is-not-injective f = ¬ (is-injective f)

abstract
  is-not-injective-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → is-not-injective f
  is-not-injective-le-Fin {k} {l} f p =
    functor-neg (is-emb-is-injective (is-set-Fin l)) (is-not-emb-le-Fin f p)

abstract
  is-not-injective-map-Fin-succ-Fin :
    {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → is-not-injective f 
  is-not-injective-map-Fin-succ-Fin {k} f =
    is-not-injective-le-Fin f (le-succ-ℕ {k})

module _
  {l1 l2 l3 l4 : Level} {A : Set l1} {B : Set l2} {C : Set l3} {D : Set l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h))
  where

  {-

  We assumed a commuting square

          h
    A --------> C
    |           |
   f|           |g
    V           V
    B --------> D
          i                                                                   -}
          
  abstract
    is-equiv-top-is-equiv-left-square :
      is-equiv i → is-equiv f → is-equiv g → is-equiv h
    is-equiv-top-is-equiv-left-square Ei Ef Eg =
      is-equiv-right-factor (i ∘ f) g h H Eg (is-equiv-comp' i f Ef Ei)

  abstract
    is-equiv-top-is-equiv-bottom-square :
      is-equiv f → is-equiv g → is-equiv i → is-equiv h
    is-equiv-top-is-equiv-bottom-square Ef Eg Ei =
      is-equiv-right-factor (i ∘ f) g h H Eg (is-equiv-comp' i f Ef Ei)

  abstract
    is-equiv-bottom-is-equiv-top-square :
      is-equiv f → is-equiv g → is-equiv h → is-equiv i
    is-equiv-bottom-is-equiv-top-square Ef Eg Eh = 
      is-equiv-left-factor' i f (is-equiv-comp (i ∘ f) g h H Eh Eg) Ef

  abstract
    is-equiv-left-is-equiv-right-square :
      is-equiv h → is-equiv i → is-equiv g → is-equiv f
    is-equiv-left-is-equiv-right-square Eh Ei Eg =
      is-equiv-right-factor' i f Ei (is-equiv-comp (i ∘ f) g h H Eh Eg)

  abstract
    is-equiv-right-is-equiv-left-square :
      is-equiv h → is-equiv i → is-equiv f → is-equiv g
    is-equiv-right-is-equiv-left-square Eh Ei Ef =
      is-equiv-left-factor (i ∘ f) g h H (is-equiv-comp' i f Ef Ei) Eh
      
module _
  {l1 l2 : Level} {A : Set l1} {B : Set l2} (f g : A → B) (H : f ~ g)
  where

  abstract
    is-emb-htpy : is-emb g → is-emb f
    is-emb-htpy is-emb-g x y =
      is-equiv-top-is-equiv-left-square
        ( cong g)
        ( concat' (f x) (H y))
        ( cong f)
        ( concat (H x) (g y))
        ( htpy-nat H)
        ( is-equiv-concat (H x) (g y))
        ( is-emb-g x y)
        ( is-equiv-concat' (f x) (H y))
        
module _
  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
  where

  abstract
    is-emb-comp :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
      is-emb h → is-emb f
    is-emb-comp f g h H is-emb-g is-emb-h =
      is-emb-htpy f (g ∘ h) H
        ( λ x y → is-equiv-comp (cong (g ∘ h)) (cong g) (cong h) cong-comp
          ( is-emb-h x y)
          ( is-emb-g (h x) (h y)))

  abstract
    is-emb-comp' :
      (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
    is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

    comp-emb :
      (B ↪ C) → (A ↪ B) → (A ↪ C)
    pr1 (comp-emb (pair g H) (pair f K)) = g ∘ f
    pr2 (comp-emb (pair g H) (pair f K)) = is-emb-comp' g f H K

  abstract
    is-emb-right-factor :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
      is-emb f → is-emb h
    is-emb-right-factor f g h H is-emb-g is-emb-f x y =
      is-equiv-right-factor
        ( cong (g ∘ h))
        ( cong g)
        ( cong h)
        ( cong-comp)
        ( is-emb-g (h x) (h y))
        ( is-emb-htpy (g ∘ h) f (inv-htpy H) is-emb-f x y)

  abstract
    is-emb-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
      is-emb-comp f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ {x} {y} e = eq-Eq-ℕ x y (Eq-eq-ℕ e)

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = Peano-8 y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin {succ-ℕ k} (inr star) =
  succ-le-ℕ k
  
is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  cong inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p =
  refl
                                                                    
is-emb-nat-Fin : {k : ℕ} → is-emb (nat-Fin {k})
is-emb-nat-Fin {k} = is-emb-is-injective is-set-ℕ is-injective-nat-Fin

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
pr1 (emb-nat-Fin k) = nat-Fin
pr2 (emb-nat-Fin k) = is-emb-nat-Fin

abstract
  no-embedding-ℕ-Fin :
    (k : ℕ) → ¬ (ℕ ↪ Fin k)
  no-embedding-ℕ-Fin k e =
    contradiction-leq-ℕ k k
      ( refl-leq-ℕ k)
      ( leq-emb-Fin (comp-emb e (emb-nat-Fin (succ-ℕ k))))
