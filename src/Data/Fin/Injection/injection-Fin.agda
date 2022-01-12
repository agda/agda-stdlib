------------------------------------------------------------------------
-- The Agda standard library
--
-- Proving that Fin m ↪ Fin n implies that m ≤ n.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Injection.injection-Fin where
            
open import Data.Empty
  using ()
  renaming
    ( ⊥ to empty;
      ⊥-elim to ex-falso)

open import Data.Nat
  using
    ( ℕ)
  renaming
    ( suc to succ-ℕ;
      zero to zero-ℕ)

open import Data.Nat.Properties
  using ()
  renaming
    ( suc-injective to is-injective-succ-ℕ)
      
open import Data.Product using (Σ)
  renaming (_,_ to pair; proj₁ to pr1; proj₂ to pr2)

open import Data.Sum.Base using ()
  renaming (_⊎_ to coprod; inj₁ to inl; inj₂ to inr)

open import Data.Unit
  using ()
  renaming
    ( ⊤ to unit;
      tt to star)
      
open import Function.Base
  using
    ( id;
      _∘_)

open import Function.Definitions
  using
    ( Injective)

open import Level
  using
    ( Level; _⊔_)
  renaming
    ( zero to lzero;
      suc to lsuc)

open import Relation.Binary.PropositionalEquality.Core
  using
    ( refl; cong)
  renaming
    ( _≡_ to Id;
      sym to inv;
      trans to _∙_)

open import Relation.Nullary
  using
    ( ¬_)

-- We declare private definitions for things that already exist in agda-stdlib

private

  module _
    {l : Level} (A : Set l)
    where
    
    is-empty : Set l
    is-empty = ¬ A

    is-nonempty : Set l
    is-nonempty = ¬ is-empty


  module _
    {l1 l2 : Level} {A : Set l1} {B : Set l2}
    where

    is-injective : (A → B) → Set (l1 ⊔ l2)
    is-injective f = Injective Id Id f

    is-not-injective : (A → B) → Set (l1 ⊔ l2)
    is-not-injective f = ¬ (is-injective f)

  _↣_ : {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
  A ↣ B = Σ (A → B) is-injective

  module _
    {l1 l2 : Level} {A : Set l1} {B : Set l2}
    where

    map-inj : A ↣ B → A → B
    map-inj f = pr1 f

    is-injective-map-inj : (f : A ↣ B) → is-injective (map-inj f)
    is-injective-map-inj f = pr2 f

  module _
    {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3}
    where

    is-injective-comp :
      {g : B → C} {f : A → B} →
      is-injective g → is-injective f → is-injective (g ∘ f)
    is-injective-comp H K p = K (H p)

    _∘i_ : B ↣ C → A ↣ B → A ↣ C
    pr1 (g ∘i f) = map-inj g ∘ map-inj f
    pr2 (g ∘i f) =
      is-injective-comp (is-injective-map-inj g) (is-injective-map-inj f)

  module _
    {l1 l2 : Level} {A : Set l1} {B : Set l2}
    where
  
    is-injective-inl : is-injective (inl {A = A} {B = B})
    is-injective-inl {x} {y} refl = refl 
    
    is-injective-inr : is-injective (inr {A = A} {B = B})
    is-injective-inr {x} {y} refl = refl

functor-neg : {l1 l2 : Level} {P : Set l1} {Q : Set l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

map-coprod :
  {l1 l2 l1' l2' : Level}
  {A : Set l1} {B : Set l2} {A' : Set l1'} {B' : Set l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
map-coprod f g (inl x) = inl (f x)
map-coprod f g (inr y) = inr (g y)

-- Decidability

is-decidable : {l : Level} (A : Set l) → Set l
is-decidable A = coprod A (¬ A)

is-decidable-iff :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g (inl x) = inl (f x)
is-decidable-iff f g (inr y) = inr (functor-neg g y)

is-decidable-function-type :
  {l1 l2 : Level} {A : Set l1} {B : Set l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-neg :
  {l : Level} {A : Set l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d (inr id)
   
-- The natural numbers

is-zero-ℕ : ℕ → Set lzero
is-zero-ℕ n = Id n zero-ℕ

is-nonzero-ℕ : ℕ → Set lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → Set lzero
is-one-ℕ n = Id n 1

Peano-8 : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
Peano-8 x ()

-- Inequality on ℕ

leq-ℕ : ℕ → ℕ → Set lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ

leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star

refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

-- Strict inequality on ℕ

le-ℕ : ℕ → ℕ → Set lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

le-succ-ℕ : {x : ℕ} → le-ℕ x (succ-ℕ x)
le-succ-ℕ {zero-ℕ} = star
le-succ-ℕ {succ-ℕ x} = le-succ-ℕ {x}

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = Peano-8 y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)

--------------------------------------------------------------------------------
      
-- Finite types

Fin : ℕ → Set lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

Eq-Fin : (k : ℕ) → Fin k → Fin k → Set lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

is-inl-Fin : {k : ℕ} → Fin (succ-ℕ k) → Set lzero
is-inl-Fin {k} x = Σ (Fin k) (λ y → Id (inl y) x)

is-star-Fin : {k : ℕ} → Fin (succ-ℕ k) → Set lzero
is-star-Fin x = Id (inr star) x

is-star-is-not-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → ¬ (is-inl-Fin x) → is-star-Fin x
is-star-is-not-inl-Fin (inl x) H = ex-falso (H (pair x refl))
is-star-is-not-inl-Fin (inr star) H = refl

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
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inr star} f g ()
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inr star} {inl z} f g ()
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
  α (pair y ())

cases-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) →
  is-decidable (is-inl-Fin (map-inj f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin (map-inj f (inl x))) → Fin l
cases-map-reduce-inj-Fin f (inl (pair t p)) x d =
  repeat-Fin t (map-inj f (inl x))
cases-map-reduce-inj-Fin f (inr g) x (inl (pair y p)) = y
cases-map-reduce-inj-Fin f (inr g) x (inr h) =
  ex-falso (Eq-Fin-eq (is-injective-map-inj f ((inv p) ∙ q)))
  where
  p : is-star-Fin (map-inj f (inr star))
  p = is-star-is-not-inl-Fin (map-inj f (inr star)) g
  q : is-star-Fin (map-inj f (inl x))
  q = is-star-is-not-inl-Fin (map-inj f (inl x)) h

map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-inj-Fin f x =
  cases-map-reduce-inj-Fin f
    ( is-decidable-is-inl-Fin (map-inj f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin (map-inj f (inl x)))

is-injective-cases-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l))
  (d : is-decidable (is-inl-Fin (map-inj f (inr star))))
  (x : Fin k) (e : is-decidable (is-inl-Fin (map-inj f (inl x))))
  (x' : Fin k) (e' : is-decidable  (is-inl-Fin (map-inj f (inl x')))) →
  Id (cases-map-reduce-inj-Fin f d x e) (cases-map-reduce-inj-Fin f d x' e') →
  Id x x'
is-injective-cases-map-reduce-inj-Fin f (inl (pair t q)) x e x' e' p =
  is-injective-inl
    ( is-injective-map-inj f
      ( is-almost-injective-repeat-Fin t
        ( λ α → Eq-Fin-eq (is-injective-map-inj f ((inv q) ∙ α)))
        ( λ α → Eq-Fin-eq (is-injective-map-inj f ((inv q) ∙ α)))
        ( p)))
is-injective-cases-map-reduce-inj-Fin
  f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p =
  is-injective-inl (is-injective-map-inj f ((inv q) ∙ (cong inl p ∙ q')))
is-injective-cases-map-reduce-inj-Fin
  f (inr g) x (inl (pair y q)) x' (inr h) p =
  ex-falso
    ( Eq-Fin-eq
      ( is-injective-map-inj f
        ( ( inv (is-star-is-not-inl-Fin (map-inj f (inr star)) g)) ∙
          ( is-star-is-not-inl-Fin (map-inj f (inl x')) h))))
is-injective-cases-map-reduce-inj-Fin
  f (inr g) x (inr h) x' (inl (pair y' q')) p =
  ex-falso
    ( Eq-Fin-eq
      ( is-injective-map-inj f
        ( ( inv (is-star-is-not-inl-Fin (map-inj f (inr star)) g)) ∙
          ( is-star-is-not-inl-Fin (map-inj f (inl x)) h))))
is-injective-cases-map-reduce-inj-Fin f (inr g) x (inr h) x' (inr k) p =
  ex-falso
    ( Eq-Fin-eq
      ( is-injective-map-inj f
        ( ( inv (is-star-is-not-inl-Fin (map-inj f (inr star)) g)) ∙
          ( is-star-is-not-inl-Fin (map-inj f (inl x)) h))))

is-injective-map-reduce-inj-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↣ Fin (succ-ℕ l)) →
  is-injective (map-reduce-inj-Fin f)
is-injective-map-reduce-inj-Fin f {x} {y} =
  is-injective-cases-map-reduce-inj-Fin f
    ( is-decidable-is-inl-Fin (map-inj f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin (map-inj f (inl x)))
    ( y)
    ( is-decidable-is-inl-Fin (map-inj f (inl y)))

reduce-inj-Fin : (k l : ℕ) → Fin (succ-ℕ k) ↣ Fin (succ-ℕ l) → Fin k ↣ Fin l
pr1 (reduce-inj-Fin k l f) = map-reduce-inj-Fin f
pr2 (reduce-inj-Fin k l f) = is-injective-map-reduce-inj-Fin f

-- We now come to the main result

leq-inj-Fin : {k l : ℕ} → Fin k ↣ Fin l → k ≤-ℕ l
leq-inj-Fin {zero-ℕ} {zero-ℕ} (pair f H) = refl-leq-ℕ 0
leq-inj-Fin {zero-ℕ} {succ-ℕ l} (pair f H) = leq-zero-ℕ (succ-ℕ l)
leq-inj-Fin {succ-ℕ k} {zero-ℕ} (pair f H) = ex-falso (f (inr star))
leq-inj-Fin {succ-ℕ k} {succ-ℕ l} (pair f H) =
  leq-inj-Fin (reduce-inj-Fin k l (pair f H))

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
  leq-is-injective-Fin H = leq-inj-Fin (pair _ H)

abstract
  is-not-injective-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → is-not-injective f
  is-not-injective-le-Fin {k} {l} f p =
    functor-neg leq-is-injective-Fin (contradiction-le-ℕ l k p)

abstract
  is-not-injective-map-Fin-succ-Fin :
    {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → is-not-injective f 
  is-not-injective-map-Fin-succ-Fin {k} f =
    is-not-injective-le-Fin f (le-succ-ℕ {k})

-- Finally, we show that there is no injection ℕ ↣ Fin k

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

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

inj-nat-Fin : (k : ℕ) → Fin k ↣ ℕ
pr1 (inj-nat-Fin k) = nat-Fin
pr2 (inj-nat-Fin k) = is-injective-nat-Fin

no-injection-ℕ-Fin : (k : ℕ) → ¬ (ℕ ↣ Fin k)
no-injection-ℕ-Fin k f =
  contradiction-leq-ℕ k k
    ( refl-leq-ℕ k)
    ( leq-inj-Fin (f ∘i inj-nat-Fin (succ-ℕ k)))
