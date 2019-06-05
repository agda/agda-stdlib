------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Nary.NonDependent where

------------------------------------------------------------------------
-- Concrete examples can be found in README.Nary. This file's comments
-- are more focused on the implementation details and the motivations
-- behind the design decisions.
------------------------------------------------------------------------

open import Level using (Level; 0ℓ; _⊔_; Lift)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit.Base
open import Function.Core using (_∘′_; _$′_; const; flip)
open import Relation.Unary using (IUniversal)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Type Definitions

-- We want to define n-ary function spaces and generic n-ary operations on
-- them such as (un)currying, zipWith, alignWith, etc.

-- We want users to be able to use these seamlessly whenever n is concrete.

-- In other words, we want Agda to infer the sets `A₁, ⋯, Aₙ` when we write
-- `uncurryₙ n f` where `f` has type `A₁ → ⋯ → Aₙ → B`. For this to happen,
-- we need the structure in which these Sets are stored to effectively
-- η-expand to `A₁, ⋯, Aₙ` when the parameter `n` is known.

-- Hence the following definitions:
------------------------------------------------------------------------

-- First, a "vector" of `n` Levels (defined by induction on n so that it
-- may be built by η-expansion and unification). Each Level will be that
-- of one of the Sets we want to take the n-ary product of.

Levels : ℕ → Set
Levels zero    = ⊤
Levels (suc n) = Level × Levels n

-- The overall Level of a `n` Sets of respective levels `l₁, ⋯, lₙ` will
-- be the least upper bound `l₁ ⊔ ⋯ ⊔ lₙ` of all of the Levels involved.
-- Hence the following definition of n-ary least upper bound:

⨆ : ∀ n → Levels n → Level
⨆ zero    _        = Level.zero
⨆ (suc n) (l , ls) = l ⊔ (⨆ n ls)

-- Second, a "vector" of `n` Sets whose respective Levels are determined
-- by the `Levels n` input.

Sets : ∀ n (ls : Levels n) → Set (Level.suc (⨆ n ls))
Sets zero    _        = Lift _ ⊤
Sets (suc n) (l , ls) = Set l × Sets n ls

-- Third, a function type whose domains are given by a "vector" of `n` Sets
-- `A₁, ⋯, Aₙ` and whose codomain is `B`. `Arrows` forms such a type of
-- shape `A₁ → ⋯ → Aₙ → B` by induction on `n`.

Arrows : ∀ n {r ls} → Sets n ls → Set r → Set (r ⊔ (⨆ n ls))
Arrows zero    _        b = b
Arrows (suc n) (a , as) b = a → Arrows n as b

-- We introduce a notation for this definition

infixr 0 _⇉_
_⇉_ : ∀ {n ls r} → Sets n ls → Set r → Set (r ⊔ (⨆ n ls))
_⇉_ = Arrows _



------------------------------------------------------------------------
-- Operations on Levels

lmap : (Level → Level) → ∀ n → Levels n → Levels n
lmap f zero    ls       = _
lmap f (suc n) (l , ls) = f l , lmap f n ls

ltabulate : ∀ n → (Fin n → Level) → Levels n
ltabulate zero    f = _
ltabulate (suc n) f = f zero , ltabulate n (f ∘′ suc)

lreplicate : ∀ n → Level → Levels n
lreplicate n ℓ = ltabulate n (const ℓ)

0ℓs : ∀[ Levels ]
0ℓs = lreplicate _ 0ℓ


------------------------------------------------------------------------
-- Operations on Sets

_<$>_ : (∀ {l} → Set l → Set l) →
        ∀ {n ls} → Sets n ls → Sets n ls
_<$>_ f {zero}   as        = _
_<$>_ f {suc n}  (a , as)  = f a , f <$> as

-- generalised map

smap : ∀ f → (∀ {l} → Set l → Set (f l)) →
       ∀ n {ls} → Sets n ls → Sets n (lmap f n ls)
smap f F zero    as       = _
smap f F (suc n) (a , as) = F a , smap f F n as


------------------------------------------------------------------------
-- Operations on Functions

-- mapping under n arguments

mapₙ : ∀ n {ls} {as : Sets n ls} → (B → C) → as ⇉ B → as ⇉ C
mapₙ zero    f v = f v
mapₙ (suc n) f g = mapₙ n f ∘′ g

-- compose function at the n-th position

_%=_⊢_ : ∀ n {ls} {as : Sets n ls} → (A → B) → as ⇉ (B → C) → as ⇉ (A → C)
n %= f ⊢ g = mapₙ n (_∘′ f) g

-- partially apply function at the n-th position

_∷=_⊢_ : ∀ n {ls} {as : Sets n ls} → A → as ⇉ (A → B) → as ⇉ B
n ∷= x ⊢ g = mapₙ n (_$′ x) g

-- hole at the n-th position

holeₙ : ∀ n {ls} {as : Sets n ls} → (A → as ⇉ B) → as ⇉ (A → B)
holeₙ zero    f = f
holeₙ (suc n) f = holeₙ n ∘′ flip f

-- function constant in its n first arguments

-- Note that its type will only be inferred if it is used in a context
-- specifying what the type of the function ought to be. Just like the
-- usual const: there is no way to infer its domain from its argument.

constₙ : ∀ n {ls r} {as : Sets n ls} {b : Set r} → b → as ⇉ b
constₙ zero    v = v
constₙ (suc n) v = const (constₙ n v)

