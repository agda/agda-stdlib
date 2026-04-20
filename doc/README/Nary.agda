------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the generic n-ary operations the stdlib provides
-- can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module README.Nary where

open import Level using (Level)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ; #_; inject₁)
open import Data.List
open import Data.List.Properties
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (id; flip; _∘′_)
open import Relation.Nullary
open import Relation.Binary.Definitions using (module Tri); open Tri
open import Relation.Binary.PropositionalEquality

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

------------------------------------------------------------------------
-- Introduction
------------------------------------------------------------------------

-- Function.Nary.NonDependent and Data.Product.N-ary.Heterogeneous provide
-- a generic representation of n-ary heterogeneous (non dependent) products
-- and the corresponding types of (non-dependent) n-ary functions. The
-- representation works well with inference thus allowing us to use generic
-- combinators to manipulate such functions.

open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Relation.Nary


------------------------------------------------------------------------
-- Generalised equality-manipulating combinators
------------------------------------------------------------------------

-- By default the standard library provides users with (we are leaving out
-- the implicit arguments here):
--
-- cong   : (f : A₁      → B) → a₁ ≡ b₁           → f a₁   ≡ f b₁
-- cong₂  : (f : A₁ → A₂ → B) → a₁ ≡ b₁ → a₂ ≡ b₂ → f a₁ a₂ ≡ f b₁ b₂
--
-- and
--
-- subst  : (P : A₁      → Set p) → a₁ ≡ b₁           → P a₁    → P b₁
-- subst₂ : (P : A₁ → A₂ → Set p) → a₁ ≡ b₁ → a₂ ≡ b₂ → P a₁ a₂ → P b₁ b₂
--
-- This pattern can be generalised to any natural number `n`. Thanks to our
-- library for n-ary functions, we can write the types and implementations
-- of `congₙ` and `substₙ`.

------------------------------------------------------------------------
-- congₙ : ∀ n (f : A₁ → ⋯ → Aₙ → B) →
--         a₁ ≡ b₁ → ⋯ aₙ ≡ bₙ → f a₁ ⋯ aₙ ≡ f b₁ ⋯ bₙ

-- It may be used directly to prove something:

_ : ∀ (as bs cs : List ℕ) →
       zip (zip (as ++ []) (map id cs)) (reverse (reverse bs))
     ≡ zip (zip as cs) bs
_ = λ as bs cs → congₙ 3 (λ as bs → zip (zip as bs))
                         (++-identityʳ as)
                         (map-id cs)
                         (reverse-involutive bs)

-- Or as part of a longer derivation:

_ : ∀ m n p q → suc (m + (p * n) + (q ^ (m + n)))
              ≡ (m + 0) + (n * p) + (q ^ m * q ^ n) + 1
_ = λ m n p q → begin
    suc (m + (p * n) + (q ^ (m + n))) ≡⟨ +-comm 1 _ ⟩
    m + (p * n) + (q ^ (m + n)) + 1   ≡⟨ congₙ 3 (λ m n p → m + n + p + 1)
                                                 (+-comm 0 m)
                                                 (*-comm p n)
                                                 (^-distribˡ-+-* q m n)
                                       ⟩
    m + 0 + n * p + (q ^ m) * (q ^ n) + 1 ∎ where open ≡-Reasoning

-- Partial application of the functional argument is fine: the number of arguments
-- `congₙ` is going to take is determined by its first argument (a natural number)
-- and not by the type of the function it works on.

_ : ∀ m → (m +_) ≡ ((m + 0) +_)
_ = λ m → congₙ 1 _+_ (+-comm 0 m)

-- We don't have to work on the function's first argument either: we can just as
-- easily use `congₙ` to act on the second one by `flip`ping it. See `holeₙ` for
-- a generalisation of this idea allowing to target *any* of the function's
-- arguments and not just the first or second one.

_ : ∀ m → (_+ m) ≡ (_+ (m + 0))
_ = λ m → congₙ 1 (flip _+_) (+-comm 0 m)

------------------------------------------------------------------------
-- substₙ : (P : A₁ → ⋯ → Aₙ → Set p) →
--          a₁ ≡ b₁ → ⋯ aₙ ≡ bₙ → P a₁ ⋯ aₙ → P b₁ ⋯ bₙ

-- We can play the same type of game with subst

open import Agda.Builtin.Nat using (mod-helper)

-- Because we know from the definition `mod-helper` that this equation holds:
-- mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j
-- we should be able to prove the slightly modified statement by transforming
-- all the `x + 1` into `suc x`. We can do so using `substₙ`.

_ : ∀ k m n j → mod-helper k m (n + 1) (j + 1) ≡ mod-helper (k + 1) m n j
_ = λ k m n j →
    let P sk sn sj = mod-helper k m sn sj ≡ mod-helper sk m n j
    in substₙ P (+-comm 1 k) (+-comm 1 n) (+-comm 1 j) refl

-----------------------------------------------------------------------
-- Generic programs working on n-ary products & functions
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- curryₙ   : ∀ n → (A₁ × ⋯ × Aₙ → B) → A₁ → ⋯ → Aₙ → B
-- uncurryₙ : ∀ n → (A₁ → ⋯ → Aₙ → B) → A₁ × ⋯ × Aₙ → B

-- The first thing we may want to do generically is convert between
-- curried function types and uncurried ones. We can do this by using:

-- They both work the same way so we will focus on curryₙ only here.
-- If we pass to `curryₙ` the arity of its argument then we obtain a
-- fully curried function.

curry₁ : (A × B × C × D → E) → A → B → C → D → E
curry₁ = curryₙ 4

-- Note that here we are not flattening arbitrary nestings: products have
-- to be right nested. Which means that if you have a deeply-nested product
-- then it won't be affected by the procedure.

curry₁′ : (A × (B × C) × D → E) → A → (B × C) → D → E
curry₁′ = curryₙ 3

-- When we are currying a function, we have no obligation to pass its exact
-- arity as the parameter: we can decide to only curry part of it like so:
-- Indeed (A₁ × ⋯ × Aₙ → B) can also be seen as (A₁ × ⋯ × (Aₖ × ⋯ × Aₙ) → B)

curry₂ : (A × B × C × D → E) → A → B → (C × D) → E
curry₂ = curryₙ 3

-----------------------------------------------------------------------
-- projₙ : ∀ n (k : Fin n) → (A₁ × ⋯ × Aₙ) → Aₖ₊₁

-- Another useful class of functions to manipulate n-ary product is a
-- generic projection function. Note the (k + 1) in the return index:
-- Fin counts from 0 up.

-- It behaves as one expects (Data.Fin's #_ comes in handy to write down
-- Fin literals):

proj₃ : (A × B × C × D × E) → C
proj₃ = projₙ 5 (# 2)

-- Of course we can once more project the "tail" of the n-ary product by
-- passing `projₙ` a natural number which is smaller than the size of the
-- n-ary product, seeing (A₁ × ⋯ × Aₙ) as (A₁ × ⋯ × (Aₖ × ⋯ × Aₙ)).

proj₃′ : (A × B × C × D × E) → C × D × E
proj₃′ = projₙ 3 (# 2)

-----------------------------------------------------------------------
-- insertₙ : ∀ n (k : Fin (suc n)) →
--           B → (A₁ × ⋯ Aₙ) → (A₁ × ⋯ × Aₖ × B × Aₖ₊₁ × ⋯ Aₙ)

insert₁ : C → (A × B × D × E) → (A × B × C × D × E)
insert₁ = insertₙ 4 (# 2)

insert₁′ : C → (A × B × D × E) → (A × B × C × D × E)
insert₁′ = insertₙ 3 (# 2)

-- Note that `insertₙ` takes a `Fin (suc n)`. Indeed in an n-ary product
-- there are (suc n) positions at which one may insert a value. We may
-- insert at the front or the back of the product:

insert-front : A → (B × C × D × E) → (A × B × C × D × E)
insert-front = insertₙ 4 (# 0)

insert-back : E → (A × B × C × D) → (A × B × C × D × E)
insert-back = insertₙ 4 (# 4)

-----------------------------------------------------------------------
-- removeₙ : ∀ n (k : Fin n) → (A₁ × ⋯ Aₙ) → (A₁ × ⋯ × Aₖ × Aₖ₊₂ × ⋯ Aₙ)

-- Dual to `insertₙ`, we may remove a value.

remove₁ : (A × B × C × D × E) → (A × B × D × E)
remove₁ = removeₙ 5 (# 2)

-- Inserting at `k` and then removing at `inject₁ k` should yield the identity

remove-insert : C → (A × B × D × E) → (A × B × D × E)
remove-insert c = removeₙ 5 (inject₁ k) ∘′ insertₙ 4 k c
    where k = # 2

-----------------------------------------------------------------------
-- updateₙ : ∀ n (k : Fin n) (f : (a : Aₖ₊₁) → B a) →
--           (p : A₁ × ⋯ Aₙ) → (A₁ × ⋯ × Aₖ × B (projₙ n k p) × Aₖ₊₂ × ⋯ Aₙ)

-- We can not only project out, insert or remove values: we can update them
-- in place. The type (and value) of the replacement at position k may depend
-- upon the current value at position k.

update₁ : (p : A × B × ℕ × C × D) → (A × B × Fin _ × C × D)
update₁ = updateₙ 5 (# 2) fromℕ

-- We can explicitly use the primed version of `updateₙ` to make it known to
-- Agda that the update function is non dependent. This type of information
-- is useful for inference: the tighter the constraints, the easier it is to
-- find a solution (if possible).

update₂ : (p : A × B × ℕ × C × D) → (A × B × List D × C × D)
update₂ = λ p → updateₙ′ 5 (# 2) (λ n → replicate n (projₙ 5 (# 4) p)) p

-----------------------------------------------------------------------
-- _%=_⊢_ : ∀ n → (C → D) → (A₁ → ⋯ Aₙ → D → B) → A₁ → ⋯ → Aₙ → C → B

-- Traditional composition (also known as the index update operator `_⊢_`
-- in `Relation.Unary`) focuses solely on the first argument of an n-ary
-- function. `_%=_⊢_` on the other hand allows us to touch any one of the
-- arguments.

-- In the following example we have a function `f : A → B` and `replicate`
-- of type `ℕ → B → List B`. We want ̀f` to act on the second argument of
-- replicate. Which we can do like so.

compose₁ : (A → B) → ℕ → A → List B
compose₁ f = 1 %= f ⊢ replicate

-- Here we spell out the equivalent explicit variable-manipulation and
-- prove the two functions equal.

compose₁′ : (A → B) → ℕ → A → List B
compose₁′ f n a = replicate n (f a)

compose₁-eq : compose₁ {a} {A} {b} {B} ≡ compose₁′
compose₁-eq = refl

-----------------------------------------------------------------------
-- _∷=_⊢_ : ∀ n → A → (A₁ → ⋯ Aₙ → A → B) → A₁ → ⋯ → Aₙ → B

-- Partial application usually focuses on the first argument of a function.
-- We can now partially apply a function in any of its arguments using
-- `_∷=_⊢_`. Reusing our example involving replicate: we can specialise it
-- to only output finite lists of `0`:

apply₁ : ℕ → List ℕ
apply₁ = 1 ∷= 0 ⊢ replicate

apply₁-eq : apply₁ 3 ≡ 0 ∷ 0 ∷ 0 ∷ []
apply₁-eq = refl

------------------------------------------------------------------------
-- holeₙ : ∀ n → (A → (A₁ → ⋯ Aₙ → B)) → A₁ → ⋯ → Aₙ → (A → B)

-- As we have seen earlier, `cong` acts on a function's first variable.
-- If we want to access the second one, we can use `flip`. But what about
-- the fourth one? We typically use an explicit λ-abstraction shuffling
-- variables. Not anymore.

-- Reusing mod-helper just because it takes a lot of arguments:

hole₁ : ∀ k m n j → mod-helper k (m + 1) n j ≡ mod-helper k (suc m) n j
hole₁ = λ k m n j → cong (holeₙ 2 (mod-helper k) n j) (+-comm m 1)

-----------------------------------------------------------------------
-- mapₙ : ∀ n → (B → C) → (A₁ → ⋯ Aₙ → B) → (A₁ → ⋯ → Aₙ → C)

-- (R →_) gives us the reader monad (and, a fortiori, functor). That is to
-- say that given a function (A → B) and an (R → A) we can get an (R → B)
-- This generalises to n-ary functions.

-- Reusing our `composeₙ` example: instead of applying `f` to the replicated
-- element, we can map it on the resulting list. Giving us:

map₁ : (A → B) → ℕ → A → List B
map₁ f = mapₙ 2 (map f) replicate

------------------------------------------------------------------------
-- constₙ : ∀ n → B → A₁ → ⋯ → Aₙ → B

-- `const` is basically `pure` for the reader monad discussed above. Just
-- like we can generalise the functorial action corresponding to the reader
-- functor to n-ary functions, we can do the same for `pure`.

const₁ : A → B → C → D → E → A
const₁ = constₙ 4

-- Together with `holeₙ`, this means we can make a constant function out
-- of any of the arguments. The fourth for instance:

const₂ : A → B → C → D → E → D
const₂ = holeₙ 3 (constₙ 4)

------------------------------------------------------------------------
-- Generalised quantifiers
------------------------------------------------------------------------

-- As we have seen multiple times already, one of the advantages of working
-- with non-dependent products is that they can be easily inferred. This is
-- a prime opportunity to define generic quantifiers.

-- And because n-ary relations are Set-terminated, there is no ambiguity
-- where to split between arguments & codomain. As a consequence Agda can
-- infer even `n`, the number of arguments. We can use notations which are
-- just like the ones defined in `Relation.Unary`.

------------------------------------------------------------------------
-- ∃⟨_⟩ : (A₁ → ⋯ → Aₙ → Set r) → Set _
-- ∃⟨ P ⟩ = ∃ λ a₁ → ⋯ → ∃ λ aₙ → P a₁ ⋯ aₙ

-- Returning to our favourite function taking a lot of arguments: we can
-- find a set of input for which it evaluates to 666

exist₁ : ∃⟨ (λ k m n j → mod-helper k m n j ≡ 666) ⟩
exist₁ = 19 , 793 , 3059 , 10 , refl

------------------------------------------------------------------------
-- ∀[_] : (A₁ → ⋯ → Aₙ → Set r) → Set _
-- ∀[_] P = ∀ {a₁} → ⋯ → ∀ {aₙ} → P a₁ ⋯ aₙ

all₁ : ∀[ (λ (a₁ a₂ : ℕ) → Dec (a₁ ≡ a₂)) ]
all₁ {a₁} {a₂} = a₁ ≡? a₂

------------------------------------------------------------------------
-- Π : (A₁ → ⋯ → Aₙ → Set r) → Set _
-- Π P = ∀ a₁ → ⋯ → ∀ aₙ → P a₁ ⋯ aₙ

all₂ : Π[ (λ (a₁ a₂ : ℕ) → Dec (a₁ ≡ a₂)) ]
all₂ = _≡?_

------------------------------------------------------------------------
-- _⇒_ : (A₁ → ⋯ → Aₙ → Set r) → (A₁ → ⋯ → Aₙ → Set s) → (A₁ → ⋯ → Aₙ → Set _)
-- P ⇒ Q = λ a₁ → ⋯ → λ aₙ → P a₁ ⋯ aₙ → Q a₁ ⋯ aₙ

antisym : ∀[ _≤_ ⇒ _≥_ ⇒ _≡_ ]
antisym = ≤-antisym

------------------------------------------------------------------------
-- _∪_ : (A₁ → ⋯ → Aₙ → Set r) → (A₁ → ⋯ → Aₙ → Set s) → (A₁ → ⋯ → Aₙ → Set _)
-- P ∪ Q = λ a₁ → ⋯ → λ aₙ → P a₁ ⋯ aₙ ⊎ Q a₁ ⋯ aₙ

≤->-connex : Π[ _≤_ ∪ _>_ ]
≤->-connex m n with <-cmp m n
... | tri< a ¬b ¬c = inj₁ (<⇒≤ a)
... | tri≈ ¬a b ¬c = inj₁ (≤-reflexive b)
... | tri> ¬a ¬b c = inj₂ c

------------------------------------------------------------------------
-- _∩_ : (A₁ → ⋯ → Aₙ → Set r) → (A₁ → ⋯ → Aₙ → Set s) → (A₁ → ⋯ → Aₙ → Set _)
-- P ∩ Q = λ a₁ → ⋯ → λ aₙ → P a₁ ⋯ aₙ × Q a₁ ⋯ aₙ

<-inversion : ∀[ _<_ ⇒ _≤_ ∩ _≢_ ]
<-inversion m<n = <⇒≤ m<n , <⇒≢ m<n

------------------------------------------------------------------------
-- ∁ : (A₁ → ⋯ → Aₙ → Set r) → (A₁ → ⋯ → Aₙ → Set _)
-- ∁ P = λ a₁ → ⋯ → λ aₙ → ¬ (P a₁ ⋯ aₙ)

m<n⇒m≱n : ∀[ _>_ ⇒ ∁ _≤_ ]
m<n⇒m≱n m>n m≤n = <⇒≱ m>n m≤n
