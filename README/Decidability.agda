------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of decision procedures and how to use them
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Decidability where

-- Reflects and Dec are defined in Relation.Nullary, and operations on them can
-- be found in Relation.Nullary.Reflects and Relation.Nullary.Decidable.

open import Relation.Nullary as Nullary
open import Relation.Nullary.Reflects
open import Relation.Nullary.Decidable

open import Data.Bool
open import Data.List
open import Data.List.Properties using (∷-injective)
open import Data.Nat
open import Data.Nat.Properties using (suc-injective)
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nary
open import Relation.Nullary.Product

infix 4 _≟₀_ _≟₁_ _≟₂_

-- A proof of `Reflects P b` shows that a proposition `P` has the truth value of
-- the boolean `b`. A proof of `Reflects P true` amounts to a proof of `P`, and
-- a proof of `Reflects P false` amounts to a refutation of `P`.

ex₀ : (n : ℕ) → Reflects (n ≡ n) true
ex₀ n = ofʸ refl

ex₁ : (n : ℕ) → Reflects (zero ≡ suc n) false
ex₁ n = ofⁿ λ ()

ex₂ : (b : Bool) → Reflects (T b) b
ex₂ false = ofⁿ id
ex₂ true  = ofʸ tt

-- A proof of `Dec P` is a proof of `Reflects P b` for some `b`.
-- `Dec P` is declared as a record, with fields:
--   does : Bool
--   proof : Reflects P does

ex₃ : (b : Bool) → Dec (T b)
does  (ex₃ b) = b
proof (ex₃ b) = ex₂ b

-- We also have pattern synonyms `yes` and `no`, allowing both fields to be
-- given at once.

ex₄ : (n : ℕ) → Dec (zero ≡ suc n)
ex₄ n = no λ ()

-- It is possible, but not ideal, to define recursive decision procedures using
-- only the `yes` and `no` patterns. The following procedure decides whether two
-- given natural numbers are equal.

_≟₀_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟₀ zero  = yes refl
zero  ≟₀ suc n = no λ ()
suc m ≟₀ zero  = no λ ()
suc m ≟₀ suc n with m ≟₀ n
... | yes p = yes (cong suc p)
... | no ¬p = no (¬p ∘ suc-injective)

-- In this case, we can see that `does (suc m ≟ suc n)` should be equal to
-- `does (m ≟ n)`, because a `yes` from `m ≟ n` gives rise to a `yes` from the
-- result, and similarly for `no`. However, in the above definition, this
-- equality does not hold definitionally, because we always do a case split
-- before returning a result. To avoid this, we can return the `does` part
-- separately, before any pattern matching.

_≟₁_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟₁ zero  = yes refl
zero  ≟₁ suc n = no λ ()
suc m ≟₁ zero  = no λ ()
does  (suc m ≟₁ suc n) = does (m ≟₁ n)
proof (suc m ≟₁ suc n) with m ≟₁ n
... | yes p = ofʸ (cong suc p)
... | no ¬p = ofⁿ (¬p ∘ suc-injective)

-- We now get definitional equalities such as the following.

_ : (m n : ℕ) → does (5 + m ≟₁ 3 + n) ≡ does (2 + m ≟₁ n)
_ = λ m n → refl

-- Even better, from a maintainability point of view, is to use `map` or `map′`,
-- both of which capture the pattern of the `does` field remaining the same, but
-- the `proof` field being updated.

_≟₂_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟₂ zero  = yes refl
zero  ≟₂ suc n = no λ ()
suc m ≟₂ zero  = no λ ()
suc m ≟₂ suc n = map′ (cong suc) suc-injective (m ≟₂ n)

_ : (m n : ℕ) → does (5 + m ≟₂ 3 + n) ≡ does (2 + m ≟₂ n)
_ = λ m n → refl

-- `map′` can be used in conjunction with combinators such as `_⊎-dec_` and
-- `_×-dec_` to build complex (simply typed) decision procedures.

module ListDecEq₀ {a} {A : Set a} (_≟ᴬ_ : (x y : A) → Dec (x ≡ y)) where

  _≟ᴸᴬ_ : (xs ys : List A) → Dec (xs ≡ ys)
  []       ≟ᴸᴬ []       = yes refl
  []       ≟ᴸᴬ (y ∷ ys) = no λ ()
  (x ∷ xs) ≟ᴸᴬ []       = no λ ()
  (x ∷ xs) ≟ᴸᴬ (y ∷ ys) =
    map′ (uncurry (cong₂ _∷_)) ∷-injective (x ≟ᴬ y ×-dec xs ≟ᴸᴬ ys)

-- The final case says that `x ∷ xs ≡ y ∷ ys` exactly when `x ≡ y` *and*
-- `xs ≡ ys`. The proofs are updated by the first two arguments to `map′`.

-- In the case of ≡-equality tests, the pattern
-- `map′ (congₙ c) c-injective (x₀ ≟ y₀ ×-dec ... ×-dec xₙ₋₁ ≟ yₙ₋₁)`
-- is captured by `≟-mapₙ n c c-injective (x₀ ≟ y₀) ... (xₙ₋₁ ≟ yₙ₋₁)`.

module ListDecEq₁ {a} {A : Set a} (_≟ᴬ_ : (x y : A) → Dec (x ≡ y)) where

  _≟ᴸᴬ_ : (xs ys : List A) → Dec (xs ≡ ys)
  []       ≟ᴸᴬ []       = yes refl
  []       ≟ᴸᴬ (y ∷ ys) = no λ ()
  (x ∷ xs) ≟ᴸᴬ []       = no λ ()
  (x ∷ xs) ≟ᴸᴬ (y ∷ ys) = ≟-mapₙ 2 _∷_ ∷-injective (x ≟ᴬ y) (xs ≟ᴸᴬ ys)
