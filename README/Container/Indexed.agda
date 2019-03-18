------------------------------------------------------------------------
-- The Agda standard library
--
-- Example showing how to define an indexed container
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module README.Container.Indexed where

open import Data.Unit
open import Data.Empty
open import Data.Nat.Base
open import Data.Product
open import Function
open import Data.W.Indexed
open import Data.Container.Indexed
open import Data.Container.Indexed.WithK

module _ {a} (A : Set a) where

------------------------------------------------------------------------
-- Vector as an indexed container

-- An indexed container is defined by three things:
-- 1. Commands the user can emit
-- 2. Responses the indexed container returns to these commands
-- 3. Update of the index based on the command and the response issued.

-- For a vector, commands are constructors, responses are the number of subvectors
-- (0 if the vector is empty, 1 otherwise) and the update corresponds to setting the
-- size of the tail (if it exists). We can formalize these ideas like so:

-- Depending on the size of the vector, we may have reached the end already (nil)
-- or we may specify what the head should be (cons). This is the type of commands.

  data VecC : ℕ → Set a where
    nil  :           VecC zero
    cons : ∀ n → A → VecC (suc n)

  Vec : Container ℕ ℕ a _
  Command Vec = VecC

-- We then treat each command independently, specifying both the response and the
-- next index based on that response.

-- In the nil case, the response is the empty type: there won't be any tail. As
-- a consequence, the next index won't be needed (and we can rely on the fact the
-- user will never be able to call it).

  Response Vec nil = ⊥
  next     Vec nil = λ ()

-- In the cons case, the response is the unit type: there is exactly one tail. The
-- next index is the predecessor of the current one. It is handily handed over to
-- use by `cons`.

  -- cons
  Response Vec (cons n a) = ⊤
  next     Vec (cons n a) = λ _ → n

-- Finally we can define the type of Vector as the least fixed point of Vec.

  Vector : ℕ → Set a
  Vector = μ Vec

module _ {a} {A : Set a} where

-- We can recover the usual constructors by using `sup` to enter the fixpoint
-- and then using the appropriate pairing of a command & a handler for the
-- response.

-- For [], the response is ⊥ which makes it easy to conclude.

  [] : Vector A 0
  [] = sup (nil , λ ())

-- For _∷_, the response is ⊤ so we need to pass a tail. We give the one we took
-- as an argument.

  infixr 3 _∷_
  _∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)
  x ∷ xs = sup (cons _ x , λ _ → xs)

-- We can now use these constructors to build up vectors:

1⋯3 : Vector ℕ 3
1⋯3 = 1 ∷ 2 ∷ 3 ∷ []





-- Horrible thing to check the definition of _∈_ is not buggy.
-- Not sure whether we can say anything interesting about it in the case of Vector...

open import Relation.Binary.HeterogeneousEquality

_ : _∈_ {C = Vec ℕ} {X = Vector ℕ} 1⋯3 (⟦ Vec ℕ ⟧ (Vector ℕ) 4 ∋ cons _ 0 , λ _ → 1⋯3)
_ = _ , refl
