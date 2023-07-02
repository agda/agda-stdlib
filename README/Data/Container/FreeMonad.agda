------------------------------------------------------------------------
-- The Agda standard library
--
-- Example showing how the free monad construction on containers can be
-- used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module README.Data.Container.FreeMonad where

open import Level using (0ℓ)
open import Effect.Monad
open import Data.Empty
open import Data.Unit
open import Data.Bool.Base using (Bool; true)
open import Data.Nat
open import Data.Sum using (inj₁; inj₂)
open import Data.Product.Base renaming (_×_ to _⟨×⟩_)
open import Data.Container using (Container; _▷_)
open import Data.Container.Combinator
open import Data.Container.FreeMonad as FreeMonad
open import Data.W
open import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------
-- Defining the signature of an effect and building trees describing
-- computations leveraging that effect.

-- The signature of state and its (generic) operations.

State : Set → Container _ _
State S = ⊤ ⟶ S ⊎ S ⟶ ⊤
  where
  _⟶_ : Set → Set → Container _ _
  I ⟶ O = I ▷ λ _ → O

get : ∀ {S} → State S ⋆ S
get = impure (inj₁ _ , pure)

put : ∀ {S} → S → State S ⋆ ⊤
put s = impure (inj₂ s , pure)

-- Using the above we can, for example, write a stateful program that
-- delivers a boolean.
prog : State ℕ ⋆ Bool
prog =
  get         >>= λ n →
  put (suc n) >>
  pure true
  where
  open RawMonad monad using (_>>_)

runState : {S X : Set} → State S ⋆ X → (S → X ⟨×⟩ S)
runState (pure x)                = λ s → x , s
runState (impure ((inj₁ _) , k)) = λ s → runState (k s) s
runState (impure ((inj₂ s) , k)) = λ _ → runState (k _) s

test : runState prog 0 ≡ (true , 1)
test = P.refl

-- It should be noted that @State S ⋆ X@ is not the state monad. If we
-- could quotient @State S ⋆ X@ by the seven axioms of state (see
-- Plotkin and Power's "Notions of Computation Determine Monads", 2002)
-- then we would get the state monad.

------------------------------------------------------------------------
-- Defining effectful inductive data structures

-- The definition of `C ⋆ A` is strictly positive in `A`, meaning that we
-- can use `C ⋆_` when defining (co)inductive datatypes.


open import Size
open import Codata.Sized.Thunk
open import Data.Vec.Base using (Vec; []; _∷_)


-- A `Tap C A` is a infinite source of `A`s provided that we can perform
-- the effectful computations described by `C`.
-- The first one can be accessed readily but the rest of them is hidden
-- under layers of `C` computations.

module _ (C : Container 0ℓ 0ℓ) (A : Set 0ℓ) where

  data Tap (i : Size) : Set 0ℓ where
    _∷_ : A → Thunk (λ i → C ⋆ Tap i) i → Tap i

-- We can run a given tap for a set number of steps and collect the elements
-- thus generated along the way. This gives us a `C ⋆_` computation of a vector.

module _ {C : Container 0ℓ 0ℓ} {A : Set 0ℓ} where

  take : Tap C A _ → (n : ℕ) → C ⋆ Vec A n
  take _ 0 = pure []
  take (x ∷ _) 1 = pure (x ∷ [])
  take (x ∷ mxs) (suc n) = do
    xs ← mxs .force
    rest ← take xs n
    pure (x ∷ rest)

-- A stream of all the natural numbers starting from a given value is an
-- example of a tap.

natsFrom : ∀ {i} → State ℕ ⋆ Tap (State ℕ) ℕ i
natsFrom = let open RawMonad monad using (_>>_) in do
  n ← get
  put (suc n)
  pure (n ∷ λ where .force → natsFrom)

-- We can use `take` to capture an initial segment of the `natsFrom` tap
-- and, after running the state operations, observe that it does generate
-- successive numbers.

_ : ∀ k →
    runState (natsFrom >>= λ ns → take ns 5) k
  ≡ (k ∷ 1 + k ∷ 2 + k ∷ 3 + k ∷ 4 + k ∷ [] , 5 + k)
_ = λ k → refl
