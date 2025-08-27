------------------------------------------------------------------------
-- The Agda standard library
--
-- *Pseudo-random* number generation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module System.Random where

import System.Random.Primitive as Prim

open import Data.Bool.Base using (T)
open import Data.Nat.Base using (ℕ; z≤n) hiding (module ℕ)
open import Foreign.Haskell.Pair using (_,_)
open import Function.Base using (_$_; _∘_)
open import IO.Base using (IO; lift; lift!; _<$>_; _>>=_; pure)
import IO.Effectful as IO
open import Level using (0ℓ; suc; _⊔_; lift)
open import Relation.Binary.Core using (Rel)

------------------------------------------------------------------------
-- Ranged generation shall return proofs

record InBounds {a r} {A : Set a} (_≤_ : Rel A r) (lo hi : A) : Set (a ⊔ r) where
  constructor _∈[_,_]
  field
    value : A
    .isLowerBound : lo ≤ value
    .isUpperBound : value ≤ hi

RandomRIO : ∀ {a r} {A : Set a} (_≤_ : Rel A r) → Set (suc (a ⊔ r))
RandomRIO {A = A} _≤_ = (lo hi : A) → .(lo ≤ hi) → IO (InBounds _≤_ lo hi)

------------------------------------------------------------------------
-- Instances

module Char where

  open import Data.Char.Base using (Char; _≤_)

  randomIO : IO Char
  randomIO = lift Prim.randomIO-Char

  randomRIO : RandomRIO _≤_
  randomRIO lo hi _ = do
    value ← lift (Prim.randomRIO-Char (lo , hi))
    pure (value ∈[ trustMe , trustMe ])
    where postulate trustMe : ∀ {A} → A

module Float where

  open import Data.Float.Base using (Float; _≤_)

  randomIO : IO Float
  randomIO = lift Prim.randomIO-Float

  randomRIO : RandomRIO _≤_
  randomRIO lo hi _ = do
    value ← lift (Prim.randomRIO-Float (lo , hi))
    pure (value ∈[ trustMe , trustMe ])
    where postulate trustMe : ∀ {A} → A

module ℤ where

  open import Data.Integer.Base using (ℤ; _≤_)

  randomIO : IO ℤ
  randomIO = lift Prim.randomIO-Int

  randomRIO : RandomRIO _≤_
  randomRIO lo hi _ = do
    value ← lift (Prim.randomRIO-Int (lo , hi))
    pure (value ∈[ trustMe , trustMe ])
    where postulate trustMe : ∀ {A} → A

module ℕ where

  open import Data.Nat.Base using (ℕ; _≤_)

  randomIO : IO ℕ
  randomIO = lift Prim.randomIO-Nat

  randomRIO : RandomRIO _≤_
  randomRIO lo hi _ = do
    value ← lift (Prim.randomRIO-Nat (lo , hi))
    pure (value ∈[ trustMe , trustMe ])
    where postulate trustMe : ∀ {A} → A

module Word64 where

  open import Data.Word64.Base using (Word64; _≤_)

  randomIO : IO Word64
  randomIO = lift Prim.randomIO-Word64

  randomRIO : RandomRIO _≤_
  randomRIO lo hi _ = do
    value ← lift (Prim.randomRIO-Word64 (lo , hi))
    pure (value ∈[ trustMe , trustMe ])
    where postulate trustMe : ∀ {A} → A

module Fin where

  open import Data.Nat.Base as ℕ using (suc; NonZero; z≤n; s≤s)
  import Data.Nat.Properties as ℕ
  open import Data.Fin.Base using (Fin; _≤_; fromℕ<; toℕ)
  import Data.Fin.Properties as Fin

  randomIO : ∀ {n} → .{{NonZero n}} → IO (Fin n)
  randomIO {n = n@(suc _)} = do
    suc k ∈[ lo≤k , k≤hi ] ← ℕ.randomRIO 1 n (s≤s z≤n)
    pure (fromℕ< k≤hi)

  toℕ-cancel-InBounds : ∀ {n} {lo hi : Fin n} →
                        InBounds ℕ._≤_ (toℕ lo) (toℕ hi) →
                        InBounds _≤_ lo hi
  toℕ-cancel-InBounds {n} {lo} {hi} (k ∈[ toℕlo≤k , k≤toℕhi ]) =
    let
      .k<n  : k ℕ.< n
      k<n = ℕ.≤-<-trans k≤toℕhi (Fin.toℕ<n hi)

      .lo≤k : lo ≤ fromℕ< k<n
      lo≤k = Fin.toℕ-cancel-≤ $ let open ℕ.≤-Reasoning in begin
        toℕ lo           ≤⟨ toℕlo≤k ⟩
        k                ≡⟨ Fin.toℕ-fromℕ< k<n ⟨
        toℕ (fromℕ< k<n) ∎

      .k≤hi : fromℕ< k<n ≤ hi
      k≤hi = Fin.toℕ-cancel-≤ $ let open ℕ.≤-Reasoning in begin
        toℕ (fromℕ< k<n) ≡⟨ Fin.toℕ-fromℕ< k<n ⟩
        k                ≤⟨ k≤toℕhi ⟩
        toℕ hi           ∎

    in fromℕ< k<n ∈[ lo≤k , k≤hi ]

  randomRIO : ∀ {n} → RandomRIO {A = Fin n} _≤_
  randomRIO {n} lo hi p = do
    k ← ℕ.randomRIO (toℕ lo) (toℕ hi) (Fin.toℕ-mono-≤ p)
    pure (toℕ-cancel-InBounds k)

module List {a} {A : Set a} (rIO : IO A)  where

  open import Data.List.Base using (List; replicate)
  open import Data.List.Effectful using (module TraversableA)

  -- Careful: this can generate very long lists!
  -- You may want to use Vec≤ instead.
  randomIO : IO (List A)
  randomIO = do
    lift n ← lift! ℕ.randomIO
    TraversableA.sequenceA IO.applicative $ replicate n rIO

module Vec {a} {A : Set a} (rIO : IO A) (n : ℕ) where

  open import Data.Vec.Base using (Vec; replicate)
  open import Data.Vec.Effectful using (module TraversableA)

  randomIO : IO (Vec A n)
  randomIO = TraversableA.sequenceA IO.applicative $ replicate n rIO

module Vec≤ {a} {A : Set a} (rIO : IO A) (n : ℕ) where

  open import Data.Vec.Bounded.Base using (Vec≤; _,_)

  randomIO : IO (Vec≤ A n)
  randomIO = do
    lift (len ∈[ _ , len≤n ]) ← lift! (ℕ.randomRIO 0 n z≤n)
    vec ← Vec.randomIO rIO len
    pure (vec , len≤n)

module String where

  open import Data.String.Base using (String; fromList)

  -- Careful: this can generate very long lists!
  -- You may want to use String≤ instead.
  randomIO : IO String
  randomIO = fromList <$> List.randomIO Char.randomIO

module String≤ (n : ℕ) where

  import Data.Vec.Bounded.Base as Vec≤
  open import Data.String.Base using (String; fromList)

  randomIO : IO String
  randomIO = fromList ∘ Vec≤.toList <$> Vec≤.randomIO Char.randomIO n

open import Data.Char.Base using (Char; _≤_)

module RangedString≤ (a b : Char)  .(a≤b : a ≤ b) (n : ℕ) where

  import Data.Vec.Bounded.Base as Vec≤
  open import Data.String.Base using (String; fromList)

  randomIO : IO String
  randomIO =
    fromList ∘ Vec≤.toList ∘ Vec≤.map InBounds.value
    <$> Vec≤.randomIO (Char.randomRIO a b a≤b) n
