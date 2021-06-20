------------------------------------------------------------------------
-- The Agda standard library
--
-- Matrices
------------------------------------------------------------------------

open import Algebra.Core using (Op₂)
open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin; _≡ᵇ_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Functional as Vector using (Vector)
open import Function.Base using (_$_)
open import Level using (Level)

module Data.Matrix where

private
  variable
    a : Level
    A B C : Set a
    m n o : ℕ

------------------------------------------------------------------------
-- Definition

-- Matrices are defined as maps from finite indices to values. This
-- definition is equivalent to `Vector (Vector A m) n`, and consequently
-- many of the operations, relations and proofs about `Vector`s can be
-- lifted to matrices.

Matrix : Set a → ℕ → ℕ → Set a
Matrix A m n = Fin m → Fin n → A

SquareMatrix : Set a → ℕ → Set a
SquareMatrix A n = Matrix A n n

------------------------------------------------------------------------
-- Operations for deconstructing matrices

row : Matrix A m n → Fin m → Vector A n
row M i = M i

col : Matrix A m n → Fin n → Vector A m
col M j = λ i → M i j

------------------------------------------------------------------------
-- Operations for constructing matrices

[] : SquareMatrix A 0
[] ()

[_] : A → SquareMatrix A 1
[ x ] i j = x

constant : A → Matrix A m n
constant x i j = x

diagonal : A → A → SquareMatrix A n
diagonal 1# 0# i j = if i ≡ᵇ j then 1# else 0#

------------------------------------------------------------------------
-- Operations for transforming matrices

map : (A → B) → Matrix A m n → Matrix B m n
map f M i j = f (M i j)

zipWith : (A → B → C) → Matrix A m n → Matrix B m n → Matrix C m n
zipWith f M N i j = f (M i j) (N i j)

zip : Matrix A m n → Matrix B m n → Matrix (A × B) m n
zip = zipWith _,_

_⊛_ : Matrix (A → B) m n → Matrix A m n → Matrix B m n
_⊛_ = zipWith _$_

_ᵀ : Matrix A m n → Matrix A n m
(M ᵀ) i j = M j i

add : Op₂ A → Op₂ (Matrix A m n)
add _+_ = zipWith _+_

multiply : Op₂ C → (A → B → C) → C → Matrix A m n → Matrix B n o → Matrix C m o
multiply _+_ _×_ 1# M N i j = Vector.foldr _+_ 1# (λ k → M i k × N k j)

multiply+ : Op₂ C → (A → B → C) → Matrix A m (suc n) → Matrix B (suc n) o → Matrix C m o
multiply+ _+_ _×_ M N i j = Vector.foldr+ _+_ (λ k → M i k × N k j)
