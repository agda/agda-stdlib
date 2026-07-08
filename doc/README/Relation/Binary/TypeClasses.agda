------------------------------------------------------------------------
-- The Agda standard library
--
-- Usage examples of typeclasses for binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Relation.Binary.TypeClasses where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.TypeClasses

open import Data.Bool.Base renaming (_≤_ to _≤Bool)
open import Data.Bool.Instances
open import Data.List.Base
open import Data.List.Instances
open import Data.List.Relation.Binary.Lex.NonStrict using (Lex-≤)
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Instances
open import Data.Product.Base using (_×_; _,_; Σ)
open import Data.Product.Instances
open import Data.Unit.Base renaming (_≤_ to _≤⊤_)
open import Data.Unit.Instances
open import Data.Vec.Base
open import Data.Vec.Instances

test-Dec≡-Bool : Dec (true ≡ true)
test-Dec≡-Bool = true ≟ true

test-Dec≡-Nat : Dec (0 ≡ 1)
test-Dec≡-Nat = 0 ≟ 1

test-Dec≡-List : Dec (_≡_ {A = List ℕ} (1 ∷ 2 ∷ []) (1 ∷ 2 ∷ []))
test-Dec≡-List = (1 ∷ 2 ∷ []) ≟ (1 ∷ 2 ∷ [])

test-Dec≡-⊤ : Dec (tt ≡ tt)
test-Dec≡-⊤ = _ ≟ _

test-Dec≡-Pair : Dec (_≡_ {A = Bool × Bool} (true , false) (false , true))
test-Dec≡-Pair = _ ≟ _

test-Dec≡-Vec : Dec (_≡_ {A = Vec Bool 2} (true ∷ false ∷ []) (true ∷ false ∷ []))
test-Dec≡-Vec = _ ≟ _

test-Dec≡-Σ : Dec (_≡_ {A = Σ ℕ (Vec Bool)} (0 , []) (1 , true ∷ []))
test-Dec≡-Σ = _ ≟ _

test-Dec≤-Nat : Dec (0 ≤ℕ 1)
test-Dec≤-Nat = 0 ≤? 1

test-Dec≤-List : Dec (Lex-≤ _≡_ _≤ℕ_ (0 ∷ 1 ∷ []) (1 ∷ []))
test-Dec≤-List = _ ≤? _
