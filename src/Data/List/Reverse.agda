------------------------------------------------------------------------
-- The Agda standard library
--
-- Reverse view
------------------------------------------------------------------------

module Data.List.Reverse where

open import Data.List.Base
open import Data.Nat
import Data.Nat.Properties as Nat
open import Induction.Nat using (<′-Rec; <′-rec)
open import Relation.Binary.PropositionalEquality

-- If you want to traverse a list from the end, then you can use the
-- reverse view of it.

infixl 5 _∶_∶ʳ_

data Reverse {a} {A : Set a} : List A → Set a where
  []     : Reverse []
  _∶_∶ʳ_ : ∀ xs (rs : Reverse xs) (x : A) → Reverse (xs ∷ʳ x)

module _ {a} {A : Set a} where

  reverseView : (xs : List A) → Reverse xs
  reverseView xs = <′-rec Pred rev (length xs) xs refl where

    Pred : ℕ → Set a
    Pred n = (xs : List A) → length xs ≡ n → Reverse xs

    lem : ∀ xs {x : A} → length xs <′ length (xs ∷ʳ x)
    lem []       = ≤′-refl
    lem (x ∷ xs) = Nat.s≤′s (lem xs)

    rev : (n : ℕ) → <′-Rec Pred n → Pred n
    rev n                   rec xs         eq   with initLast xs
    rev n                   rec .[]        eq   | []       = []
    rev .(length (xs ∷ʳ x)) rec .(xs ∷ʳ x) refl | xs ∷ʳ' x
      with rec (length xs) (lem xs) xs refl
    rev ._ rec .([]      ∷ʳ x) refl | ._ ∷ʳ' x | [] = _ ∶ [] ∶ʳ x
    rev ._ rec .(ys ∷ʳ y ∷ʳ x) refl | ._ ∷ʳ' x | ys ∶ rs ∶ʳ y =
      _ ∶ (_ ∶ rs ∶ʳ y) ∶ʳ x
