------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of membership of vectors based on propositional equality.
------------------------------------------------------------------------

module Data.Vec.Membership.Propositional.Properties where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import Data.Vec hiding (here; there)
open import Data.Vec.Any using (here; there)
open import Data.List using ([]; _∷_)
open import Data.List.Any using (here; there)
open import Data.Vec.Membership.Propositional
import Data.List.Membership.Propositional as List
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------
-- lookup

module _ {a} {A : Set a} where

  ∈-lookup : ∀ {n} i (xs : Vec A n) → lookup i xs ∈ xs
  ∈-lookup zero    (x ∷ xs) = here refl
  ∈-lookup (suc i) (x ∷ xs) = there (∈-lookup i xs)

------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} (f : A → B) where

  ∈-map⁺ : ∀ {m v} {xs : Vec A m} → v ∈ xs → f v ∈ map f xs
  ∈-map⁺ (here refl)  = here refl
  ∈-map⁺ (there x∈xs) = there (∈-map⁺ x∈xs)

------------------------------------------------------------------------
-- _++_

module _ {a} {A : Set a} {v : A} where

  ∈-++⁺ˡ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → v ∈ xs → v ∈ xs ++ ys
  ∈-++⁺ˡ (here refl)  = here refl
  ∈-++⁺ˡ (there x∈xs) = there (∈-++⁺ˡ x∈xs)

  ∈-++⁺ʳ : ∀ {m n} (xs : Vec A m) {ys : Vec A n} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ []       x∈ys = x∈ys
  ∈-++⁺ʳ (x ∷ xs) x∈ys = there (∈-++⁺ʳ xs x∈ys)

------------------------------------------------------------------------
-- tabulate

module _ {a} {A : Set a} where

  ∈-tabulate⁺ : ∀ {n} (f : Fin n → A) i → f i ∈ tabulate f
  ∈-tabulate⁺ f zero    = here refl
  ∈-tabulate⁺ f (suc i) = there (∈-tabulate⁺ (f ∘ suc) i)

------------------------------------------------------------------------
-- allFin

∈-allFin⁺ : ∀ {n} (i : Fin n) → i ∈ allFin n
∈-allFin⁺ = ∈-tabulate⁺ id

------------------------------------------------------------------------
-- allPairs

module _ {a b} {A : Set a} {B : Set b} where

  ∈-allPairs⁺ : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
               x ∈ xs → y ∈ ys → (x , y) ∈ allPairs xs ys
  ∈-allPairs⁺ {xs = x ∷ xs} (here refl) = ∈-++⁺ˡ ∘ ∈-map⁺ (x ,_)
  ∈-allPairs⁺ {xs = x ∷ _} (there x∈xs) =
    ∈-++⁺ʳ (map (x ,_) _) ∘ ∈-allPairs⁺ x∈xs

------------------------------------------------------------------------
-- toList

module _ {a} {A : Set a} {v : A} where

  ∈-toList⁺ : ∀ {n} {xs : Vec A n} → v ∈ xs → v List.∈ toList xs
  ∈-toList⁺ (here refl) = here refl
  ∈-toList⁺ (there x∈)  = there (∈-toList⁺ x∈)

  ∈-toList⁻ : ∀ {n} {xs : Vec A n} → v List.∈ toList xs → v ∈ xs
  ∈-toList⁻ {xs = []}     ()
  ∈-toList⁻ {xs = x ∷ xs} (here refl)  = here refl
  ∈-toList⁻ {xs = x ∷ xs} (there v∈xs) = there (∈-toList⁻ v∈xs)

------------------------------------------------------------------------
-- fromList

module _ {a} {A : Set a} {v : A} where

  ∈-fromList⁺ : ∀ {xs} → v List.∈ xs → v ∈ fromList xs
  ∈-fromList⁺ (here refl) = here refl
  ∈-fromList⁺ (there x∈)  = there (∈-fromList⁺ x∈)

  ∈-fromList⁻ : ∀ {xs} → v ∈ fromList xs → v List.∈ xs
  ∈-fromList⁻ {[]}    ()
  ∈-fromList⁻ {_ ∷ _} (here refl)  = here refl
  ∈-fromList⁻ {_ ∷ _} (there v∈xs) = there (∈-fromList⁻ v∈xs)
