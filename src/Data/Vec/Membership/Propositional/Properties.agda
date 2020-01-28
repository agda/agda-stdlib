------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of membership of vectors based on propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Membership.Propositional.Properties where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product as Prod using (_,_; ∃; _×_; -,_)
open import Data.Vec hiding (here; there)
open import Data.Vec.Relation.Unary.Any using (here; there)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Data.Vec.Membership.Propositional
open import Data.List.Membership.Propositional
  using () renaming (_∈_ to _∈ₗ_)
open import Level using (Level)
open import Function using (_∘_; id)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (refl)

private
  variable
    a b p : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- lookup

∈-lookup : ∀ {n} i (xs : Vec A n) → lookup xs i ∈ xs
∈-lookup zero    (x ∷ xs) = here refl
∈-lookup (suc i) (x ∷ xs) = there (∈-lookup i xs)

------------------------------------------------------------------------
-- map

∈-map⁺ : (f : A → B) → ∀ {m v} {xs : Vec A m} → v ∈ xs → f v ∈ map f xs
∈-map⁺ f (here refl)  = here refl
∈-map⁺ f (there x∈xs) = there (∈-map⁺ f x∈xs)

------------------------------------------------------------------------
-- _++_

∈-++⁺ˡ : ∀ {m n v} {xs : Vec A m} {ys : Vec A n} → v ∈ xs → v ∈ xs ++ ys
∈-++⁺ˡ (here refl)  = here refl
∈-++⁺ˡ (there x∈xs) = there (∈-++⁺ˡ x∈xs)

∈-++⁺ʳ : ∀ {m n v} (xs : Vec A m) {ys : Vec A n} → v ∈ ys → v ∈ xs ++ ys
∈-++⁺ʳ []       x∈ys = x∈ys
∈-++⁺ʳ (x ∷ xs) x∈ys = there (∈-++⁺ʳ xs x∈ys)

------------------------------------------------------------------------
-- tabulate

∈-tabulate⁺ : ∀ {n} (f : Fin n → A) i → f i ∈ tabulate f
∈-tabulate⁺ f zero    = here refl
∈-tabulate⁺ f (suc i) = there (∈-tabulate⁺ (f ∘ suc) i)

------------------------------------------------------------------------
-- allFin

∈-allFin⁺ : ∀ {n} (i : Fin n) → i ∈ allFin n
∈-allFin⁺ = ∈-tabulate⁺ id

------------------------------------------------------------------------
-- allPairs

∈-allPairs⁺ : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
             x ∈ xs → y ∈ ys → (x , y) ∈ allPairs xs ys
∈-allPairs⁺ {xs = x ∷ xs} (here refl)  = ∈-++⁺ˡ ∘ ∈-map⁺ (x ,_)
∈-allPairs⁺ {xs = x ∷ _}  (there x∈xs) =
  ∈-++⁺ʳ (map (x ,_) _) ∘ ∈-allPairs⁺ x∈xs

------------------------------------------------------------------------
-- toList

∈-toList⁺ : ∀ {n} {v : A} {xs : Vec A n} → v ∈ xs → v ∈ₗ toList xs
∈-toList⁺ (here refl) = here refl
∈-toList⁺ (there x∈)  = there (∈-toList⁺ x∈)

∈-toList⁻ : ∀ {n} {v : A} {xs : Vec A n} → v ∈ₗ toList xs → v ∈ xs
∈-toList⁻ {xs = x ∷ xs} (here refl)  = here refl
∈-toList⁻ {xs = x ∷ xs} (there v∈xs) = there (∈-toList⁻ v∈xs)

------------------------------------------------------------------------
-- fromList

∈-fromList⁺ : ∀ {v : A} {xs} → v ∈ₗ xs → v ∈ fromList xs
∈-fromList⁺ (here refl) = here refl
∈-fromList⁺ (there x∈)  = there (∈-fromList⁺ x∈)

∈-fromList⁻ : ∀ {v : A} {xs} → v ∈ fromList xs → v ∈ₗ xs
∈-fromList⁻ {xs = _ ∷ _} (here refl)  = here refl
∈-fromList⁻ {xs = _ ∷ _} (there v∈xs) = there (∈-fromList⁻ v∈xs)

------------------------------------------------------------------------
-- Relationship to Any

module _ {P : Pred A p} where

  fromAny : ∀ {n} {xs : Vec A n} → Any P xs → ∃ λ x → x ∈ xs × P x
  fromAny (here px) = -, here refl , px
  fromAny (there v) = Prod.map₂ (Prod.map₁ there) (fromAny v)

  toAny : ∀ {n x} {xs : Vec A n} → x ∈ xs → P x → Any P xs
  toAny (here refl) px = here px
  toAny (there v)   px = there (toAny v px)
