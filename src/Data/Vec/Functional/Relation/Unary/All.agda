------------------------------------------------------------------------
-- The Agda standard library
--
-- All lifting of predicates to index notation vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Unary.All where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Vec.Functional as VF hiding (map)
open import Function
open import Level using (Level)
open import Relation.Unary

private
  variable
    a b p q ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

All : Pred A ℓ → ∀ {n} → Vector A n → Set ℓ
All P u = ∀ i → P (u i)

------------------------------------------------------------------------
-- Operations

map : {P : Pred A p} {Q : Pred A q} → P ⊆ Q → ∀ {n} → All P {n = n} ⊆ All Q
map f ps i = f (ps i)

------------------------------------------------------------------------
-- map

map⁺ : {P : Pred A p} {Q : Pred B q} {f : A → B} →
       (∀ {x} → P x → Q (f x)) → ∀ {n} →
       (∀ {xs} → All P {n = n} xs → All Q (VF.map f xs))
map⁺ f ps i = f (ps i)

------------------------------------------------------------------------
-- replicate

replicate⁺ : ∀ {P : Pred A p} {x n} → P x → All P (replicate {n = n} x)
replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

⊛⁺ : ∀ {P : Pred A p} {Q : Pred B q} {n} {fs : Vector (A → B) n} {xs} →
     All (λ f → ∀ {x} → P x → Q (f x)) fs → All P xs → All Q (fs ⊛ xs)
⊛⁺ fs xs i = (fs i) (xs i)

------------------------------------------------------------------------
-- head

head⁺ : ∀ (P : Pred A p) {n v} → All P v → P (head {n = n} v)
head⁺ P ps = ps zero

------------------------------------------------------------------------
-- tail

tail⁺ : ∀ (P : Pred A p) {n v} → All P v → All P (tail {n = n} v)
tail⁺ P ps = ps ∘ suc

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {P : Pred A p} where

  all : Decidable P → ∀ {n} → Decidable (All P {n = n})
  all p? u = all? λ i → p? (u i)

  universal : Universal P → ∀ {n} → Universal (All P {n = n})
  universal uni u i = uni (u i)

  satisfiable : Satisfiable P → ∀ {n} → Satisfiable (All P {n = n})
  satisfiable (x , px) = replicate x , replicate⁺ {P = P} px

------------------------------------------------------------------------
-- ++

++⁺ : ∀ (P : Pred A p) {m n xs ys} →
      All P {n = m} xs → All P {n = n} ys → All P (xs ++ ys)
++⁺ P {m = zero} pxs pys = pys
++⁺ P {m = suc m} pxs pys zero = head⁺ P pxs
++⁺ P {m = suc m} pxs pys (suc i) = ++⁺ P (tail⁺ P pxs) pys i

++⁻ˡ : ∀ (P : Pred A p) {m n} (xs : Vector A m) {ys : Vector A n} →
       All P (xs ++ ys) → All P xs
++⁻ˡ P _ ps zero = head⁺ P ps
++⁻ˡ P _ ps (suc i) = ++⁻ˡ P _ (tail⁺ P ps) i

++⁻ʳ : ∀ (P : Pred A p) {m n} (xs : Vector A m) {ys : Vector A n} →
       All P (xs ++ ys) → All P ys
++⁻ʳ P {m = zero} _ ps = ps
++⁻ʳ P {m = suc m} _ ps = ++⁻ʳ P _ (tail⁺ P ps)

++⁻ : ∀ (P : Pred A p) {m n} (xs : Vector A m) {ys : Vector A n} →
      All P (xs ++ ys) → All P xs × All P ys
++⁻ P _ ps = ++⁻ˡ P _ ps , ++⁻ʳ P _ ps
