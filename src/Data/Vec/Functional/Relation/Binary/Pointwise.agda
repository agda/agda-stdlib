------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to index notation vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Binary.Pointwise where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Vec.Functional as VF hiding (map)
open import Function
open import Level using (Level)
open import Relation.Binary

private
  variable
    a a′ b b′ r s ℓ : Level
    A : Set a
    B : Set b
    A′ : Set a′
    B′ : Set b′

------------------------------------------------------------------------
-- Definition

Pointwise : REL A B ℓ → ∀ {n} → Vector A n → Vector B n → Set ℓ
Pointwise R u v = ∀ i → R (u i) (v i)

------------------------------------------------------------------------
-- Operations

map : {R : REL A B r} {S : REL A B s} →
      R ⇒ S → ∀ {n} → Pointwise R ⇒ Pointwise S {n = n}
map f rs i = f (rs i)

------------------------------------------------------------------------
-- Relational properties

module _ {R : Rel A ℓ} where

  refl : Reflexive R → ∀ {n} → Reflexive (Pointwise R {n = n})
  refl r i = r

  sym : Symmetric R → ∀ {n} → Symmetric (Pointwise R {n = n})
  sym s uv i = s (uv i)

  trans : Transitive R → ∀ {n} → Transitive (Pointwise R {n = n})
  trans t uv vw i = t (uv i) (vw i)

  decidable : Decidable R → ∀ {n} → Decidable (Pointwise R {n = n})
  decidable r? u v = all? λ i → r? (u i) (v i)

------------------------------------------------------------------------
-- map

map⁺ : {R : REL A B r} {S : REL A′ B′ s} {f : A → A′} {g : B → B′} →
       (∀ {x y} → R x y → S (f x) (g y)) → ∀ {n} →
       ∀ {xs ys} → Pointwise R {n = n} xs ys →
                   Pointwise S (VF.map f xs) (VF.map g ys)
map⁺ f rs i = f (rs i)

------------------------------------------------------------------------
-- head

head⁺ : ∀ (R : REL A B r) {n u v} →
        Pointwise R u v → R (head u) (head {n = n} v)
head⁺ R rs = rs zero

------------------------------------------------------------------------
-- tail

tail⁺ : ∀ (R : REL A B r) {n u v} →
        Pointwise R u v → Pointwise R (tail u) (tail {n = n} v)
tail⁺ R rs = rs ∘ suc

------------------------------------------------------------------------
-- _++_

++⁺ : ∀ (R : REL A B r) {m n xs ys xs′ ys′} →
      Pointwise R {n = m} xs ys → Pointwise R {n = n} xs′ ys′ →
      Pointwise R (xs ++ xs′) (ys ++ ys′)
++⁺ R {m = zero} rs rs′ i = rs′ i
++⁺ R {m = suc m} rs rs′ zero = rs zero
++⁺ R {m = suc m} rs rs′ (suc i) = ++⁺ R (rs ∘ suc) rs′ i

++⁻ˡ : ∀ (R : REL A B r) {m n} (xs : Vector A m) (ys : Vector B m)
         {xs′ : Vector A n} {ys′ : Vector B n} →
       Pointwise R (xs ++ xs′) (ys ++ ys′) → Pointwise R xs ys
++⁻ˡ R _ _ rs zero = rs zero
++⁻ˡ R _ _ rs (suc i) = ++⁻ˡ R _ _ (tail⁺ R rs) i

++⁻ʳ : ∀ (R : REL A B r) {m n} (xs : Vector A m) (ys : Vector B m)
         {xs′ : Vector A n} {ys′ : Vector B n} →
       Pointwise R (xs ++ xs′) (ys ++ ys′) → Pointwise R xs′ ys′
++⁻ʳ R {m = zero} _ _ rs = rs
++⁻ʳ R {m = suc m} _ _ rs = ++⁻ʳ R _ _ (tail⁺ R rs)

++⁻ : ∀ (R : REL A B r) {m n} xs ys {xs′ ys′} →
      Pointwise R (xs ++ xs′) (ys ++ ys′) →
      Pointwise R {n = m} xs ys × Pointwise R {n = n} xs′ ys′
++⁻ R _ _ rs = ++⁻ˡ R _ _ rs , ++⁻ʳ R _ _ rs

------------------------------------------------------------------------
-- replicate

replicate⁺ : ∀ {R : REL A B r} {x y n} → R x y →
             Pointwise R {n = n} (replicate x) (replicate y)
replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

⊛⁺ : ∀ {R : REL A B r} {S : REL A′ B′ s} {n}
       {fs : Vector (A → A′) n} {gs : Vector (B → B′) n} {xs ys} →
     Pointwise (λ f g → ∀ {x y} → R x y → S (f x) (g y)) fs gs →
     Pointwise R xs ys → Pointwise S (fs ⊛ xs) (gs ⊛ ys)
⊛⁺ fs xs i = (fs i) (xs i)
