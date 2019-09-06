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
    R : REL A B r
    S : REL A B s
    m n : ℕ

------------------------------------------------------------------------
-- Definition

Pointwise : REL A B ℓ → Vector A n → Vector B n → Set ℓ
Pointwise R u v = ∀ i → R (u i) (v i)

------------------------------------------------------------------------
-- Operations

map : R ⇒ S → Pointwise {n = n} R ⇒ Pointwise S
map f rs i = f (rs i)

------------------------------------------------------------------------
-- Relational properties

refl : {R : Rel A ℓ} → Reflexive R → Reflexive (Pointwise {n = n} R)
refl r i = r

sym : {R : Rel A ℓ} → Symmetric R → Symmetric (Pointwise {n = n} R)
sym s uv i = s (uv i)

trans : {R : Rel A ℓ} → Transitive R → Transitive (Pointwise {n = n} R)
trans t uv vw i = t (uv i) (vw i)

decidable : Decidable R → Decidable (Pointwise {n = n} R)
decidable r? u v = all? λ i → r? (u i) (v i)

------------------------------------------------------------------------
-- map

map⁺ : {R : REL A B r} {S : REL A′ B′ s} {f : A → A′} {g : B → B′} →
       (∀ {x y} → R x y → S (f x) (g y)) →
       ∀ {xs ys} → Pointwise {n = n} R xs ys →
                   Pointwise S (VF.map f xs) (VF.map g ys)
map⁺ f rs i = f (rs i)

------------------------------------------------------------------------
-- head

head⁺ : ∀ (R : REL A B r) {u v} →
        Pointwise {n = suc n} R u v → R (head u) (head v)
head⁺ R rs = rs zero

------------------------------------------------------------------------
-- tail

tail⁺ : ∀ (R : REL A B r) {u v} →
        Pointwise {n = suc n} R u v → Pointwise R (tail u) (tail v)
tail⁺ R rs = rs ∘ suc

------------------------------------------------------------------------
-- _++_

++⁺ : ∀ (R : REL A B r) {xs ys xs′ ys′} →
      Pointwise {n = m} R xs ys → Pointwise {n = n} R xs′ ys′ →
      Pointwise R (xs ++ xs′) (ys ++ ys′)
++⁺ {m = zero} R rs rs′ i = rs′ i
++⁺ {m = suc m} R rs rs′ zero = rs zero
++⁺ {m = suc m} R rs rs′ (suc i) = ++⁺ R (rs ∘ suc) rs′ i

++⁻ˡ : ∀ (R : REL A B r) (xs : Vector A m) (ys : Vector B m)
         {xs′ : Vector A n} {ys′ : Vector B n} →
       Pointwise R (xs ++ xs′) (ys ++ ys′) → Pointwise R xs ys
++⁻ˡ R _ _ rs zero = rs zero
++⁻ˡ R _ _ rs (suc i) = ++⁻ˡ R _ _ (tail⁺ R rs) i

++⁻ʳ : ∀ (R : REL A B r) (xs : Vector A m) (ys : Vector B m)
         {xs′ : Vector A n} {ys′ : Vector B n} →
       Pointwise R (xs ++ xs′) (ys ++ ys′) → Pointwise R xs′ ys′
++⁻ʳ {m = zero} R _ _ rs = rs
++⁻ʳ {m = suc m} R _ _ rs = ++⁻ʳ R _ _ (tail⁺ R rs)

++⁻ : ∀ (R : REL A B r) xs ys {xs′ ys′} → Pointwise R (xs ++ xs′) (ys ++ ys′) →
      Pointwise {n = m} R xs ys × Pointwise {n = n} R xs′ ys′
++⁻ R _ _ rs = ++⁻ˡ R _ _ rs , ++⁻ʳ R _ _ rs

------------------------------------------------------------------------
-- replicate

replicate⁺ : ∀ {x y} → R x y → Pointwise {n = n} R (replicate x) (replicate y)
replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

⊛⁺ : ∀ {R : REL A B r} {S : REL A′ B′ s}
       {fs : Vector (A → A′) n} {gs : Vector (B → B′) n} {xs ys} →
     Pointwise (λ f g → ∀ {x y} → R x y → S (f x) (g y)) fs gs →
     Pointwise R xs ys → Pointwise S (fs ⊛ xs) (gs ⊛ ys)
⊛⁺ fs xs i = (fs i) (xs i)
