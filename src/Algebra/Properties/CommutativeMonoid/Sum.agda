------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite summations over a commutative monoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; NonZero)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Permutation as Perm using (Permutation; _⟨$⟩ˡ_; _⟨$⟩ʳ_)
open import Data.Fin.Patterns using (0F)
open import Data.Vec.Functional
open import Function.Base using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary.Negation using (contradiction)

module Algebra.Properties.CommutativeMonoid.Sum
  {a ℓ} (M : CommutativeMonoid a ℓ) where

open CommutativeMonoid M
  renaming
  ( _∙_       to _+_
  ; ∙-cong    to +-cong
  ; ∙-congˡ   to +-congˡ
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; ε         to 0#
  )

open import Algebra.Definitions _≈_
open import Algebra.Solver.CommutativeMonoid M
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Re-export summation over monoids

open import Algebra.Properties.Monoid.Sum monoid public

------------------------------------------------------------------------
-- Properties

-- When summing over a function from a finite set, we can pull out any
-- value and move it to the front.
sum-remove : ∀ {n} {i : Fin (suc n)} t → sum t ≈ t i + sum (remove i t)
sum-remove {_}     {zero}   xs = refl
sum-remove {suc n} {suc i}  xs = begin
  t₀ + ∑t           ≈⟨ +-congˡ (sum-remove t) ⟩
  t₀ + (tᵢ + ∑t′)   ≈⟨ solve 3 (λ x y z → x ⊕ (y ⊕ z) ⊜ y ⊕ (x ⊕ z)) refl t₀ tᵢ ∑t′ ⟩
  tᵢ + (t₀ + ∑t′)   ∎
  where
  t = tail xs
  t₀ = head xs
  tᵢ = t i
  ∑t = sum t
  ∑t′ = sum (remove i t)

-- The '∑' operator distributes over addition.
∑-distrib-+ : ∀ {n} (f g : Vector Carrier n) → ∑[ i < n ] (f i + g i) ≈ ∑[ i < n ] f i + ∑[ i < n ] g i
∑-distrib-+ {zero}  f g = sym (+-identityˡ _)
∑-distrib-+ {suc n} f g = begin
  f₀ + g₀ + ∑fg          ≈⟨ +-assoc _ _ _ ⟩
  f₀ + (g₀ + ∑fg)        ≈⟨ +-congˡ (+-congˡ (∑-distrib-+ (f ∘ suc) (g ∘ suc))) ⟩
  f₀ + (g₀ + (∑f + ∑g))  ≈⟨ solve 4 (λ a b c d → a ⊕ (c ⊕ (b ⊕ d)) ⊜ (a ⊕ b) ⊕ (c ⊕ d)) refl f₀ ∑f g₀ ∑g ⟩
  (f₀ + ∑f) + (g₀ + ∑g)  ∎
  where
  f₀ = f 0F
  g₀ = g 0F
  ∑f  = ∑[ i < n ] f (suc i)
  ∑g  = ∑[ i < n ] g (suc i)
  ∑fg = ∑[ i < n ] (f (suc i) + g (suc i))

-- The '∑' operator commutes with itself.
∑-comm : ∀ {m n} (f : Fin m → Fin n → Carrier) →
         ∑[ i < m ] ∑[ j < n ] f i j ≈ ∑[ j < n ] ∑[ i < m ] f i j
∑-comm {zero}  {n} f = sym (sum-replicate-zero n)
∑-comm {suc m} {n} f = begin
  ∑[ j < n ] f zero j + ∑[ i < m ] ∑[ j < n ] f (suc i) j  ≈⟨ +-congˡ (∑-comm (f ∘ suc)) ⟩
  ∑[ j < n ] f zero j + ∑[ j < n ] ∑[ i < m ] f (suc i) j  ≈⟨ sym (∑-distrib-+ (f zero) _) ⟩
  ∑[ j < n ] (f zero j + ∑[ i < m ] f (suc i) j)           ∎

-- Summation is insensitive to permutations of the input
sum-permute : ∀ {m n} f (π : Permutation m n) → sum f ≈ sum (rearrange (π ⟨$⟩ʳ_) f)
sum-permute {zero}  {zero}  f π = refl
sum-permute {zero}  {suc n} f π = contradiction π (Perm.refute λ())
sum-permute {suc m} {zero}  f π = contradiction π (Perm.refute λ())
sum-permute {suc m} {suc n} f π = begin
  sum f                                    ≡⟨⟩
  f 0F  + sum f/0                          ≡˘⟨ P.cong (_+ sum f/0) (P.cong f (Perm.inverseʳ π)) ⟩
  πf π₀ + sum f/0                          ≈⟨ +-congˡ (sum-permute f/0 (Perm.remove π₀ π)) ⟩
  πf π₀ + sum (rearrange (π/0 ⟨$⟩ʳ_) f/0)  ≡˘⟨ P.cong (πf π₀ +_) (sum-cong-≗ (P.cong f ∘ Perm.punchIn-permute′ π 0F)) ⟩
  πf π₀ + sum (remove π₀ πf)               ≈⟨ sym (sum-remove πf) ⟩
  sum πf                                   ∎
  where
  f/0 = remove 0F f
  π₀ = π ⟨$⟩ˡ 0F
  π/0 = Perm.remove π₀ π
  πf = rearrange (π ⟨$⟩ʳ_) f

∑-permute : ∀ {m n} (f : Vector Carrier n) (π : Permutation m n) →
            ∑[ i < n ] f i ≈ ∑[ i < m ] f (π ⟨$⟩ʳ i)
∑-permute f π = sum-permute f π
