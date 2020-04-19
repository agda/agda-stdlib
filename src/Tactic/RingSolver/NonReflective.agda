------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of the ring solver that requires you to manually
-- pass the equation you wish to solve.
------------------------------------------------------------------------

-- You'll probably want to use `Tactic.RingSolver` instead which uses
-- reflection to automatically extract the equation.

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.AlmostCommutativeRing

module Tactic.RingSolver.NonReflective
  {ℓ₁ ℓ₂} (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
  (let open AlmostCommutativeRing ring)
  where

open import Algebra.Morphism
open import Function
open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Maybe.Base
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Vec hiding (_⊛_)
open import Data.Vec.N-ary

open import Tactic.RingSolver.Core.Polynomial.Parameters
open import Tactic.RingSolver.Core.Expression public

module Ops where
  zero-homo : ∀ x → T (is-just (0≟ x)) → 0# ≈ x
  zero-homo x _ with 0≟ x
  zero-homo x _  | just p = p
  zero-homo x () | nothing

  homo : Homomorphism ℓ₁ ℓ₂ ℓ₁ ℓ₂
  homo = record
    { from = record
      { rawRing = AlmostCommutativeRing.rawRing ring
      ; isZero  = λ x → is-just (0≟ x)
      }
    ; to = record
      { isAlmostCommutativeRing = record
          { isCommutativeSemiring = isCommutativeSemiring
          ; -‿cong       = -‿cong
          ; -‿*-distribˡ = -‿*-distribˡ
          ; -‿+-comm     = -‿+-comm
          }
      }
    ; morphism      = -raw-almostCommutative⟶ ring
    ; Zero-C⟶Zero-R = zero-homo
    }
  open Eval rawRing id public

  open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homo)

  norm : ∀ {n} → Expr Carrier n → Poly n
  norm (Κ x)   = κ x
  norm (Ι x)   = ι x
  norm (x ⊕ y) = norm x ⊞ norm y
  norm (x ⊗ y) = norm x ⊠ norm y
  norm (⊝ x)   = ⊟ norm x
  norm (x ⊛ i) = norm x ⊡ i

  ⟦_⇓⟧ : ∀ {n} → Expr Carrier n → Vec Carrier n → Carrier
  ⟦ expr ⇓⟧ = ⟦ norm expr ⟧ₚ where

    open import Tactic.RingSolver.Core.Polynomial.Semantics homo
      renaming (⟦_⟧ to ⟦_⟧ₚ)

  correct : ∀ {n} (expr : Expr Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
  correct {n = n} = go
    where
    open import Tactic.RingSolver.Core.Polynomial.Homomorphism homo

    go : ∀ (expr : Expr Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
    go (Κ x)   ρ = κ-hom x ρ
    go (Ι x)   ρ = ι-hom x ρ
    go (x ⊕ y) ρ = ⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ +-cong ⟩ go y ρ)
    go (x ⊗ y) ρ = ⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ *-cong ⟩ go y ρ)
    go (⊝ x)   ρ = ⊟-hom (norm x) ρ   ⟨ trans ⟩ -‿cong (go x ρ)
    go (x ⊛ i) ρ = ⊡-hom (norm x) i ρ ⟨ trans ⟩ pow-cong i (go x ρ)

  open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public

solve : ∀ (n : ℕ) →
        (f : N-ary n (Expr Carrier n) (Expr Carrier n × Expr Carrier n)) →
        Eqʰ n _≈_ (curryⁿ (Ops.⟦_⇓⟧ (proj₁ (Ops.close n f)))) (curryⁿ (Ops.⟦_⇓⟧ (proj₂ (Ops.close n f)))) →
        Eq  n _≈_ (curryⁿ (Ops.⟦_⟧  (proj₁ (Ops.close n f)))) (curryⁿ (Ops.⟦_⟧  (proj₂ (Ops.close n f))))
solve = Ops.solve
{-# INLINE solve #-}

_⊜_ : ∀ (n : ℕ) →
      Expr Carrier n →
      Expr Carrier n →
      Expr Carrier n × Expr Carrier n
_⊜_ _ = _,_
{-# INLINE _⊜_ #-}
