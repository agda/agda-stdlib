{-# OPTIONS --without-K --safe #-}

module Algebra.Solver.Ring.Simple.Solver where

open import Algebra.Construct.Ring.Expr public
open import Algebra.Solver.Ring.Simple.AlmostCommutativeRing public
  hiding (-raw-almostCommutative⟶)
open import Algebra.Solver.Ring.AlmostCommutativeRing
  using (-raw-almostCommutative⟶)
open import Algebra.Construct.Polynomial.Parameters
open import Function
open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Vec hiding (_⊛_)
open import Data.Vec.N-ary

module Ops {ℓ₁ ℓ₂} (ring : AlmostCommutativeRing ℓ₁ ℓ₂) where
  open AlmostCommutativeRing ring

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
          ; -‿cong = -‿cong
          ; -‿*-distribˡ = -‿*-distribˡ
          ; -‿+-comm = -‿+-comm
          }
      }
    ; morphism = -raw-almostCommutative⟶ _
    ; Zero-C⟶Zero-R = zero-homo
    }
  open Eval rawRing id public

  open import Algebra.Construct.Polynomial.Base (Homomorphism.from homo)

  norm : ∀ {n} → Expr Carrier n → Poly n
  norm (Κ x)   = κ x
  norm (Ι x)   = ι x
  norm (x ⊕ y) = norm x ⊞ norm y
  norm (x ⊗ y) = norm x ⊠ norm y
  norm (⊝ x)   = ⊟ norm x
  norm (x ⊛ i) = norm x ⊡ i

  ⟦_⇓⟧ : ∀ {n} → Expr Carrier n → Vec Carrier n → Carrier
  ⟦ expr ⇓⟧ = ⟦ norm expr ⟧ₚ where

    open import Algebra.Construct.Polynomial.Semantics homo
      renaming (⟦_⟧ to ⟦_⟧ₚ)

  correct : ∀ {n} (expr : Expr Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
  correct {n = n} = go
    where
    open import Algebra.Construct.Polynomial.Homomorphism homo

    go : ∀ (expr : Expr Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
    go (Κ x)   ρ = κ-hom x ρ
    go (Ι x)   ρ = ι-hom x ρ
    go (x ⊕ y) ρ = ⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ +-cong ⟩ go y ρ)
    go (x ⊗ y) ρ = ⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ *-cong ⟩ go y ρ)
    go (⊝ x)   ρ = ⊟-hom (norm x) ρ ⟨ trans ⟩ -‿cong (go x ρ)
    go (x ⊛ i) ρ = ⊡-hom (norm x) i ρ ⟨ trans ⟩ pow-cong i (go x ρ)

  open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public

solve : ∀ {ℓ₁ ℓ₂}
      → (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
      → (n : ℕ)
      → (f : N-ary n (Expr (AlmostCommutativeRing.Carrier ring) n) (Expr (AlmostCommutativeRing.Carrier ring) n × Expr (AlmostCommutativeRing.Carrier ring) n))
      → Eqʰ n (AlmostCommutativeRing._≈_ ring) (curryⁿ (Ops.⟦_⇓⟧ ring  (proj₁ (Ops.close ring n f)))) (curryⁿ (Ops.⟦_⇓⟧ ring (proj₂ (Ops.close ring n f))))
      → Eq  n (AlmostCommutativeRing._≈_ ring) (curryⁿ (Ops.⟦_⟧ ring (proj₁ (Ops.close ring n f)))) (curryⁿ (Ops.⟦_⟧ ring (proj₂ (Ops.close ring n f))))
solve ring = solve′
  where
  open Ops ring renaming (solve to solve′)
{-# INLINE solve #-}

_⊜_ : ∀ {ℓ₁ ℓ₂}
    → (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
    → (n : ℕ)
    → Expr (AlmostCommutativeRing.Carrier ring) n
    → Expr (AlmostCommutativeRing.Carrier ring) n
    → Expr (AlmostCommutativeRing.Carrier ring) n × Expr (AlmostCommutativeRing.Carrier ring) n
_⊜_ _ _ = _,_
{-# INLINE _⊜_ #-}
