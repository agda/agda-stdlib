------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver, using the integers as the
-- coefficient ring
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (RawRing; Ring; CommutativeRing )

module Algebra.Solver.Ring.IntegralCoefficients
  {r₁ r₂} (R : CommutativeRing r₁ r₂)
  (open CommutativeRing R)
  where

open import Algebra.Solver.Ring.AlmostCommutativeRing
import Algebra.Properties.Semiring.Mult as SemiringMultiplication
open import Data.Integer using (ℤ; +_; +0; +[1+_]; -[1+_]; _⊖_; _◃_) renaming (_+_ to _ℤ+_; _-_ to _ℤ-_; -_ to ℤ-_; _*_ to _ℤ*_)
open import Data.Integer.Properties as ℤ using (+-*-ring; _≡?_)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Sign.Base using (Sign)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Consequences using (dec⇒weaklyDec)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Properties.Ring ring
open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring using (solve; con; _:+_; _:=_)

private
  ⟦_⟧ₙ : ℕ → Carrier
  ⟦ ℕ.zero ⟧ₙ = 0#
  ⟦ suc n ⟧ₙ = 1# + ⟦ n ⟧ₙ

  ⟦_⟧ : ℤ → Carrier
  ⟦ +_ n ⟧ = ⟦ n ⟧ₙ
  ⟦ -[1+_] n ⟧ = - (1# + ⟦ n ⟧ₙ)

  ⊖-homo : ∀ a b → ⟦ a ⊖ b ⟧ ≈ ⟦ a ⟧ₙ - ⟦ b ⟧ₙ
  ⊖-homo ℕ.zero ℕ.zero = begin
    ⟦ ℕ.zero ⊖ ℕ.zero ⟧ ≡⟨⟩
    0#                  ≈⟨ +-identityʳ _ ⟨
    0# + 0#             ≈⟨ +-congˡ -0#≈0# ⟨
    0# - 0#             ∎
  ⊖-homo ℕ.zero (suc b) = begin
    ⟦ ℕ.zero ⊖ suc b ⟧       ≡⟨⟩
    ⟦ -[1+ b ] ⟧             ≡⟨⟩
    - (1# + ⟦ b ⟧ₙ )         ≈˘⟨ +-identityˡ _ ⟩
    0# - (1# + ⟦ b ⟧ₙ )      ≡⟨⟩
    ⟦ ℕ.zero ⟧ₙ - ⟦ suc b ⟧ₙ ∎
  ⊖-homo (suc a) ℕ.zero = begin
    ⟦ suc a ⊖ ℕ.zero ⟧       ≡⟨⟩
    ⟦ +_ (suc a) ⟧           ≡⟨⟩
    ⟦ suc a ⟧ₙ               ≈˘⟨ +-identityʳ _ ⟩
    ⟦ suc a ⟧ₙ + 0#          ≈˘⟨ +-congˡ -0#≈0# ⟩
    ⟦ suc a ⟧ₙ - 0#          ≡⟨⟩
    ⟦ suc a ⟧ₙ - ⟦ ℕ.zero ⟧ₙ ∎
  ⊖-homo (suc a) (suc b) = begin
    ⟦ suc a ⊖ suc b ⟧               ≡⟨ ≡.cong ⟦_⟧ (ℤ.[1+m]⊖[1+n]≡m⊖n a b) ⟩
    ⟦ a ⊖ b ⟧                       ≈⟨ ⊖-homo a b ⟩
    ⟦ a ⟧ₙ - ⟦ b ⟧ₙ                 ≈˘⟨ +-identityʳ _ ⟩
    ⟦ a ⟧ₙ - ⟦ b ⟧ₙ + 0#            ≈˘⟨ +-congˡ (-‿inverseˡ _) ⟩
    (⟦ a ⟧ₙ - ⟦ b ⟧ₙ) + (- 1# + 1#) ≈⟨ solve 4 (λ a -b o mo → (a :+ -b) :+ (mo :+ o) := (o :+ a) :+ (mo :+ -b) ) refl _ _ _ _ ⟩
    (1# + ⟦ a ⟧ₙ) + (- 1# - ⟦ b ⟧ₙ) ≈⟨ +-congˡ (-‿+-comm _ _) ⟩
    (1# + ⟦ a ⟧ₙ) - (1# + ⟦ b ⟧ₙ)   ≡⟨⟩
    ⟦ suc a ⟧ₙ - ⟦ suc b ⟧ₙ         ∎

  +-homoₙ : ∀ a b → ⟦ a ℕ.+ b ⟧ₙ ≈ ⟦ a ⟧ₙ + ⟦ b ⟧ₙ
  +-homoₙ ℕ.zero b = begin
    ⟦ ℕ.zero ℕ.+ b ⟧ₙ    ≡⟨⟩
    ⟦ b ⟧ₙ               ≈˘⟨ +-identityˡ _ ⟩
    0# + ⟦ b ⟧ₙ          ≡⟨⟩
    ⟦ ℕ.zero ⟧ₙ + ⟦ b ⟧ₙ ∎
  +-homoₙ (suc a) b = begin
    ⟦ suc a ℕ.+ b ⟧ₙ       ≡⟨⟩
    ⟦ suc (a ℕ.+ b) ⟧ₙ     ≡⟨⟩
    1# + ⟦ a ℕ.+ b ⟧ₙ      ≈⟨ +-congˡ (+-homoₙ a b) ⟩
    1# + (⟦ a ⟧ₙ + ⟦ b ⟧ₙ) ≈˘⟨ +-assoc _ _ _ ⟩
    (1# + ⟦ a ⟧ₙ) + ⟦ b ⟧ₙ ≡⟨⟩
    ⟦ suc a ⟧ₙ + ⟦ b ⟧ₙ    ∎

  +-homo : ∀ a b → ⟦ a ℤ+ b ⟧ ≈ ⟦ a ⟧ + ⟦ b ⟧
  +-homo (+_ a) (+_ b) = begin
    ⟦ + a ℤ+ + b ⟧    ≡⟨⟩
    ⟦ + (a ℕ.+ b) ⟧   ≡⟨⟩
    ⟦ a ℕ.+ b ⟧ₙ      ≈⟨ +-homoₙ a b ⟩
    ⟦ a ⟧ₙ + ⟦ b ⟧ₙ   ≡⟨⟩
    ⟦ + a ⟧ + ⟦ + b ⟧ ∎
  +-homo (+_ a) (-[1+_] b) = begin
    ⟦ + a ℤ+ -[1+ b ] ⟧    ≡⟨⟩
    ⟦ a ⊖ (ℕ.suc b) ⟧      ≈⟨ ⊖-homo a (ℕ.suc b) ⟩
    ⟦ a ⟧ₙ - ⟦ ℕ.suc b ⟧ₙ  ≡⟨⟩
    ⟦ + a ⟧ + ⟦ -[1+ b ] ⟧ ∎
  +-homo (-[1+_] a) (+_ b) = begin
    ⟦ -[1+ a ] ℤ+ + b ⟧ ≡⟨⟩
    ⟦ b ⊖ (ℕ.suc a) ⟧ ≈⟨ ⊖-homo b (ℕ.suc a) ⟩
    ⟦ b ⟧ₙ - ⟦ ℕ.suc a ⟧ₙ  ≡⟨⟩
    ⟦ + b ⟧ + ⟦ -[1+ a ] ⟧ ≈⟨ +-comm _ _ ⟩
    ⟦ -[1+ a ] ⟧ + ⟦ + b ⟧ ∎
  +-homo (-[1+_] a) (-[1+_] b) = begin
    ⟦ -[1+ a ] ℤ+ -[1+ b ] ⟧          ≡⟨⟩
    ⟦ -[1+ suc (a ℕ.+ b) ] ⟧          ≡⟨⟩
    - (1# + (1# + ⟦ a ℕ.+ b ⟧ₙ))      ≈⟨ -‿cong (+-congˡ (+-congˡ (+-homoₙ a b))) ⟩
    - (1# + (1# + (⟦ a ⟧ₙ + ⟦ b ⟧ₙ))) ≈⟨ -‿cong (solve 2 (λ a b → con 1 :+ (con 1 :+ (a :+ b)) := (con 1 :+ a) :+ (con 1 :+ b) ) refl ⟦ a ⟧ₙ ⟦ b ⟧ₙ) ⟩
    - ((1# + ⟦ a ⟧ₙ) + (1# + ⟦ b ⟧ₙ)) ≈˘⟨ -‿+-comm _ _ ⟩
    - (1# + ⟦ a ⟧ₙ) - (1# + ⟦ b ⟧ₙ)   ≡⟨⟩
    ⟦ -[1+ a ] ⟧ + ⟦ -[1+ b ] ⟧       ∎

  -‿homo : ∀ a → ⟦ ℤ- a ⟧ ≈ - ⟦ a ⟧
  -‿homo +[1+ n ] = begin
    ⟦ ℤ- +[1+ n ] ⟧  ≡⟨⟩
    ⟦ -[1+ n ] ⟧     ≡⟨⟩
    - (1# +  ⟦ n ⟧ₙ) ≡⟨⟩
    - ⟦ +[1+ n ] ⟧   ∎
  -‿homo +0 = sym -0#≈0#
  -‿homo -[1+ n ] = begin
    ⟦ ℤ- -[1+ n ] ⟧   ≡⟨⟩
    ⟦ +[1+ n ] ⟧      ≡⟨⟩
    ⟦ + (ℕ.suc n) ⟧   ≡⟨⟩
    1# + ⟦ n ⟧ₙ       ≈˘⟨ -‿involutive (1# + ⟦ n ⟧ₙ) ⟩
    - - (1# + ⟦ n ⟧ₙ) ≡⟨⟩
    - ⟦ -[1+ n ] ⟧    ∎

  *-homoₙ : ∀ a b → ⟦ a ℕ.* b ⟧ₙ ≈ ⟦ a ⟧ₙ * ⟦ b ⟧ₙ
  *-homoₙ ℕ.zero b = begin
    ⟦ ℕ.zero ℕ.* b ⟧ₙ    ≡⟨⟩
    0#                   ≈˘⟨ zeroˡ ⟦ b ⟧ₙ ⟩
    ⟦ ℕ.zero ⟧ₙ * ⟦ b ⟧ₙ ∎
  *-homoₙ (suc a) b = begin
    ⟦ suc a ℕ.* b ⟧ₙ                ≡⟨⟩
    ⟦ b ℕ.+ a ℕ.* b ⟧ₙ              ≈⟨ +-homoₙ b (a ℕ.* b) ⟩
    ⟦ b ⟧ₙ + ⟦ a ℕ.* b ⟧ₙ           ≈⟨ +-congˡ (*-homoₙ a b) ⟩
    ⟦ b ⟧ₙ + ⟦ a ⟧ₙ * ⟦ b ⟧ₙ        ≈⟨ +-congʳ (sym (*-identityˡ ⟦ b ⟧ₙ)) ⟩
    (1# * ⟦ b ⟧ₙ) + ⟦ a ⟧ₙ * ⟦ b ⟧ₙ ≈˘⟨ distribʳ ⟦ b ⟧ₙ 1# ⟦ a ⟧ₙ ⟩
    (1# + ⟦ a ⟧ₙ) * ⟦ b ⟧ₙ          ≡⟨⟩
    ⟦ suc a ⟧ₙ * ⟦ b ⟧ₙ             ∎

  *-homo : ∀ a b → ⟦ a ℤ* b ⟧ ≈ ⟦ a ⟧ * ⟦ b ⟧
  *-homo (+ a) (+ b) = begin
    ⟦ + a ℤ* + b ⟧       ≡⟨⟩
    ⟦ Sign.+ ◃ a ℕ.* b ⟧ ≡⟨ ≡.cong ⟦_⟧ (ℤ.+◃n≡+n (a ℕ.* b)) ⟩
    ⟦ + (a ℕ.* b) ⟧      ≡⟨⟩
    ⟦ a ℕ.* b ⟧ₙ         ≈⟨ *-homoₙ a b ⟩
    ⟦ a ⟧ₙ * ⟦ b ⟧ₙ      ≡⟨⟩
    ⟦ + a ⟧ * ⟦ + b ⟧    ∎
  *-homo (+ a) (-[1+ b ]) = begin
    ⟦ + a ℤ* -[1+ b ] ⟧        ≡⟨⟩
    ⟦ Sign.- ◃ (a ℕ.* suc b) ⟧ ≡⟨ ≡.cong ⟦_⟧ (ℤ.-◃n≡-n (a ℕ.* suc b)) ⟩
    ⟦ ℤ- + (a ℕ.* suc b) ⟧     ≈⟨ -‿homo (+ (a ℕ.* suc b)) ⟩
    - ⟦ + (a ℕ.* suc b) ⟧      ≡⟨⟩
    - ⟦ a ℕ.* suc b ⟧ₙ         ≈⟨ -‿cong (*-homoₙ a (suc b)) ⟩
    - (⟦ a ⟧ₙ * ⟦ suc b ⟧ₙ)    ≈⟨ -‿distribʳ-* ⟦ a ⟧ₙ ⟦ suc b ⟧ₙ ⟩
    ⟦ a ⟧ₙ * - ⟦ suc b ⟧ₙ      ≡⟨⟩
    ⟦ + a ⟧ * ⟦ -[1+ b ] ⟧     ∎
  *-homo (-[1+ a ]) (+ b) = begin
    ⟦ -[1+ a ] ℤ* + b ⟧    ≡⟨ ≡.cong ⟦_⟧ (ℤ.*-comm -[1+ a ] (+ b)) ⟩
    ⟦ + b ℤ* -[1+ a ] ⟧    ≈⟨ *-homo (+ b) -[1+ a ] ⟩
    ⟦ + b ⟧ * ⟦ -[1+ a ] ⟧ ≈⟨ *-comm ⟦ + b ⟧ ⟦ -[1+ a ] ⟧ ⟩
    ⟦ -[1+ a ] ⟧ * ⟦ + b ⟧ ∎
  *-homo (-[1+ a ]) (-[1+ b ]) = begin
    ⟦ -[1+ a ] ℤ* -[1+ b ] ⟧         ≡⟨⟩
    ⟦ Sign.+ ◃ ℕ.suc a ℕ.* ℕ.suc b ⟧ ≡⟨ ≡.cong ⟦_⟧ (ℤ.+◃n≡+n (ℕ.suc a ℕ.* ℕ.suc b)) ⟩
    ⟦ + (ℕ.suc a ℕ.* ℕ.suc b) ⟧      ≡⟨⟩
    ⟦ ℕ.suc a ℕ.* ℕ.suc b ⟧ₙ         ≈⟨ *-homoₙ (ℕ.suc a) (ℕ.suc b) ⟩
    ⟦ ℕ.suc a ⟧ₙ * ⟦ ℕ.suc b ⟧ₙ      ≈˘⟨ [-x][-y]≈xy ⟦ suc a ⟧ₙ ⟦ suc b ⟧ₙ ⟩
    - ⟦ ℕ.suc a ⟧ₙ * - ⟦ ℕ.suc b ⟧ₙ  ≡⟨⟩
    ⟦ -[1+ a ] ⟧ * ⟦ -[1+ b ] ⟧      ∎

  homomorphism : Ring.rawRing +-*-ring -Raw-AlmostCommutative⟶ fromCommutativeRing R
  homomorphism = record
                  { ⟦_⟧ = ⟦_⟧
                  ; +-homo = +-homo
                  ; *-homo = *-homo
                  ; -‿homo = -‿homo
                  ; 0-homo = refl
                  ; 1-homo = +-identityʳ 1#
                  }

  dec : ∀ m n → Maybe (⟦ m ⟧ ≈ ⟦ n ⟧)
  dec m n = map (λ { ≡.refl → refl }) (dec⇒weaklyDec _≡?_ m n)

open import Algebra.Solver.Ring _ _ homomorphism dec public

