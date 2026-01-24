------------------------------------------------------------------------
-- The Agda standard library
--
-- The Chinese Remainder Theorem for arbitrary rings
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles

module Algebra.Construct.Quotient.Ring.Properties.ChineseRemainderTheorem {c ℓ} (R : Ring c ℓ) where

open Ring R

import Algebra.Construct.DirectProduct as DP
open import Algebra.Construct.Quotient.Ring as QR using (quotientRawRing)
open import Algebra.Ideal R
open import Algebra.Ideal.Coprimality R using (Coprime)
open import Algebra.Ideal.Construct.Intersection R
open import Algebra.Morphism.Structures
open import Algebra.Properties.Ring R
open import Data.Product.Base
open import Relation.Binary.Reasoning.Setoid setoid

module _
  {c₁ c₂ ℓ₁ ℓ₂}
  (I : Ideal c₁ ℓ₁) (J : Ideal c₂ ℓ₂)
  where

  private
    module I = Ideal I
    module J = Ideal J

  CRT : Coprime I J → IsRingIsomorphism (quotientRawRing R (I ∩ J)) (DP.rawRing (quotientRawRing R I) (quotientRawRing R J)) λ x → x , x
  CRT ((m , n) , m+n≈1) = record
    { isRingMonomorphism = record
      { isRingHomomorphism = record
        { isSemiringHomomorphism = record
          { isNearSemiringHomomorphism = record
            { +-isMonoidHomomorphism = record
              { isMagmaHomomorphism = record
                { isRelHomomorphism = record
                  { cong = λ { (t R/I∩J.by p) → (ICarrier.a t R/I.by p) , (ICarrier.b t R/J.by trans p (ICarrier.a≈b t)) }
                  }
                ; homo = λ x y → R/I.≋-refl , R/J.≋-refl
                }
              ; ε-homo = R/I.≋-refl , R/J.≋-refl
              }
            ; *-homo = λ x y → R/I.≋-refl , R/J.≋-refl
            }
          ; 1#-homo = R/I.≋-refl , R/J.≋-refl
          }
        ; -‿homo = λ x → R/I.≋-refl , R/J.≋-refl
        }
        ; injective = λ {((i R/I.by p) , (j R/J.by q)) → record { a≈b = trans (sym p) q } R/I∩J.by p}
      }
    ; surjective = λ (a₁ , a₂) → a₁ * J.ι n + a₂ * I.ι m , λ {z} → λ
      { (record {a = a; b = b; a≈b = a≈b}  R/I∩J.by p) → record
        { fst = a I.I.+ᴹ (a₂ - a₁) I.I.*ₗ m R/I.by begin
          -- introduce a coprimality term
          z - a₁                   ≈⟨ +-congˡ (-‿cong (*-identityʳ a₁)) ⟨
          z - a₁ * 1#              ≈⟨ +-congˡ (-‿cong (*-congˡ m+n≈1)) ⟨
          -- lots and lots of rearrangement
          z - a₁ * (I.ι m + J.ι n)                                          ≈⟨ +-congˡ (-‿cong (distribˡ a₁ (I.ι m) (J.ι n))) ⟩
          z - (a₁ * I.ι m + a₁ * J.ι n)                                     ≈⟨ +-congˡ (-‿cong (+-comm (a₁ * I.ι m) (a₁ * J.ι n))) ⟩
          z - (a₁ * J.ι n + a₁ * I.ι m)                                     ≈⟨ +-congˡ (-‿cong (+-congʳ (+-identityʳ (a₁ * J.ι n)))) ⟨
          z - (a₁ * J.ι n + 0# + a₁ * I.ι m)                                ≈⟨ +-congˡ (-‿cong (+-congʳ (+-congˡ (-‿inverseʳ (a₂ * I.ι m))))) ⟨
          z - (a₁ * J.ι n + (a₂ * I.ι m - a₂ * I.ι m) + a₁ * I.ι m)         ≈⟨ +-congˡ (-‿cong (+-congʳ (+-assoc _ _ _))) ⟨
          z - (a₁ * J.ι n + a₂ * I.ι m - a₂ * I.ι m + a₁ * I.ι m)           ≈⟨ +-congˡ (-‿cong (+-assoc _ _ _)) ⟩
          z - (a₁ * J.ι n + a₂ * I.ι m + (- (a₂ * I.ι m) + a₁ * I.ι m))     ≈⟨ +-congˡ (-‿+-comm _ _) ⟨
          z + (- (a₁ * J.ι n + a₂ * I.ι m) - (- (a₂ * I.ι m) + a₁ * I.ι m)) ≈⟨ +-assoc z _ _ ⟨
          z - (a₁ * J.ι n + a₂ * I.ι m) - (- (a₂ * I.ι m) + a₁ * I.ι m)     ≈⟨ +-congˡ (-‿+-comm _ _) ⟨
          z - (a₁ * J.ι n + a₂ * I.ι m) + (- - (a₂ * I.ι m) - a₁ * I.ι m)   ≈⟨ +-congˡ (+-congʳ (-‿involutive _)) ⟩
          z - (a₁ * J.ι n + a₂ * I.ι m) + (a₂ * I.ι m - a₁ * I.ι m)         ≈⟨ +-congˡ ([y-z]x≈yx-zx _ _ _) ⟨
          -- substitute z-t
          z - (a₁ * J.ι n + a₂ * I.ι m) + (a₂ - a₁) * I.ι m ≈⟨ +-congʳ p ⟩
          -- show we're in I
          I.ι a + (a₂ - a₁) * I.ι m         ≈⟨ +-congˡ (I.ι.*ₗ-homo (a₂ - a₁) m) ⟨
          I.ι a + I.ι ((a₂ - a₁) I.I.*ₗ m)  ≈⟨ I.ι.+ᴹ-homo a _ ⟨
          I.ι (a I.I.+ᴹ (a₂ - a₁) I.I.*ₗ m) ∎
        ; snd = b J.I.+ᴹ (a₁ - a₂) J.I.*ₗ n R/J.by begin
          -- introduce a coprimality term
          z - a₂                   ≈⟨ +-congˡ (-‿cong (*-identityʳ a₂)) ⟨
          z - a₂ * 1#              ≈⟨ +-congˡ (-‿cong (*-congˡ m+n≈1)) ⟨
          -- lots and lots of rearrangement
          z - a₂ * (I.ι m + J.ι n)                                          ≈⟨ +-congˡ (-‿cong (distribˡ a₂ (I.ι m) (J.ι n))) ⟩
          z - (a₂ * I.ι m + a₂ * J.ι n)                                     ≈⟨ +-congˡ (-‿cong (+-congʳ (+-identityʳ (a₂ * I.ι m)))) ⟨
          z - (a₂ * I.ι m + 0# + a₂ * J.ι n)                                ≈⟨ +-congˡ (-‿cong (+-congʳ (+-congˡ (-‿inverseʳ (a₁ * J.ι n))))) ⟨
          z - (a₂ * I.ι m + (a₁ * J.ι n - a₁ * J.ι n) + a₂ * J.ι n)         ≈⟨ +-congˡ (-‿cong (+-congʳ (+-assoc (a₂ * I.ι m) (a₁ * J.ι n) _))) ⟨
          z - (a₂ * I.ι m + a₁ * J.ι n - a₁ * J.ι n + a₂ * J.ι n)           ≈⟨ +-congˡ (-‿cong (+-assoc (a₂ * I.ι m + a₁ * J.ι n) (- (a₁ * J.ι n)) _)) ⟩
          z - (a₂ * I.ι m + a₁ * J.ι n + (- (a₁ * J.ι n) + a₂ * J.ι n))     ≈⟨ +-congˡ (-‿+-comm (a₂ * I.ι m + a₁ * J.ι n) (- (a₁ * J.ι n) + a₂ * J.ι n)) ⟨
          z + (- (a₂ * I.ι m + a₁ * J.ι n) - (- (a₁ * J.ι n) + a₂ * J.ι n)) ≈⟨ +-assoc z (- (a₂ * I.ι m + a₁ * J.ι n)) (- (- (a₁ * J.ι n) + a₂ * J.ι n)) ⟨
          z - (a₂ * I.ι m + a₁ * J.ι n) - (- (a₁ * J.ι n) + a₂ * J.ι n)     ≈⟨ +-cong (+-congˡ (-‿cong (+-comm _ _))) (-‿cong (+-congˡ (-‿involutive _))) ⟨
          z - (a₁ * J.ι n + a₂ * I.ι m) - (- (a₁ * J.ι n) - - (a₂ * J.ι n)) ≈⟨ +-congˡ (-‿cong (-‿+-comm (a₁ * J.ι n) (- (a₂ * J.ι n)))) ⟩
          z - (a₁ * J.ι n + a₂ * I.ι m) - - (a₁ * J.ι n - a₂ * J.ι n)       ≈⟨ +-congˡ (-‿involutive (a₁ * J.ι n - a₂ * J.ι n)) ⟩
          z - (a₁ * J.ι n + a₂ * I.ι m) + (a₁ * J.ι n - a₂ * J.ι n)         ≈⟨ +-congˡ ([y-z]x≈yx-zx (J.ι n) a₁ a₂) ⟨
          -- substitute z-t
          z - (a₁ * J.ι n + a₂ * I.ι m) + (a₁ - a₂) * J.ι n ≈⟨ +-congʳ (trans p a≈b) ⟩
          -- show we're in I
          J.ι b + (a₁ - a₂) * J.ι n          ≈⟨ +-congˡ (J.ι.*ₗ-homo (a₁ - a₂) n) ⟨
          J.ι b + J.ι ((a₁ - a₂) J.I.*ₗ n)   ≈⟨ J.ι.+ᴹ-homo b ((a₁ - a₂) J.I.*ₗ n) ⟨
          J.ι (b J.I.+ᴹ  (a₁ - a₂) J.I.*ₗ n) ∎
        }
      }
    }
    where
      module R/I = QR R I
      module R/J = QR R J
      module R/I∩J = QR R (I ∩ J)
