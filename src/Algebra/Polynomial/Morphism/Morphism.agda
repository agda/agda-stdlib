-- Polynomial Morphisms
open import Algebra.Bundles
  using (CommutativeRing ; CommutativeSemiring; Ring;
         SemiringWithoutAnnihilatingZero; Semiring)

module Algebra.Polynomial.Morphism.Morphism
  {ℓ₁ ℓ₂}
  (R : CommutativeRing ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw using (RawRing)
import Algebra.Definitions as Def
open import Algebra.Morphism.Bundles
  using (RingHomomorphism ; MagmaHomomorphism ; MonoidHomomorphism)
open import Algebra.Morphism.Structures
  using (IsRingHomomorphism ; IsMagmaHomomorphism ; IsSemiringHomomorphism;
         IsNearSemiringHomomorphism ; IsMonoidHomomorphism)
open import Algebra.Polynomial.Base.CommutativeRing R
open import Algebra.Polynomial.Poly.Base.CommutativeRing R
  using (Poly; []≈ ; ≈[]; cons ; cast-lem ; consˡ ; consʳ)
  renaming ( sym to P-sym ; _·_ to _·P_
           ; _+_ to _+P_ ; _*_ to _*P_; _≈_ to _≈P_; -_ to -P_)
open import Algebra.Polynomial.Poly.Properties.CommutativeRing R
  using (cast-p≈p; IsZero⇒≈0; ≈0⇒IsZero; a·p≈a∷[]*p ; *-distrib-shift; shift-is-x*)
  renaming (+-identityˡ to +-P-identityˡ ; +-identityʳ to +-P-identityʳ
            ; zeroˡ to P-zeroˡ; zeroʳ to P-zeroʳ ; *-comm to *-P-comm )
open import Algebra.Polynomial.Properties.CommutativeRing R as P
  using (+-identityˡ; +-identityʳ; +-*-commutativeRing; *-zeroˡ ; *-zeroʳ)
  renaming (rawRing to PolyrawRing)
open import Algebra.Properties.Group
open import Algebra.Properties.Ring using (-‿distribʳ-*)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; suc; pred; _⊔_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All
import Level as L
import Relation.Binary.Morphism.Structures as S
  using (IsRelHomomorphism)

module A = CommutativeRing R
open A
  hiding (distrib)
  renaming
  ( Carrier to A
  ; _≈_ to _≈A_
  ; _+_ to _+A_
  ; _*_ to _*A_
  ; -_ to -A_
  ; 0# to A0#
  ; 1# to A1#)
  
private
  variable
    m n k l : ℕ
    a b c d : A
    p : Poly m
    q : Poly n
    P : Polynomial
    Q : Polynomial

module PolynomialRingMorphism
  {ℓ₃ ℓ₄}
  (B : CommutativeRing ℓ₃ ℓ₄)

  (f : RingHomomorphism {ℓ₁} {ℓ₂} (CommutativeRing.rawRing R) (CommutativeRing.rawRing B))
  where

  module B = CommutativeRing B 
  open B
    using (distrib)
    renaming
    (_≈_ to _≈B_
    ; _+_ to _+B_
    ; _*_ to _*B_
    ; -_ to -B_
    ; setoid to B-Set)
    using (0#; 1#)

  open import Relation.Binary.Reasoning.Setoid B-Set
  open RingHomomorphism f using (⟦_⟧)
  open Def {A = B.Carrier} (_≈B_)

  eval-poly : CommutativeRing.Carrier B → (Poly m) → CommutativeRing.Carrier B
  eval-poly β [] = 0#
  eval-poly β (a ∷ p) = ⟦ a ⟧ +B (β *B eval-poly β p)

  eval : CommutativeRing.Carrier B → Polynomial → CommutativeRing.Carrier B
  eval β (ℕ.zero , []) = 0#
  eval β (suc n , (a ∷ p)) = ⟦ a ⟧ +B (β *B (eval β (n , p)))

  -- prove that eval (0 ∷ 1 ∷ []) is β

  eval-equiv : (β : CommutativeRing.Carrier B) → (p : Poly m) → eval-poly β p ≈B (eval β (m , p))
  eval-equiv {ℕ.zero} β [] = B.refl
  eval-equiv {suc m} β (a ∷ p) = B.+-congˡ (B.*-congˡ (eval-equiv β p))

  eval-poly-cong : ∀ {p : Poly m} → ∀ {q : Poly n} → p ≈P q →
                   (β : CommutativeRing.Carrier B) → (eval-poly β p) ≈B (eval-poly β q)
  eval-poly-cong {p = []} {[]} P≈Q β = B.refl
  eval-poly-cong {p = []} {b ∷ q} p≈q β = begin
    eval-poly β []
      ≈⟨ B.zeroʳ β ⟨
    β *B 0#
      ≈⟨ B.+-identityˡ (β *B eval-poly β []) ⟨
    0# +B β *B eval-poly β []
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
         (RingHomomorphism.+-monoidHomomorphism f)) ⟨
    ⟦ A0# ⟧ +B β *B eval-poly β []
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-poly-cong {p = []} {q = q}
         (P-sym (IsZero⇒≈0 (tail (≈0⇒IsZero (P-sym p≈q))))) β)) ⟩
    ⟦ A0# ⟧ +B β *B eval-poly β q
      ≈⟨ B.+-congʳ (S.IsRelHomomorphism.cong
         (RingHomomorphism.isRelHomomorphism f) (head (≈0⇒IsZero (P-sym p≈q)))) ⟨
    eval-poly β (b ∷ q)
      ∎
  eval-poly-cong {p = a ∷ p} {[]} p≈q β = begin
    eval-poly β (a ∷ p)
      ≈⟨ B.+-congʳ (S.IsRelHomomorphism.cong
         (RingHomomorphism.isRelHomomorphism f) (head (≈0⇒IsZero p≈q))) ⟩
    ⟦ A0# ⟧ +B β *B eval-poly β p
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-poly-cong {p = p} {q = []}
         (IsZero⇒≈0 (tail (≈0⇒IsZero p≈q))) β)) ⟩
    ⟦ A0# ⟧ +B β *B eval-poly β []
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
         (RingHomomorphism.+-monoidHomomorphism f)) ⟩
    0# +B β *B eval-poly β []
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟩
    0# +B 0#
      ≈⟨ B.+-identityʳ 0# ⟩
    eval-poly β []
      ∎
  eval-poly-cong {p = a ∷ p} {b ∷ q} (cons a≈b p≈q) β
    = B.+-cong (S.IsRelHomomorphism.cong (RingHomomorphism.isRelHomomorphism f) a≈b)
      (B.*-congˡ (eval-poly-cong p≈q β))

  eval-cong : (β : CommutativeRing.Carrier B) → P ≈ Q → eval β P ≈B eval β Q
  eval-cong {P = (m , p)} {Q = (n , q)} β P≈Q = begin
    eval β (m , p)
      ≈⟨ eval-equiv β p ⟨
    eval-poly β p
      ≈⟨ eval-poly-cong P≈Q β ⟩
    eval-poly β q
      ≈⟨ eval-equiv β q ⟩
    eval β (n , q)
      ∎

  eval-poly-+-homomorphic : (β : CommutativeRing.Carrier B) → (p : Poly m) → (q : Poly n) →
                            eval-poly β (p +P q) ≈B eval-poly β p +B eval-poly β q
  eval-poly-+-homomorphic β [] q = begin
    eval-poly β ([] +P q) 
      ≈⟨ eval-poly-cong (+-P-identityˡ {m = 0} q) β ⟩
    eval-poly β q
      ≈⟨ B.+-identityˡ (eval-poly β q) ⟨
    eval-poly β [] +B eval-poly β q
      ∎
  eval-poly-+-homomorphic β (a ∷ p) [] = B.sym (B.+-identityʳ (eval-poly β (a ∷ p)))
  eval-poly-+-homomorphic β (a ∷ p) (b ∷ q) = begin
    eval-poly β ((a ∷ p) +P (b ∷ q)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-poly-+-homomorphic β p q)) ⟩
    ⟦ a +A b ⟧ +B (β *B (eval-poly β p +B eval-poly β q))
      ≈⟨ B.+-congˡ (proj₁ distrib β (eval-poly β p) (eval-poly β q)) ⟩
    ⟦ a +A b ⟧ +B (β *B eval-poly β p +B β *B eval-poly β q)
      ≈⟨ B.+-congʳ (IsMagmaHomomorphism.homo (RingHomomorphism.+-isMagmaHomomorphism f) a b) ⟩
    ⟦ a ⟧ +B ⟦ b ⟧ +B (β *B eval-poly β p +B β *B eval-poly β q) 
      ≈⟨ B.+-assoc (⟦ a ⟧ +B ⟦ b ⟧) (β *B eval-poly β p) (β *B eval-poly β q) ⟨
    ⟦ a ⟧ +B ⟦ b ⟧ +B β *B eval-poly β p +B β *B eval-poly β q
      ≈⟨ B.+-congʳ (B.+-assoc ⟦ a ⟧ ⟦ b ⟧ (β *B eval-poly β p)) ⟩
    ⟦ a ⟧ +B (⟦ b ⟧ +B β *B eval-poly β p) +B β *B eval-poly β q
      ≈⟨ B.+-assoc  (⟦ a ⟧) (⟦ b ⟧ +B β *B eval-poly β p) (β *B eval-poly β q) ⟩
    ⟦ a ⟧ +B ( ⟦ b ⟧ +B β *B eval-poly β p +B (β *B eval-poly β q))
      ≈⟨ B.+-congˡ (B.+-congʳ ((B.+-comm (β *B eval-poly β p) ⟦ b ⟧))) ⟨
    ⟦ a ⟧ +B ((β *B eval-poly β p) +B ⟦ b ⟧ +B (β *B eval-poly β q))
      ≈⟨ B.+-congˡ (B.+-assoc (β *B eval-poly β p) ⟦ b ⟧ (β *B eval-poly β q)) ⟩
    ⟦ a ⟧ +B (β *B eval-poly β p +B eval-poly β (b ∷ q))
      ≈⟨ B.+-assoc ⟦ a ⟧ (β *B eval-poly β p) (eval-poly β (b ∷ q)) ⟨ 
    ⟦ a ⟧ +B β *B eval-poly β p +B eval-poly β (b ∷ q)
      ∎

  eval-+-homomorphic : (β : CommutativeRing.Carrier B) → (P : Polynomial) → (Q : Polynomial) →
                       eval β (P + Q) ≈B eval β P +B eval β Q
  eval-+-homomorphic β (m , p) (n , q) = begin
    eval β ((m , p) + (n , q)) 
      ≈⟨ eval-equiv β (p +P q) ⟨
    eval-poly β (p +P q) 
      ≈⟨ eval-poly-+-homomorphic β p q ⟩
    eval-poly β p +B eval-poly β q
      ≈⟨ B.+-cong (eval-equiv β p) (eval-equiv β q) ⟩
    eval β (m , p) +B eval β (n , q)
      ∎

  eval-poly-1#-homomorphic : (β : CommutativeRing.Carrier B) → eval-poly β (A1# ∷ []) ≈B 1#
  eval-poly-1#-homomorphic β = begin
    eval-poly β (A1# ∷ []) 
      ≈⟨ B.+-cong (RingHomomorphism.1#-homo f) (B.zeroʳ β) ⟩
    1# +B 0#
      ≈⟨ B.+-identityʳ 1# ⟩
    1#
      ∎
  
  eval-1#-homomorphic : (β : CommutativeRing.Carrier B) → eval β one ≈B 1#
  eval-1#-homomorphic β = begin
    eval β (1 , (A1# ∷ [])) 
      ≈⟨ eval-equiv β (A1# ∷ []) ⟨
    eval-poly β (A1# ∷ []) 
      ≈⟨ eval-poly-1#-homomorphic β ⟩
    1#
      ∎

  eval-poly-scale :  (β : CommutativeRing.Carrier B) → (a : A) → (p : Poly m) →
                     eval-poly β (a ·P p) ≈B eval-poly β (a ∷ []) *B (eval-poly β p) 
  eval-poly-scale β a [] = begin
    0#
      ≈⟨ B.zeroʳ (⟦ a ⟧ +B β *B 0#) ⟨
    (⟦ a ⟧ +B β *B 0#) *B 0#
    ∎
  eval-poly-scale β a (b ∷ p) = begin
    ⟦ a *A b ⟧ +B β *B eval-poly β (a ·P p) 
      ≈⟨ B.+-congʳ (IsMagmaHomomorphism.homo (RingHomomorphism.*-isMagmaHomomorphism f) a b) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B eval-poly β (a ·P p)  
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-poly-scale β a p)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B (eval-poly β (a ∷ []) *B (eval-poly β p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-congˡ (B.zeroʳ β)))) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B ((⟦ a ⟧ +B 0#) *B (eval-poly β p))
       ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-identityʳ ⟦ a ⟧))) ⟩
    ⟦ a ⟧ *B ⟦ b ⟧ +B β *B ((⟦ a ⟧ *B eval-poly β p)) 
      ≈⟨ B.+-congˡ (B.*-assoc β ⟦ a ⟧ (eval-poly β p)) ⟨
    ⟦ a ⟧ *B ⟦ b ⟧ +B (β *B (⟦ a ⟧) *B (eval-poly β p)) 
      ≈⟨ B.+-congˡ (B.*-congʳ (B.*-comm β ⟦ a ⟧)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B (⟦ a ⟧ *B β) *B eval-poly β p
      ≈⟨ B.+-congˡ (B.*-assoc ⟦ a ⟧ β (eval-poly β p)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B ⟦ a ⟧ *B (β *B eval-poly β p)
      ≈⟨ proj₁ distrib  ⟦ a ⟧ ⟦ b ⟧ ( β *B eval-poly β p)  ⟨
    (⟦ a ⟧) *B (⟦ b ⟧ +B β *B eval-poly β p)
      ≈⟨ B.*-congʳ (B.+-identityʳ ⟦ a ⟧) ⟨
    (⟦ a ⟧ +B 0#) *B (⟦ b ⟧ +B β *B eval-poly β p) 
      ≈⟨ B.*-congʳ (B.+-congˡ (B.zeroʳ β)) ⟨
    (⟦ a ⟧ +B β *B 0#) *B (⟦ b ⟧ +B β *B eval-poly β p)
      ∎

  eval-poly-shift : (β : CommutativeRing.Carrier B) → (p : Poly m) → eval-poly β (A0# ∷ p) ≈B β *B eval-poly β p
  eval-poly-shift β p = begin
    ⟦ A0# ⟧ +B β *B eval-poly β p
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
      (RingHomomorphism.+-monoidHomomorphism f)) ⟩
    0# +B β *B eval-poly β p 
      ≈⟨ B.+-identityˡ (β *B eval-poly β p) ⟩
    β *B eval-poly β p
      ∎

  eval-poly-*-homomorphic : (β : CommutativeRing.Carrier B) → (p : Poly m) →
                            (q : Poly n) → eval-poly β (p *P q) ≈B eval-poly β p *B eval-poly β q
  eval-poly-*-homomorphic β [] q = begin
    eval-poly β ([] *P q)
      ≈⟨ eval-poly-cong (P-zeroˡ q) β ⟩
    eval-poly β []
      ≈⟨ B.zeroˡ (eval-poly β q) ⟨
    eval-poly β [] *B eval-poly β q
      ∎
  eval-poly-*-homomorphic β (a ∷ p) [] = begin
    eval-poly β ((a ∷ p) *P []) 
      ≈⟨ eval-poly-cong (P-zeroʳ (a ∷ p)) β ⟩
    eval-poly β []
      ≈⟨ B.zeroʳ (eval-poly β (a ∷ p)) ⟨
    eval-poly β (a ∷ p) *B eval-poly β []
      ∎
  eval-poly-*-homomorphic {suc m} {suc n} β (a ∷ p) (b ∷ q) = begin
    eval-poly β ((a ∷ p) *P (b ∷ q))
      ≈⟨ eval-poly-cong (cast-p≈p (cast-lem (suc n) (m))) β ⟩
    eval-poly β (a ·P (b ∷ q) +P p *P (A0# ∷ b ∷ q))  
      ≈⟨ eval-poly-+-homomorphic β (a ·P (b ∷ q)) (p *P (A0# ∷ b ∷ q)) ⟩
    eval-poly β (a ·P (b ∷ q)) +B eval-poly β (p *P (A0# ∷ b ∷ q)) 
      ≈⟨ B.+-congʳ (eval-poly-scale β a (b ∷ q)) ⟩
    (eval-poly β (a ∷ []) *B eval-poly β (b ∷ q)) +B eval-poly β (p *P (A0# ∷ b ∷ q))
      ≈⟨ B.+-congˡ (eval-poly-*-homomorphic β p (A0# ∷ b ∷ q)) ⟩
    (eval-poly β (a ∷ []) *B eval-poly β (b ∷ q)) +B (eval-poly β p) *B eval-poly β (A0# ∷ b ∷ q) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-poly-shift β (b ∷ q))) ⟩
    (eval-poly β (a ∷ []) *B eval-poly β (b ∷ q)) +B (eval-poly β p) *B (β *B eval-poly β (b ∷ q))
      ≈⟨ B.+-congʳ (B.*-congʳ (B.+-congˡ (B.zeroʳ β))) ⟩
    (⟦ a ⟧ +B 0#) *B (⟦ b ⟧ +B β *B eval-poly β q) +B eval-poly β p *B (β *B (⟦ b ⟧ +B β *B eval-poly β q)) 
      ≈⟨ B.+-congʳ (B.*-congʳ (B.+-identityʳ ⟦ a ⟧)) ⟩
    (⟦ a ⟧  *B (⟦ b ⟧ +B β *B eval-poly β q) +B  eval-poly β p *B (β *B (⟦ b ⟧ +B β *B eval-poly β q)))
      ≈⟨ B.+-congˡ (B.*-assoc (eval-poly β p) β (⟦ b ⟧ +B β *B eval-poly β q)) ⟨
    (⟦ a ⟧ *B (⟦ b ⟧ +B β *B eval-poly β q) +B (eval-poly β p *B β) *B (⟦ b ⟧ +B β *B eval-poly β q))
      ≈⟨ B.+-congˡ (B.*-congʳ (B.*-comm (eval-poly β p) β)) ⟩
    (⟦ a ⟧ *B (⟦ b ⟧ +B β *B eval-poly β q) +B (β *B eval-poly β p) *B (⟦ b ⟧ +B β *B eval-poly β q))
      ≈⟨ proj₂ distrib (⟦ b ⟧ +B β *B eval-poly β q) ⟦ a ⟧ (β *B eval-poly β p) ⟨
    (⟦ a ⟧ +B β *B eval-poly β p) *B (⟦ b ⟧ +B β *B eval-poly β q)
      ∎

  eval-*-homomorphic : (β : CommutativeRing.Carrier B) → (P : Polynomial) → (Q : Polynomial) →
                       eval β (P * Q)  ≈B eval β P *B eval β Q
  eval-*-homomorphic β (m , p) (n , q) = begin
    eval β ((m , p) * (n , q))
      ≈⟨ eval-equiv β ((p *P q)) ⟨
    eval-poly β (p *P q)
      ≈⟨ eval-poly-*-homomorphic β p q ⟩
     (eval-poly β p *B eval-poly β q)
      ≈⟨ B.*-cong (eval-equiv β p) (eval-equiv β q) ⟩
    eval β (m , p) *B eval β (n , q)
      ∎
 
  eval-poly-inverse-homomorphic : (β : CommutativeRing.Carrier B) → (p : Poly m) →
                                  eval-poly β (-P p) ≈B -B (eval-poly β p)
  eval-poly-inverse-homomorphic β [] = B.sym (ε⁻¹≈ε B.+-group)
  eval-poly-inverse-homomorphic β (a ∷ p) = begin
    eval-poly β (-P (a ∷ p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-poly-inverse-homomorphic β p)) ⟩
    ⟦ -A a ⟧ +B β *B (-B (eval-poly β p))
      ≈⟨ B.+-congˡ (-‿distribʳ-* (CommutativeRing.ring B) β (eval-poly β p)) ⟨
    ⟦ -A a ⟧ +B -B (β *B eval-poly β p)
      ≈⟨ B.+-congʳ (RingHomomorphism.-‿homo f a) ⟩
    -B ⟦ a ⟧ +B -B (β *B eval-poly β p)
      ≈⟨ B.+-comm (-B (β *B eval-poly β p)) (-B ⟦ a ⟧) ⟨
    -B (β *B eval-poly β p) +B -B ⟦ a ⟧
      ≈⟨ ⁻¹-anti-homo-∙ B.+-group ⟦ a ⟧ (β *B eval-poly β p) ⟨
    -B eval-poly β (a ∷ p)
      ∎

  eval-inverse-homomorphic : (β : CommutativeRing.Carrier B) → (P : Polynomial) →
                             eval β (- P) ≈B -B (eval β P) 
  eval-inverse-homomorphic β (m , p) = begin
    eval β (- (m , p)) 
      ≈⟨ eval-equiv β (-P p) ⟨
    eval-poly β (-P p) 
      ≈⟨ eval-poly-inverse-homomorphic β p ⟩
    -B eval-poly β p
      ≈⟨ B.-‿cong (eval-equiv β p) ⟩
    -B eval β (m , p)
      ∎
    
  eval-isRingHomomorphism : (β : CommutativeRing.Carrier B) → IsRingHomomorphism
    (CommutativeRing.rawRing +-*-commutativeRing) (CommutativeRing.rawRing B) (eval β)
  eval-isRingHomomorphism β = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = eval-cong β }
            ; homo = eval-+-homomorphic β
            }
          ; ε-homo = B.refl
          }
        ; *-homo = eval-*-homomorphic β
        }
      ; 1#-homo = eval-1#-homomorphic β
      }
    ; -‿homo = eval-inverse-homomorphic β
    }

---------------- Universal Property of Polynomial Rings ----------------

  x-mapsto-β : (β : CommutativeRing.Carrier B) → eval β (2 , (A0# ∷ A1# ∷ [])) ≈B β
  x-mapsto-β β = begin
    ⟦ A0# ⟧ +B β *B (⟦ A1# ⟧ +B β *B 0#)
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo (RingHomomorphism.+-monoidHomomorphism f)) ⟩
    0# +B (β *B (⟦ A1# ⟧ +B β *B 0#))
      ≈⟨ B.+-identityˡ (β *B (⟦ A1# ⟧ +B β *B 0#))⟩
    β *B (⟦ A1# ⟧ +B β *B 0#)
      ≈⟨ B.*-congˡ (B.+-cong (RingHomomorphism.1#-homo f) (B.zeroʳ β)) ⟩
    β *B (1# +B 0#)
      ≈⟨ B.*-congˡ (B.+-identityʳ 1#) ⟩
    β *B 1#
      ≈⟨ B.*-identityʳ β ⟩
    β
      ∎

-- define a canonical inclusion homomorphism from R to R[x])
  i : A.Carrier → Polynomial
  i r = (1 , (r ∷ []))

  eval-comm : (β : CommutativeRing.Carrier B) → ∀ (r : A.Carrier) → ⟦ r ⟧ ≈B eval β (i r)
  eval-comm β r = begin
    ⟦ r ⟧
      ≈⟨ B.+-identityʳ ⟦ r ⟧ ⟨
    ⟦ r ⟧ +B 0#
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟨
    eval β (1 , (r ∷ []))
      ∎
 
  eval-unique : (β : CommutativeRing.Carrier B) →
                ∀ (ϕ : RingHomomorphism {ℓ₁} {ℓ₁ L.⊔ ℓ₂} (PolyrawRing) (CommutativeRing.rawRing B)) →
                (∀ (r : A.Carrier) → RingHomomorphism.⟦ ϕ ⟧ (i r) ≈B (⟦ r ⟧)) →
                RingHomomorphism.⟦ ϕ ⟧ (2 , (A0# ∷ A1# ∷ [])) ≈B β →
                ∀ (p : Polynomial) → RingHomomorphism.⟦ ϕ ⟧ p ≈B eval β p
  eval-unique β ϕ  _ _ (ℕ.zero , []) = MonoidHomomorphism.ε-homo (RingHomomorphism.+-monoidHomomorphism ϕ)
  eval-unique β ϕ ϕ-comm x-mapsto-β (suc n , (a ∷ p))  = begin
    RingHomomorphism.⟦ ϕ ⟧ (suc n , (a ∷ p))
      ≈⟨ S.IsRelHomomorphism.cong (RingHomomorphism.isRelHomomorphism ϕ)
         (cons ((A.+-identityʳ a)) (P.+-identityˡ (n , p))) ⟨
    RingHomomorphism.⟦ ϕ ⟧ ((1 , (a ∷ [])) + (suc n , (A0# ∷ p)))
      ≈⟨ IsMagmaHomomorphism.homo (RingHomomorphism.+-isMagmaHomomorphism ϕ)
         (1 , (a ∷ [])) (suc n , (A0# ∷ p)) ⟩
    RingHomomorphism.⟦ ϕ ⟧ (1 , (a ∷ [])) +B RingHomomorphism.⟦ ϕ ⟧ (suc n , (A0# ∷ p))
      ≈⟨ B.+-congˡ (S.IsRelHomomorphism.cong (RingHomomorphism.isRelHomomorphism ϕ) (shift-is-x* (p))) ⟩
    RingHomomorphism.⟦ ϕ ⟧ (1 , (a ∷ [])) +B RingHomomorphism.⟦ ϕ ⟧ ((2 , (A0# ∷ A1# ∷ [])) * (n , p))
      ≈⟨ B.+-congˡ (IsMagmaHomomorphism.homo (RingHomomorphism.*-isMagmaHomomorphism ϕ)
         (2 , (A0# ∷ A1# ∷ [])) (n , p)) ⟩
    RingHomomorphism.⟦ ϕ ⟧ (1 , (a ∷ [])) +B RingHomomorphism.⟦ ϕ ⟧ (2 , (A0# ∷ A1# ∷ [])) *B (RingHomomorphism.⟦ ϕ ⟧ (n , p))
      ≈⟨ B.+-congˡ (B.*-cong x-mapsto-β (eval-unique β ϕ ϕ-comm x-mapsto-β (n , p))) ⟩
    RingHomomorphism.⟦ ϕ ⟧ (i a) +B β *B eval β (n , p)
      ≈⟨ B.+-congʳ (ϕ-comm a) ⟩
    eval β (suc n , (a ∷ p))
     ∎

