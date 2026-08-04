-- Polynomial Morphisms
open import Algebra.Bundles
  using (CommutativeRing ; CommutativeSemiring; Ring;
         SemiringWithoutAnnihilatingZero; Semiring)

module ALgebra.Polynomial.Morphism.Morphism
  {ℓ₁ ℓ₂}
  (R : CommutativeRing ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw using (RawRing)
open import Algebra.Morphism.Bundles
  using (RingHomomorphism ; MagmaHomomorphism ; MonoidHomomorphism)
open import Algebra.Morphism.Structures
  using (IsRingHomomorphism ; IsMagmaHomomorphism ; IsSemiringHomomorphism;
         IsNearSemiringHomomorphism ; IsMonoidHomomorphism)
open import Algebra.Polynomial.Poly.Base2 R
  using (Poly; []≈ ; ≈[]; cons ; cast-lem ; consˡ ; consʳ)
  renaming ( sym to P-sym ; _·_ to _·P_
           ; _+_ to _+P_ ; _*_ to _*P_; _≈_ to _≈P_; -_ to -P_)
open import Algebra.Polynomial.Poly.Properties2 R
  using (cast-p≈p; IsZero⇒≈0; ≈0⇒IsZero; a·p≈a∷[]*p ; *-distrib-shift)
  renaming  (+-identityˡ to +-P-identityˡ ; +-identityʳ to +-P-identityʳ
            ; zeroˡ to P-zeroˡ; zeroʳ to P-zeroʳ ; *-comm to *-P-comm )
open import Algebra.Polynomial.Base2 R
open import Algebra.Polynomial.Properties2 R as P
  using (+-identityˡ; +-identityʳ; +-*-commutativeRing; *-zeroˡ ; *-zeroʳ)

import Algebra.Definitions.RawSemiring as Def
import Algebra.Definitions as D 
open import Algebra.Properties.Group
open import Algebra.Properties.Ring
open import Data.Nat.Base as ℕ using (ℕ; suc; pred; _⊔_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All
open import Data.Product.Base using (proj₁ ; proj₂)
import Level as L
import Relation.Binary.Morphism.Structures as S
  using (IsRelHomomorphism)
open import Relation.Binary.PropositionalEquality.Core using (cong)

module R = CommutativeRing R
open R
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
  (β : CommutativeRing.Carrier B) 

  (f : RingHomomorphism {ℓ₁} {ℓ₂}
       (CommutativeRing.rawRing R) (CommutativeRing.rawRing B) )
  where

  module B = CommutativeRing B 
  open B
    using (semiringWithoutOne ; isSemiringWithoutOne ; distrib)
    renaming
    (_≈_ to _≈B_
    ; _+_ to _+B_
    ; _*_ to _*B_
    ; -_ to -B_
    ; setoid to B-Set)
    using (0#; 1#)

  open import Relation.Binary.Reasoning.Setoid B-Set
    
  open RingHomomorphism f using (⟦_⟧)
  open D {A = B.Carrier} (_≈B_)
    using (_MiddleFourExchange_; _DistributesOverˡ_)

  eval-p : Poly m → CommutativeRing.Carrier B
  eval-p [] = 0#
  eval-p (a ∷ p) =  ⟦ a ⟧ +B (β *B eval-p p )


  eval : Polynomial → CommutativeRing.Carrier B
  eval (ℕ.zero , []) = 0#
  eval (suc n , (a ∷ p)) = ⟦ a ⟧ +B (β *B eval (n , p) )

 

  eval-equiv : (p : Poly m) → eval-p p ≈B (eval (m , p))
  eval-equiv {ℕ.zero} [] = B.refl
  eval-equiv {suc m} (a ∷ p) = begin
    ⟦ a ⟧ +B β *B eval-p p
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-equiv p) ) ⟩
    ⟦ a ⟧ +B β *B eval (m , p)
      ∎


  eval-p-cong : ∀ {p : Poly m} → ∀ {q : Poly n} → p ≈P q → (eval-p p) ≈B (eval-p q)
  eval-p-cong {p = []} {[]} P≈Q = B.refl
  eval-p-cong {p = []} {b ∷ q} p≈q = begin
    eval-p []
      ≈⟨ B.zeroʳ β ⟨
    β *B 0#
      ≈⟨ B.+-identityˡ (β *B eval-p []) ⟨
    0# +B β *B eval-p []
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
         (RingHomomorphism.+-monoidHomomorphism f)) ⟨
    ⟦ A0# ⟧ +B β *B eval-p []
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-p-cong {p = []} {q = q}
         (P-sym (IsZero⇒≈0 (tail (≈0⇒IsZero (P-sym p≈q))))))) ⟩
    ⟦ A0# ⟧ +B β *B eval-p q
      ≈⟨ B.+-congʳ (S.IsRelHomomorphism.cong
         (RingHomomorphism.isRelHomomorphism f) (head (≈0⇒IsZero (P-sym p≈q)))) ⟨
    eval-p (b ∷ q)
      ∎
  eval-p-cong {p = a ∷ p} {[]} p≈q = begin
    eval-p (a ∷ p)
      ≈⟨ B.+-congʳ (S.IsRelHomomorphism.cong
         (RingHomomorphism.isRelHomomorphism f) (head (≈0⇒IsZero p≈q))) ⟩
    ⟦ A0# ⟧ +B β *B eval-p p
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-p-cong {p = p} {q = []}
         (IsZero⇒≈0 (tail (≈0⇒IsZero p≈q))))) ⟩
    ⟦ A0# ⟧ +B β *B eval-p []
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
         (RingHomomorphism.+-monoidHomomorphism f)) ⟩
    0# +B β *B eval-p []
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟩
    0# +B 0#
      ≈⟨ B.+-identityʳ 0# ⟩
    eval-p []
      ∎
  eval-p-cong {p = a ∷ p} {b ∷ q} (cons a≈b p≈q)
    = B.+-cong (S.IsRelHomomorphism.cong (RingHomomorphism.isRelHomomorphism f) a≈b)
      (B.*-congˡ (eval-p-cong p≈q))


  eval-cong : P ≈ Q → eval P ≈B eval Q
  eval-cong {P = (m , p)} {Q = (n , q)} P≈Q = begin
    eval (m , p)
      ≈⟨ eval-equiv p ⟨
    eval-p p
      ≈⟨ eval-p-cong P≈Q ⟩
    eval-p q
      ≈⟨ eval-equiv q ⟩
    eval (n , q)
      ∎



  eval-p-+-homomorphic : (p : Poly m) → (q : Poly n) → eval-p (p +P q) ≈B eval-p p +B eval-p q
  eval-p-+-homomorphic [] q = begin
    eval-p ([] +P q)
      ≈⟨ eval-p-cong (+-P-identityˡ {m = 0} q) ⟩
    eval-p q
      ≈⟨ B.+-identityˡ (eval-p q) ⟨
    eval-p [] +B eval-p q
      ∎
  eval-p-+-homomorphic (a ∷ p) [] = B.sym (B.+-identityʳ (eval-p (a ∷ p)))
  eval-p-+-homomorphic (a ∷ p) (b ∷ q) = begin
    eval-p ((a ∷ p) +P (b ∷ q))
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-p-+-homomorphic p q)) ⟩
    ⟦ a +A b ⟧ +B (β *B (eval-p p +B eval-p q))
      ≈⟨ B.+-congˡ (proj₁ distrib β (eval-p p) (eval-p q)) ⟩
    ⟦ a +A b ⟧ +B (β *B eval-p p +B β *B eval-p q)
      ≈⟨ B.+-congʳ (IsMagmaHomomorphism.homo (RingHomomorphism.+-isMagmaHomomorphism f) a b) ⟩
    ⟦ a ⟧ +B ⟦ b ⟧ +B (β *B eval-p p +B β *B eval-p q) 
      ≈⟨ B.+-assoc (⟦ a ⟧ +B ⟦ b ⟧) (β *B eval-p p) (β *B eval-p q) ⟨
    ⟦ a ⟧ +B ⟦ b ⟧ +B β *B eval-p p +B β *B eval-p q
      ≈⟨ B.+-congʳ (B.+-assoc ⟦ a ⟧ ⟦ b ⟧ (β *B eval-p p)) ⟩
    ⟦ a ⟧ +B (⟦ b ⟧ +B β *B eval-p p) +B β *B eval-p q
      ≈⟨ B.+-assoc  (⟦ a ⟧) (⟦ b ⟧ +B β *B eval-p p) (β *B eval-p q) ⟩
    ⟦ a ⟧ +B ( ⟦ b ⟧ +B β *B eval-p p +B (β *B eval-p q))
      ≈⟨ B.+-congˡ (B.+-congʳ ((B.+-comm (β *B eval-p p) ⟦ b ⟧))) ⟨
    ⟦ a ⟧ +B ((β *B eval-p p) +B ⟦ b ⟧ +B (β *B eval-p q))
      ≈⟨ B.+-congˡ (B.+-assoc (β *B eval-p p) ⟦ b ⟧ (β *B eval-p q)) ⟩
    ⟦ a ⟧ +B (β *B eval-p p +B eval-p (b ∷ q))
      ≈⟨ B.+-assoc ⟦ a ⟧ (β *B eval-p p) (eval-p (b ∷ q)) ⟨ 
    ⟦ a ⟧ +B β *B eval-p p +B eval-p (b ∷ q)
      ∎



  eval-+-homomorphic : (P : Polynomial) → (Q : Polynomial) → eval (P + Q) ≈B eval P +B eval Q
  eval-+-homomorphic (m , p) (n , q) = begin
    eval ((m , p) + (n , q))
      ≈⟨ eval-equiv (p +P q) ⟨
    eval-p (p +P q)
      ≈⟨ eval-p-+-homomorphic p q ⟩
    eval-p p +B eval-p q
      ≈⟨ B.+-cong (eval-equiv p) (eval-equiv q) ⟩
    eval (m , p) +B eval (n , q)
      ∎

  eval-p-1#-homomorphic : eval-p (A1# ∷ []) ≈B 1#
  eval-p-1#-homomorphic = begin
    eval-p (A1# ∷ [])
      ≈⟨ B.+-cong (RingHomomorphism.1#-homo f) (B.zeroʳ β) ⟩
    1# +B 0#
      ≈⟨ B.+-identityʳ 1# ⟩
    1#
      ∎
  
  eval-1#-homomorphic : eval one ≈B 1#
  eval-1#-homomorphic = begin
    eval (1 , (A1# ∷ []))
      ≈⟨ eval-equiv (A1# ∷ []) ⟨
    eval-p (A1# ∷ [])
      ≈⟨ eval-p-1#-homomorphic ⟩
    1#
      ∎


  eval-p-scale : (a : A) → (p : Poly m) → eval-p (a ·P p) ≈B eval-p (a ∷ []) *B (eval-p p)
  eval-p-scale a [] = begin
    0#
      ≈⟨ B.zeroʳ (⟦ a ⟧ +B β *B 0#) ⟨
    (⟦ a ⟧ +B β *B 0#) *B 0#
    ∎
  eval-p-scale a (b ∷ p) = begin
    ⟦ a *A b ⟧ +B β *B eval-p (a ·P p)
      ≈⟨ B.+-congʳ (IsMagmaHomomorphism.homo (RingHomomorphism.*-isMagmaHomomorphism f) a b) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B eval-p (a ·P p) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-p-scale a p)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B (eval-p (a ∷ []) *B (eval-p p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-congˡ (B.zeroʳ β)))) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B ((⟦ a ⟧ +B 0#) *B (eval-p p))
       ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-identityʳ ⟦ a ⟧))) ⟩
    ⟦ a ⟧ *B ⟦ b ⟧ +B β *B ((⟦ a ⟧ *B eval-p p)) 
      ≈⟨ B.+-congˡ (B.*-assoc β ⟦ a ⟧ (eval-p p)) ⟨
    ⟦ a ⟧ *B ⟦ b ⟧ +B (β *B (⟦ a ⟧) *B (eval-p p)) 
      ≈⟨ B.+-congˡ (B.*-congʳ (B.*-comm β ⟦ a ⟧)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B (⟦ a ⟧ *B β) *B eval-p p
      ≈⟨ B.+-congˡ (B.*-assoc ⟦ a ⟧ β (eval-p p)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B ⟦ a ⟧ *B (β *B eval-p p)
      ≈⟨ proj₁ distrib  ⟦ a ⟧ ⟦ b ⟧ ( β *B eval-p p)  ⟨
    (⟦ a ⟧) *B (⟦ b ⟧ +B β *B eval-p p)
      ≈⟨ B.*-congʳ (B.+-identityʳ ⟦ a ⟧) ⟨
    (⟦ a ⟧ +B 0#) *B (⟦ b ⟧ +B β *B eval-p p) 
      ≈⟨ B.*-congʳ (B.+-congˡ (B.zeroʳ β)) ⟨
    (⟦ a ⟧ +B β *B 0#) *B (⟦ b ⟧ +B β *B eval-p p)
      ∎
      
  eval-p-shift : (p : Poly m) → eval-p (A0# ∷ p) ≈B β *B eval-p p
  eval-p-shift p = begin
    ⟦ A0# ⟧ +B β *B eval-p p
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
      (RingHomomorphism.+-monoidHomomorphism f)) ⟩
    0# +B β *B eval-p p 
      ≈⟨ B.+-identityˡ (β *B eval-p p) ⟩
    β *B eval-p p
      ∎
      

  eval-p-*-homomorphic : (p : Poly m) → (q : Poly n) → eval-p (p *P q) ≈B eval-p p *B eval-p q
  eval-p-*-homomorphic [] q = begin
    eval-p ([] *P q)
      ≈⟨ eval-p-cong (P-zeroˡ q) ⟩
    eval-p []
      ≈⟨ B.zeroˡ (eval-p q) ⟨
    eval-p [] *B eval-p q
      ∎
  eval-p-*-homomorphic (a ∷ p) [] = begin
    eval-p ((a ∷ p) *P [])
      ≈⟨ eval-p-cong (P-zeroʳ (a ∷ p)) ⟩
    eval-p []
      ≈⟨ B.zeroʳ (eval-p (a ∷ p)) ⟨
    eval-p (a ∷ p) *B eval-p []
      ∎
  eval-p-*-homomorphic {suc m} {suc n} (a ∷ p) (b ∷ q) = begin
    eval-p ((a ∷ p) *P (b ∷ q))
      ≈⟨ eval-p-cong (cast-p≈p (cast-lem (suc n) (m))) ⟩
    eval-p (a ·P (b ∷ q) +P p *P (A0# ∷ b ∷ q))  
      ≈⟨ eval-p-+-homomorphic (a ·P (b ∷ q)) (p *P (A0# ∷ b ∷ q)) ⟩
    eval-p (a ·P (b ∷ q)) +B eval-p (p *P (A0# ∷ b ∷ q)) 
      ≈⟨ B.+-congʳ (eval-p-scale a (b ∷ q)) ⟩
    (eval-p (a ∷ []) *B eval-p (b ∷ q)) +B eval-p (p *P (A0# ∷ b ∷ q))
      ≈⟨ B.+-congˡ (eval-p-*-homomorphic p (A0# ∷ b ∷ q)) ⟩
    (eval-p (a ∷ []) *B eval-p (b ∷ q)) +B (eval-p p) *B eval-p (A0# ∷ b ∷ q)
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-p-shift (b ∷ q))) ⟩
    (eval-p (a ∷ []) *B eval-p (b ∷ q)) +B (eval-p p) *B (β *B eval-p (b ∷ q))
      ≈⟨ B.+-congʳ (B.*-congʳ (B.+-congˡ (B.zeroʳ β))) ⟩
    (⟦ a ⟧ +B 0#) *B (⟦ b ⟧ +B β *B eval-p q) +B eval-p p *B (β *B (⟦ b ⟧ +B β *B eval-p q)) 
      ≈⟨ B.+-congʳ (B.*-congʳ (B.+-identityʳ ⟦ a ⟧)) ⟩
    (⟦ a ⟧  *B (⟦ b ⟧ +B β *B eval-p q) +B  eval-p p *B (β *B (⟦ b ⟧ +B β *B eval-p q)))
      ≈⟨ B.+-congˡ (B.*-assoc (eval-p p) β (⟦ b ⟧ +B β *B eval-p q)) ⟨
    (⟦ a ⟧ *B (⟦ b ⟧ +B β *B eval-p q) +B (eval-p p *B β) *B (⟦ b ⟧ +B β *B eval-p q))
      ≈⟨ B.+-congˡ (B.*-congʳ (B.*-comm (eval-p p) β)) ⟩
    (⟦ a ⟧ *B (⟦ b ⟧ +B β *B eval-p q) +B (β *B eval-p p) *B (⟦ b ⟧ +B β *B eval-p q))
      ≈⟨ proj₂ distrib (⟦ b ⟧ +B β *B eval-p q) ⟦ a ⟧ (β *B eval-p p) ⟨
    (⟦ a ⟧ +B β *B eval-p p) *B (⟦ b ⟧ +B β *B eval-p q)
      ∎

  eval-*-homomorphic : (P : Polynomial) → (Q : Polynomial) → eval (P * Q) ≈B eval P *B eval Q
  eval-*-homomorphic (m , p) (n , q) = begin
    eval ((m , p) * (n , q))
      ≈⟨ eval-equiv ((p *P q)) ⟨
    eval-p (p *P q)
      ≈⟨ eval-p-*-homomorphic p q ⟩
     (eval-p p *B eval-p q)
      ≈⟨ B.*-cong (eval-equiv p) (eval-equiv q) ⟩
    eval (m , p) *B eval (n , q)
      ∎
 
  eval-p-inverse-homomorphic : (p : Poly m) → eval-p (-P p) ≈B -B (eval-p p)
  eval-p-inverse-homomorphic [] = B.sym (ε⁻¹≈ε B.+-group)
  eval-p-inverse-homomorphic (a ∷ p) = begin
    eval-p (-P (a ∷ p))
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-p-inverse-homomorphic p)) ⟩
    ⟦ -A a ⟧ +B β *B (-B (eval-p p))
      ≈⟨ B.+-congˡ step1 ⟩
    ⟦ -A a ⟧ +B -B (β *B eval-p p)
      ≈⟨ B.+-congʳ (RingHomomorphism.-‿homo f a) ⟩
    -B ⟦ a ⟧ +B -B (β *B eval-p p)
      ≈⟨ B.+-comm (-B (β *B eval-p p)) (-B ⟦ a ⟧) ⟨
    -B (β *B eval-p p) +B -B ⟦ a ⟧
      ≈⟨ ⁻¹-anti-homo-∙ B.+-group ⟦ a ⟧ (β *B eval-p p) ⟨
    -B eval-p (a ∷ p)
      ∎
        where
          step1 = begin
            β *B -B eval-p p
              ≈⟨ B.*-congˡ (-1*x≈-x B.ring (eval-p p)) ⟨
            β *B (-B 1# *B eval-p p)
              ≈⟨ B.*-assoc β (-B 1#) (eval-p p) ⟨
            (β *B -B 1#) *B eval-p p
              ≈⟨ B.*-congʳ (B.*-comm (-B 1#) β) ⟨
            (-B 1# *B β) *B eval-p p
              ≈⟨ B.*-assoc (-B 1#) β (eval-p p) ⟩
            (-B 1#) *B (β *B eval-p p) 
              ≈⟨ -1*x≈-x B.ring (β *B eval-p p) ⟩
            -B (β *B eval-p p)
              ∎




  eval-inverse-homomorphic : (P : Polynomial) → eval (- P) ≈B -B (eval P)
  eval-inverse-homomorphic (m , p) = begin
    eval (- (m , p))
      ≈⟨ eval-equiv (-P p) ⟨
    eval-p (-P p)
      ≈⟨ eval-p-inverse-homomorphic p ⟩
    -B eval-p p
      ≈⟨ B.-‿cong (eval-equiv p) ⟩
    -B eval (m , p)
      ∎

  eval-+-isMagmaHomomorphism : IsMagmaHomomorphism (CommutativeRing.+-rawMagma +-*-commutativeRing)
                               (CommutativeRing.+-rawMagma B) eval
  eval-+-isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = eval-cong }
    ; homo =  eval-+-homomorphic
    }

  eval-+-isMonoidHomomorphism : IsMonoidHomomorphism (CommutativeRing.+-rawMonoid +-*-commutativeRing)
                                (CommutativeRing.+-rawMonoid B) eval
  eval-+-isMonoidHomomorphism = record
    { isMagmaHomomorphism =  eval-+-isMagmaHomomorphism
    ; ε-homo = B.refl
    }

  eval-isNearSemiringHomomorphism : IsNearSemiringHomomorphism (SemiringWithoutAnnihilatingZero.rawNearSemiring
                                    (Semiring.semiringWithoutAnnihilatingZero (CommutativeRing.semiring +-*-commutativeRing)))
                                    (SemiringWithoutAnnihilatingZero.rawNearSemiring
                                    (Semiring.semiringWithoutAnnihilatingZero (CommutativeRing.semiring B))) eval
  eval-isNearSemiringHomomorphism = record
    { +-isMonoidHomomorphism = eval-+-isMonoidHomomorphism
    ; *-homo = eval-*-homomorphic }

  eval-isSemiringHomomorphism : IsSemiringHomomorphism (CommutativeSemiring.rawSemiring
                                (CommutativeRing.commutativeSemiring +-*-commutativeRing))
                                (CommutativeSemiring.rawSemiring (CommutativeRing.commutativeSemiring B)) eval
  eval-isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = eval-isNearSemiringHomomorphism
    ; 1#-homo = eval-1#-homomorphic }

  eval-isRingHomomorphism : IsRingHomomorphism (CommutativeRing.rawRing +-*-commutativeRing) (CommutativeRing.rawRing B) eval
  eval-isRingHomomorphism = record
    { isSemiringHomomorphism = eval-isSemiringHomomorphism
    ; -‿homo = eval-inverse-homomorphic
    }


            

{-
  eval-cong : P ≈ Q → eval P ≈B eval Q
  eval-cong {P = 0 , []} {Q = ℕ.zero , []} P≈Q = B.refl
  eval-cong {P = suc n , (a ∷ p)} {Q = ℕ.zero , []} P≈Q = begin
    eval (suc n , (a ∷ p))
      ≈⟨ B.+-congʳ (S.IsRelHomomorphism.cong
         (RingHomomorphism.isRelHomomorphism f) (head (≈0⇒IsZero P≈Q)))  ⟩
    ⟦ A0# ⟧ +B β *B eval (n , p)
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-cong {P = n , p} {Q = ℕ.zero , []}
         (IsZero⇒≈0 (tail (≈0⇒IsZero P≈Q))))) ⟩
    ⟦ A0# ⟧ +B β *B eval(ℕ.zero , [])
      ≈⟨ B.+-congʳ (MonoidHomomorphism.ε-homo
      (RingHomomorphism.+-monoidHomomorphism f)) ⟩
    (0# +B β *B eval(ℕ.zero , []))
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟩
    (0# +B 0#)
      ≈⟨ B.+-identityʳ 0# ⟩
    eval (ℕ.zero , [])
      ∎
  eval-cong {P = ℕ.zero , []} {Q = suc n , (a ∷ q)} P≈Q = begin
    eval (ℕ.zero , [])
      ≈⟨ B.zeroʳ β ⟨
    β *B eval (ℕ.zero , [])
      ≈⟨ B.+-identityˡ (β *B eval (ℕ.zero , [])) ⟨
    0#  +B β *B eval (ℕ.zero , [])
      ≈⟨ B.+-congʳ ( (MonoidHomomorphism.ε-homo
         (RingHomomorphism.+-monoidHomomorphism f))) ⟨
    ⟦ A0# ⟧ +B β *B eval (ℕ.zero , [])
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-cong {P = 0 , []} {Q = n , q}
         (P-sym (IsZero⇒≈0 (tail (≈0⇒IsZero (P-sym P≈Q))))))) ⟩
    ⟦ A0# ⟧ +B β *B eval (n , q)
      ≈⟨ B.+-congʳ ((S.IsRelHomomorphism.cong (RingHomomorphism.isRelHomomorphism f)
         (head (≈0⇒IsZero (P-sym P≈Q))))) ⟨
    eval (suc n , (a ∷ q))
      ∎
  eval-cong {P = suc m , (a ∷ p)} {Q = suc n , (b ∷ q)} (cons a≈b p≈q)
     = B.+-cong (S.IsRelHomomorphism.cong (RingHomomorphism.isRelHomomorphism f) a≈b)
      (B.*-congˡ (eval-cong p≈q))
 -}
      

{-eval-+-homomorphic (0 , []) (n , q) = begin
    eval ((ℕ.zero , []) + (n , q))
      ≈⟨ eval-cong (P.+-identityˡ ((n , q))) ⟩
    eval (n , q)
      ≈⟨ B.+-identityˡ (eval (n , q)) ⟨
    eval (ℕ.zero , []) +B eval (n , q)
      ∎
  eval-+-homomorphic (suc m , (a ∷ p)) (0 , []) = B.sym (B.+-identityʳ (eval (suc m , (a ∷ p))))
  eval-+-homomorphic (suc m , (a ∷ p)) (suc n , (b ∷ q)) = begin
    eval ((suc m , (a ∷ p)) + (suc n , (b ∷ q)))
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-+-homomorphic (m , p) (n , q))) ⟩
    ⟦ a +A b ⟧ +B (β *B (eval (m , p) +B eval (n , q)))
      ≈⟨ B.+-congˡ (proj₁ distrib β (eval (m , p)) (eval (n , q))) ⟩
    ⟦ a +A b ⟧ +B (β *B eval (m , p) +B β *B eval (n , q))
      ≈⟨ B.+-congʳ (IsMagmaHomomorphism.homo (RingHomomorphism.+-isMagmaHomomorphism f) a b) ⟩
    ⟦ a ⟧ +B ⟦ b ⟧ +B (β *B eval (m , p) +B β *B eval (n , q))
      ≈⟨ B.+-assoc ( ⟦ a ⟧ +B ⟦ b ⟧) (β *B eval (m , p)) (β *B eval (n , q)) ⟨
    ⟦ a ⟧ +B ⟦ b ⟧  +B β *B eval (m , p) +B β *B eval (n , q)
      ≈⟨ B.+-congʳ (B.+-assoc ⟦ a ⟧ ⟦ b ⟧ (β *B eval (m , p))) ⟩
    ⟦ a ⟧ +B (⟦ b ⟧ +B β *B eval (m , p)) +B β *B eval (n , q)
      ≈⟨ (B.+-assoc  (⟦ a ⟧) (⟦ b ⟧ +B β *B eval (m , p)) (β *B eval (n , q))) ⟩
    ⟦ a ⟧ +B ( ⟦ b ⟧ +B β *B eval (m , p) +B (β *B eval (n , q)))
      ≈⟨ B.+-congˡ (B.+-congʳ ((B.+-comm (β *B eval (m , p)) ⟦ b ⟧))) ⟨
    ⟦ a ⟧ +B ((β *B eval (m , p)) +B ⟦ b ⟧ +B (β *B eval (n , q)))
      ≈⟨ B.+-congˡ (B.+-assoc (β *B eval (m , p)) ⟦ b ⟧ (β *B eval (n , q))) ⟩
    ⟦ a ⟧ +B (β *B eval (m , p) +B eval (suc n , (b ∷ q)))
      ≈⟨ B.+-assoc ⟦ a ⟧ (β *B eval (m , p)) (eval (suc n , (b ∷ q))) ⟨
    eval (suc m , (a ∷ p)) +B eval (suc n , (b ∷ q))
      ∎
 -}



{- eval-1#-homomorphic = begin
    eval (1 , (A1# ∷ []))
      ≈⟨ B.+-cong (RingHomomorphism.1#-homo f) (B.zeroʳ β)  ⟩
    1# +B 0#
      ≈⟨ B.+-identityʳ (1#) ⟩
    1#
      ∎

-}


{-eval-inverse-homomorphic (0 , []) = B.sym (ε⁻¹≈ε B.+-group)
  eval-inverse-homomorphic (suc m , (a ∷ p)) = begin
    eval (- (suc m , (a ∷ p)))
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-inverse-homomorphic (m , p))) ⟩
    ⟦ -A a ⟧ +B β *B (-B (eval (m , p)))
      ≈⟨ B.+-congˡ step1 ⟩
    ⟦ -A a ⟧ +B -B (β *B eval (m , p))
      ≈⟨ B.+-congʳ (RingHomomorphism.-‿homo f a) ⟩
    -B ⟦ a ⟧ +B -B (β *B eval (m , p))
       ≈⟨ B.+-comm (-B (β *B eval (m , p))) (-B ⟦ a ⟧) ⟨
    -B (β *B eval (m , p)) +B (-B ⟦ a ⟧)
       ≈⟨ ⁻¹-anti-homo-∙ B.+-group ⟦ a ⟧ (β *B eval (m , p)) ⟨
    (-B eval (suc m , (a ∷ p)))
    ∎
      where
        step1 = begin
          β *B (-B (eval (m , p)))
            ≈⟨ B.*-congˡ (-1*x≈-x B.ring (eval (m , p))) ⟨
          β *B (-B 1# *B eval (m , p))
            ≈⟨ B.*-assoc β (-B 1#) (eval (m , p)) ⟨
          (β *B -B 1#) *B eval (m , p)
            ≈⟨ B.*-congʳ (B.*-comm (-B 1#) β) ⟨
          (-B 1# *B β) *B eval (m , p)
            ≈⟨ B.*-assoc (-B 1#) β (eval (m , p)) ⟩
          (-B 1#) *B (β *B eval (m , p)) 
            ≈⟨ -1*x≈-x B.ring (β *B eval (m , p)) ⟩
          -B (β *B eval (m , p))
            ∎
           -}
