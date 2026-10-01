-- Polynomial Morphisms
-- open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Bundles
  renaming (CommutativeRing to CR)
  
module Algebra.Polynomial.Morphism.Morphism
  {ℓ₁ ℓ₂}
  (R : CR ℓ₁ ℓ₂)
  where

import Algebra.Definitions as Def
open import Algebra.Morphism.Bundles
  renaming (RingHomomorphism to RingHomo; MonoidHomomorphism to MonHomo)
open import Algebra.Morphism.Structures
  renaming (IsRingHomomorphism to IsRingHomo; IsMagmaHomomorphism to IsMagmaHomo)
open import Algebra.Polynomial.Poly.Base.CommutativeRing R
  using (Poly; []≈ ; ≈[]; cons ;  consˡ ; consʳ; IsZero⇒p≈[];
         p≈[]⇒IsZero;  a·p≈a∷[]*p ; *-distrib-shift; shiftp≈x*p)
  renaming ( refl to P-refl ; sym to P-sym ; _·_ to _·P_
           ; _+_ to _+P_ ; _*_ to _*P_; _≈_ to _≈P_; -_ to -P_)
open import Algebra.Polynomial.Poly.Properties.CommutativeRing R as P
  using (+-*-commutativeRing; *-zeroˡ ; *-zeroʳ)
  renaming ( rawRing to PolyrawRing; *-comm to P*-comm
           ; +-identityˡ to +-P-identityˡ ; +-identityʳ to +-P-identityʳ
           ; zeroˡ to P-zeroˡ; zeroʳ to P-zeroʳ)
open import Algebra.Properties.Group
open import Algebra.Properties.Ring using (-‿distribʳ-*)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All
import Level as L
import Relation.Binary.Morphism.Structures as S
  renaming (IsRelHomomorphism to IsRelHomo)

open RingHomo
   renaming ( +-isMagmaHomomorphism to +-isMagmaHomo
            ; +-monoidHomomorphism to +-monoidHom
            ; isRelHomomorphism to isRelHomo
            ; *-isMagmaHomomorphism to *-isMagmaHomo)
   hiding  (⟦_⟧)
  
module A = CR R
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
    a b : A
    p : Poly
    q : Poly

module PolynomialRingMorphism
  {ℓ₃ ℓ₄}
  (B : CR ℓ₃ ℓ₄)
  (f : RingHomo {ℓ₁} {ℓ₂} (CR.rawRing R) (CR.rawRing B))
  where

  module B = CR B 
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
  open RingHomo f using (⟦_⟧)
 
  open Def {A = B.Carrier} (_≈B_)

-- evaluate the polynomial given an element β ∈ B
  eval : CR.Carrier B → Poly → CR.Carrier B
  eval β [] = 0#
  eval β (a ∷ p) = ⟦ a ⟧ +B (β *B eval β p)

  eval-equiv : (β : CR.Carrier B) → (p : Poly) → eval β p ≈B (eval β p)
  eval-equiv β [] = B.refl
  eval-equiv β (a ∷ p) = B.+-congˡ (B.*-congˡ (eval-equiv β p))

  eval-cong : ∀ {p : Poly} → ∀ {q : Poly} → (β : CR.Carrier B)
                → p ≈P q → (eval β p) ≈B (eval β q)
  eval-cong {p = []} {q = []} β p≈q  = B.refl
  eval-cong {p = []} {q = b ∷ q} β p≈q  = begin
    eval β []
      ≈⟨ B.zeroʳ β ⟨
    β *B 0#
      ≈⟨ B.+-identityˡ (β *B eval β []) ⟨
    0# +B β *B eval β []
      ≈⟨ B.+-congʳ (MonHomo.ε-homo (+-monoidHom f)) ⟨
    ⟦ A0# ⟧ +B β *B eval β []
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-cong {p = []} {q = q} β
         (P-sym (IsZero⇒p≈[] (tail (p≈[]⇒IsZero (P-sym p≈q))))))) ⟩
    ⟦ A0# ⟧ +B β *B eval β q
      ≈⟨ B.+-congʳ (S.IsRelHomo.cong
         (isRelHomo f) (head (p≈[]⇒IsZero (P-sym p≈q)))) ⟨
    eval β (b ∷ q)
      ∎
  eval-cong {p = a ∷ p} {[]} β p≈q  = begin
    eval β (a ∷ p)
      ≈⟨ B.+-congʳ (S.IsRelHomo.cong
         (isRelHomo f) (head (p≈[]⇒IsZero p≈q))) ⟩
    ⟦ A0# ⟧ +B β *B eval β p
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-cong {p = p} {q = []} β
         (IsZero⇒p≈[] (tail (p≈[]⇒IsZero p≈q))) )) ⟩
    ⟦ A0# ⟧ +B β *B eval β []
      ≈⟨ B.+-congʳ (MonHomo.ε-homo(+-monoidHom f)) ⟩
    0# +B β *B eval β []
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟩
    0# +B 0#
      ≈⟨ B.+-identityʳ 0# ⟩
    eval  β []
      ∎
  eval-cong {p = a ∷ p} {b ∷ q} β (cons a≈b p≈q) 
    = B.+-cong (S.IsRelHomo.cong (isRelHomo f) a≈b)
      (B.*-congˡ (eval-cong β p≈q ))

  eval-+-homomorphic : (β : CR.Carrier B) → (p : Poly) → (q : Poly) →
                            eval β (p +P q) ≈B eval β p +B eval β q
  eval-+-homomorphic β [] q = begin
    eval β ([] +P q) 
      ≈⟨ eval-cong β (+-P-identityˡ q)  ⟩
    eval β q
      ≈⟨ B.+-identityˡ (eval β q) ⟨
    eval β [] +B eval β q
      ∎
  eval-+-homomorphic β (a ∷ p) [] = B.sym (B.+-identityʳ (eval β (a ∷ p)))
  eval-+-homomorphic β (a ∷ p) (b ∷ q) = begin
    eval β ((a ∷ p) +P (b ∷ q)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-+-homomorphic β p q)) ⟩
    ⟦ a +A b ⟧ +B (β *B (eval β p +B eval β q))
      ≈⟨ B.+-congˡ (proj₁ distrib β (eval β p) (eval β q)) ⟩
    ⟦ a +A b ⟧ +B (β *B eval β p +B β *B eval β q)
      ≈⟨ B.+-congʳ (IsMagmaHomo.homo (+-isMagmaHomo f) a b) ⟩
    ⟦ a ⟧ +B ⟦ b ⟧ +B (β *B eval β p +B β *B eval β q) 
      ≈⟨ B.+-assoc (⟦ a ⟧ +B ⟦ b ⟧) (β *B eval β p) (β *B eval β q) ⟨
    ⟦ a ⟧ +B ⟦ b ⟧ +B β *B eval β p +B β *B eval β q
      ≈⟨ B.+-congʳ (B.+-assoc ⟦ a ⟧ ⟦ b ⟧ (β *B eval β p)) ⟩
    ⟦ a ⟧ +B (⟦ b ⟧ +B β *B eval β p) +B β *B eval β q
      ≈⟨ B.+-assoc  (⟦ a ⟧) (⟦ b ⟧ +B β *B eval β p) (β *B eval β q) ⟩
    ⟦ a ⟧ +B ( ⟦ b ⟧ +B β *B eval β p +B (β *B eval β q))
      ≈⟨ B.+-congˡ (B.+-congʳ ((B.+-comm (β *B eval β p) ⟦ b ⟧))) ⟨
    ⟦ a ⟧ +B ((β *B eval β p) +B ⟦ b ⟧ +B (β *B eval β q))
      ≈⟨ B.+-congˡ (B.+-assoc (β *B eval β p) ⟦ b ⟧ (β *B eval β q)) ⟩
    ⟦ a ⟧ +B (β *B eval β p +B eval β (b ∷ q))
      ≈⟨ B.+-assoc ⟦ a ⟧ (β *B eval β p) (eval β (b ∷ q)) ⟨ 
    ⟦ a ⟧ +B β *B eval β p +B eval β (b ∷ q)
      ∎

  eval-1#-homomorphic : (β : CR.Carrier B) → eval β (A1# ∷ []) ≈B 1#
  eval-1#-homomorphic β = begin
    eval β (A1# ∷ [])  ≈⟨ B.+-cong (RingHomo.1#-homo f) (B.zeroʳ β) ⟩
    1# +B 0#           ≈⟨ B.+-identityʳ 1# ⟩
    1#                 ∎
  
  eval-scale :  (β : CR.Carrier B) → (a : A) → (p : Poly) →
                   eval β (a ·P p) ≈B eval β (a ∷ []) *B (eval β p) 
  eval-scale β a [] = begin
    0#  ≈⟨ B.zeroʳ (⟦ a ⟧ +B β *B 0#) ⟨
    (⟦ a ⟧ +B β *B 0#) *B 0#  ∎
  eval-scale β a (b ∷ p) = begin
    ⟦ a *A b ⟧ +B β *B eval β (a ·P p) 
      ≈⟨ B.+-congʳ (IsMagmaHomo.homo (*-isMagmaHomo f) a b) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B eval β (a ·P p)  
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-scale β a p)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B (eval β (a ∷ []) *B (eval β p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-congˡ (B.zeroʳ β)))) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B β *B ((⟦ a ⟧ +B 0#) *B (eval β p))
       ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-identityʳ ⟦ a ⟧))) ⟩
    ⟦ a ⟧ *B ⟦ b ⟧ +B β *B ((⟦ a ⟧ *B eval β p)) 
      ≈⟨ B.+-congˡ (B.*-assoc β ⟦ a ⟧ (eval β p)) ⟨
    ⟦ a ⟧ *B ⟦ b ⟧ +B (β *B (⟦ a ⟧) *B (eval β p)) 
      ≈⟨ B.+-congˡ (B.*-congʳ (B.*-comm β ⟦ a ⟧)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B (⟦ a ⟧ *B β) *B eval β p
      ≈⟨ B.+-congˡ (B.*-assoc ⟦ a ⟧ β (eval β p)) ⟩
    (⟦ a ⟧ *B ⟦ b ⟧) +B ⟦ a ⟧ *B (β *B eval β p)
      ≈⟨ proj₁ distrib  ⟦ a ⟧ ⟦ b ⟧ ( β *B eval β p)  ⟨
    (⟦ a ⟧) *B (⟦ b ⟧ +B β *B eval β p)
      ≈⟨ B.*-congʳ (B.+-identityʳ ⟦ a ⟧) ⟨
    (⟦ a ⟧ +B 0#) *B (⟦ b ⟧ +B β *B eval β p) 
      ≈⟨ B.*-congʳ (B.+-congˡ (B.zeroʳ β)) ⟨
    (⟦ a ⟧ +B β *B 0#) *B (⟦ b ⟧ +B β *B eval β p)
      ∎

  eval-shift : (β : CR.Carrier B) → (p : Poly) → eval β (shift p) ≈B β *B eval β p
  eval-shift β p = begin
    ⟦ A0# ⟧ +B β *B eval β p
      ≈⟨ B.+-congʳ (MonHomo.ε-homo (+-monoidHom f)) ⟩
    0# +B β *B eval β p 
      ≈⟨ B.+-identityˡ (β *B eval β p) ⟩
    β *B eval β p
      ∎

  eval-*-homomorphic : (β : CR.Carrier B) → (p q : Poly)
                          → eval β (p *P q) ≈B eval β p *B eval β q
  eval-*-homomorphic β [] q = begin
    eval β ([] *P q)  ≈⟨ eval-cong β (P-zeroˡ q) ⟩
    eval β []  ≈⟨ B.zeroˡ (eval β q) ⟨
    eval β [] *B eval β q  ∎
  eval-*-homomorphic β (a ∷ p) q = begin
    eval β ((a ∷ p) *P q)
      ≈⟨ eval-cong {p = (a ∷ p) *P q} β P-refl ⟩
    eval β (a ·P q +P p *P (A0# ∷ q))
      ≈⟨ eval-+-homomorphic β (a ·P q) (p *P (A0# ∷ q)) ⟩
    eval β (a ·P q) +B eval β (p *P (A0# ∷ q))
      ≈⟨ B.+-cong (eval-scale β a q) (eval-*-homomorphic β p (A0# ∷ q)) ⟩
    ((eval β (a ∷ []) *B eval β q) +B (eval β p *B eval β (A0# ∷ q)))
       ≈⟨ B.+-congˡ (B.*-congˡ (eval-shift β q)) ⟩
    (eval β (a ∷ []) *B eval β q) +B (eval β p *B (β *B eval β q))
      ≈⟨ B.+-congˡ step ⟩
    (eval β (a ∷ []) *B eval β q) +B ((β *B eval β p) *B eval β q)
      ≈⟨ proj₂ distrib (eval β q) (eval β (a ∷ [])) (β *B eval β p) ⟨
    ((eval β (a ∷ []) +B β *B eval β p) *B eval β q)
      ≈⟨ B.*-congʳ ((B.+-congʳ (B.trans (B.+-congˡ
         (B.zeroʳ β)) (B.+-identityʳ ⟦ a ⟧)))) ⟩
    (eval β (a ∷ p) *B eval β q)
      ∎
      where
      step : eval β p *B (β *B eval β q) ≈B (β *B eval β p) *B eval β q
      step = begin
        eval β p *B (β *B eval β q)
          ≈⟨ B.*-assoc (eval β p) β (eval β q) ⟨
        (eval β p *B β) *B eval β q
          ≈⟨ B.*-congʳ (B.*-comm (eval β p) β) ⟩
        (β *B eval β p) *B eval β q
          ∎
    
  eval-inverse-homomorphic : (β : CR.Carrier B) → (p : Poly) →
                                  eval β (-P p) ≈B -B (eval β p)
  eval-inverse-homomorphic β [] = B.sym (ε⁻¹≈ε B.+-group)
  eval-inverse-homomorphic β (a ∷ p) = begin
    eval β (-P (a ∷ p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-inverse-homomorphic β p)) ⟩
    ⟦ -A a ⟧ +B β *B (-B (eval β p))
      ≈⟨ B.+-congˡ (-‿distribʳ-* (CR.ring B) β (eval β p)) ⟨
    ⟦ -A a ⟧ +B -B (β *B eval β p)
      ≈⟨ B.+-congʳ (RingHomo.-‿homo f a) ⟩
    -B ⟦ a ⟧ +B -B (β *B eval β p)
      ≈⟨ B.+-comm (-B (β *B eval β p)) (-B ⟦ a ⟧) ⟨
    -B (β *B eval β p) +B -B ⟦ a ⟧
      ≈⟨ ⁻¹-anti-homo-∙ B.+-group ⟦ a ⟧ (β *B eval β p) ⟨
    -B eval β (a ∷ p)
      ∎

  eval-isRingHomomorphism : (β : CR.Carrier B) → IsRingHomo
    (CR.rawRing +-*-commutativeRing) (CR.rawRing B) (eval β)
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

  x-mapsto-β : (β : CR.Carrier B) → eval β  (A0# ∷ A1# ∷ []) ≈B β
  x-mapsto-β β = begin
    ⟦ A0# ⟧ +B β *B (⟦ A1# ⟧ +B β *B 0#)
      ≈⟨ B.+-congʳ (MonHomo.ε-homo (+-monoidHom f)) ⟩
    0# +B (β *B (⟦ A1# ⟧ +B β *B 0#))
      ≈⟨ B.+-identityˡ (β *B (⟦ A1# ⟧ +B β *B 0#))⟩
    β *B (⟦ A1# ⟧ +B β *B 0#)
      ≈⟨ B.*-congˡ (B.+-cong (RingHomo.1#-homo f) (B.zeroʳ β)) ⟩
    β *B (1# +B 0#)
      ≈⟨ B.*-congˡ (B.+-identityʳ 1#) ⟩
    β *B 1#
      ≈⟨ B.*-identityʳ β ⟩
    β
      ∎

-- define a canonical inclusion homomorphism from R to R[x])
  ı : A.Carrier → Poly
  ı r = r ∷ []

  eval-comm : (β : CR.Carrier B) → ∀ (r : A.Carrier) → ⟦ r ⟧ ≈B eval β (ı r)
  eval-comm β r = begin
    ⟦ r ⟧
      ≈⟨ B.+-identityʳ ⟦ r ⟧ ⟨
    ⟦ r ⟧ +B 0#
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟨
    eval β (r ∷ [])
      ∎
 
  eval-unique : (β : CR.Carrier B) →
                ∀ (ϕ : RingHomo {ℓ₁} {ℓ₁ L.⊔ ℓ₂} (PolyrawRing) (CR.rawRing B)) →
                (∀ (r : A.Carrier) → RingHomo.⟦ ϕ ⟧ (ı r) ≈B (⟦ r ⟧)) →
                RingHomo.⟦ ϕ ⟧ (A0# ∷ A1# ∷ []) ≈B β →
                ∀ (p : Poly) → RingHomo.⟦ ϕ ⟧ p ≈B eval β p
  eval-unique β ϕ  _ _ [] = MonHomo.ε-homo (+-monoidHom ϕ)
  eval-unique β ϕ ϕ-comm x-mapsto-β (a ∷ p)  = begin
    RingHomo.⟦ ϕ ⟧ (a ∷ p)
      ≈⟨ S.IsRelHomo.cong (isRelHomo ϕ)
         (cons ((A.+-identityʳ a)) (P.+-identityˡ p)) ⟨
    RingHomo.⟦ ϕ ⟧ ((a ∷ []) +P (A0# ∷ p))
      ≈⟨ IsMagmaHomo.homo (+-isMagmaHomo ϕ)
         (a ∷ [])  (A0# ∷ p) ⟩
    RingHomo.⟦ ϕ ⟧ (a ∷ []) +B RingHomo.⟦ ϕ ⟧  (A0# ∷ p)
      ≈⟨ B.+-congˡ (S.IsRelHomo.cong (isRelHomo ϕ) (shiftp≈x*p p)) ⟩
    RingHomo.⟦ ϕ ⟧  (a ∷ []) +B RingHomo.⟦ ϕ ⟧ ((A0# ∷ A1# ∷ []) *P  p)
      ≈⟨ B.+-congˡ (IsMagmaHomo.homo (*-isMagmaHomo ϕ)
         (A0# ∷ A1# ∷ []) p) ⟩
    RingHomo.⟦ ϕ ⟧  (a ∷ []) +B RingHomo.⟦ ϕ ⟧
               (A0# ∷ A1# ∷ []) *B (RingHomo.⟦ ϕ ⟧ p)
      ≈⟨ B.+-congˡ (B.*-cong x-mapsto-β
        (eval-unique β ϕ ϕ-comm x-mapsto-β p)) ⟩
    RingHomo.⟦ ϕ ⟧ (ı a) +B β *B eval β p
      ≈⟨ B.+-congʳ (ϕ-comm a) ⟩
    eval β (a ∷ p)
     ∎

