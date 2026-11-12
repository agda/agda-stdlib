open import Algebra.Bundles

module Algebra.Polynomial.Morphism.Morphism
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where
  
import Algebra.Definitions as Def
open import Algebra.Morphism.Bundles
  renaming (RingHomomorphism to RingHomo; MonoidHomomorphism to MonHomo)
open import Algebra.Morphism.Structures
  renaming (IsRingHomomorphism to IsRingHomo; IsMagmaHomomorphism to IsMagmaHomo)
open import Algebra.Polynomial.Poly.Properties.CommutativeRing R as P
  using ( Poly; []≈; ≈[]; cons; shift; IsZero⇒p≈[]
        ; inject; p≈[]⇒IsZero; a·p≈a∷[]*p; shiftp≈x*p; 0#; 1#) 
open import Algebra.Properties.Group
open import Algebra.Properties.Ring
open CommutativeRing using (rawRing)
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
  
module A = CommutativeRing R
open A
  using ()
  renaming (Carrier to A)
  
private
  variable
    a b : A
    p q : Poly

module PolynomialRingMorphism
  {ℓ₃ ℓ₄}
  (CR : CommutativeRing ℓ₃ ℓ₄)
  (f : RingHomo {ℓ₁} {ℓ₂} (rawRing R) (rawRing CR))
  where

  module B = CommutativeRing CR 
  open B
    using ()
    renaming (Carrier to B)

  open import Relation.Binary.Reasoning.Setoid B.setoid
  open RingHomo f using (⟦_⟧)
  open Def {A = B.Carrier} (B._≈_)

-- evaluate the polynomial given an element β ∈ B
  eval : B → Poly → B
  eval β [] = B.0#
  eval β (a ∷ p) = ⟦ a ⟧ B.+ (β B.* eval β p)

  eval-cong : ∀ {p q : Poly} → (β : B)
                → p P.≈ q → (eval β p) B.≈ (eval β q)
  eval-cong {p = []} {q = []} β p≈q  = B.refl
  eval-cong {p = []} {q = b ∷ q} β p≈q  = begin
    eval β []
      ≈⟨ B.zeroʳ β ⟨
    β B.* B.0#
      ≈⟨ B.+-identityˡ (β B.* eval β []) ⟨
    B.0# B.+ β B.* eval β []
      ≈⟨ B.+-congʳ (MonHomo.ε-homo (+-monoidHom f)) ⟨
    ⟦ A.0# ⟧ B.+ β B.* eval β []
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-cong {p = []} {q = q} β
         (P.sym (IsZero⇒p≈[] (tail (p≈[]⇒IsZero (P.sym p≈q))))))) ⟩
    ⟦ A.0# ⟧ B.+ β B.* eval β q
      ≈⟨ B.+-congʳ (S.IsRelHomo.cong
         (isRelHomo f) (head (p≈[]⇒IsZero (P.sym p≈q)))) ⟨
    eval β (b ∷ q)
      ∎
  eval-cong {p = a ∷ p} {[]} β p≈q  = begin
    eval β (a ∷ p)
      ≈⟨ B.+-congʳ (S.IsRelHomo.cong
         (isRelHomo f) (head (p≈[]⇒IsZero p≈q))) ⟩
    ⟦ A.0# ⟧ B.+ β B.* eval β p
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-cong {p = p} {q = []} β
         (IsZero⇒p≈[] (tail (p≈[]⇒IsZero p≈q))) )) ⟩
    ⟦ A.0# ⟧ B.+ β B.* eval β []
      ≈⟨ B.+-congʳ (MonHomo.ε-homo(+-monoidHom f)) ⟩
    B.0# B.+ β B.* eval β []
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟩
    B.0# B.+ B.0#
      ≈⟨ B.+-identityʳ B.0# ⟩
    eval  β []
      ∎
  eval-cong {p = a ∷ p} {b ∷ q} β (cons a≈b p≈q) 
    = B.+-cong (S.IsRelHomo.cong (isRelHomo f) a≈b)
      (B.*-congˡ (eval-cong β p≈q ))

  eval-+ : (β : B) → (p : Poly) → (q : Poly) →
            eval β (p P.+ q) B.≈ eval β p B.+ eval β q
  eval-+ β [] q = begin
    eval β ([] P.+ q) 
      ≈⟨ eval-cong β (P.+-identityˡ q)  ⟩
    eval β q
      ≈⟨ B.+-identityˡ (eval β q) ⟨
    eval β [] B.+ eval β q
      ∎
  eval-+ β (a ∷ p) [] = B.sym (B.+-identityʳ (eval β (a ∷ p)))
  eval-+ β (a ∷ p) (b ∷ q) = begin
    eval β ((a ∷ p) P.+ (b ∷ q)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-+ β p q)) ⟩
    ⟦ a A.+ b ⟧ B.+ (β B.* (eval β p B.+ eval β q))
      ≈⟨ B.+-congˡ (proj₁ B.distrib β (eval β p) (eval β q)) ⟩
    ⟦ a A.+ b ⟧ B.+ (β B.* eval β p B.+ β B.* eval β q)
      ≈⟨ B.+-congʳ (IsMagmaHomo.homo (+-isMagmaHomo f) a b) ⟩
    ⟦ a ⟧ B.+ ⟦ b ⟧ B.+ (β B.* eval β p B.+ β B.* eval β q) 
      ≈⟨ B.+-assoc (⟦ a ⟧ B.+ ⟦ b ⟧) (β B.* eval β p) (β B.* eval β q) ⟨
    ⟦ a ⟧ B.+ ⟦ b ⟧ B.+ β B.* eval β p B.+ β B.* eval β q
      ≈⟨ B.+-congʳ (B.+-assoc ⟦ a ⟧ ⟦ b ⟧ (β B.* eval β p)) ⟩
    ⟦ a ⟧ B.+ (⟦ b ⟧ B.+ β B.* eval β p) B.+ β B.* eval β q
      ≈⟨ B.+-assoc  (⟦ a ⟧) (⟦ b ⟧ B.+ β B.* eval β p) (β B.* eval β q) ⟩
    ⟦ a ⟧ B.+ ( ⟦ b ⟧ B.+ β B.* eval β p B.+ (β B.* eval β q))
      ≈⟨ B.+-congˡ (B.+-congʳ ((B.+-comm (β B.* eval β p) ⟦ b ⟧))) ⟨
    ⟦ a ⟧ B.+ ((β B.* eval β p) B.+ ⟦ b ⟧ B.+ (β B.* eval β q))
      ≈⟨ B.+-congˡ (B.+-assoc (β B.* eval β p) ⟦ b ⟧ (β B.* eval β q)) ⟩
    ⟦ a ⟧ B.+ (β B.* eval β p B.+ eval β (b ∷ q))
      ≈⟨ B.+-assoc ⟦ a ⟧ (β B.* eval β p) (eval β (b ∷ q)) ⟨ 
    ⟦ a ⟧ B.+ β B.* eval β p B.+ eval β (b ∷ q)
      ∎

  eval-1# : (β : B) → eval β 1# B.≈ B.1#
  eval-1# β = begin
    eval β 1#  ≈⟨ B.+-cong (RingHomo.1#-homo f) (B.zeroʳ β) ⟩
    B.1# B.+ B.0#           ≈⟨ B.+-identityʳ B.1# ⟩
    B.1#                 ∎
  
  eval-· : (β : B) → (a : A) → (p : Poly) →
           eval β (a P.· p) B.≈ eval β (a ∷ []) B.* (eval β p) 
  eval-· β a [] = begin
    B.0#  ≈⟨ B.zeroʳ (⟦ a ⟧ B.+ β B.* B.0#) ⟨
    (⟦ a ⟧ B.+ β B.* B.0#) B.* B.0#  ∎
  eval-· β a (b ∷ p) = begin
    ⟦ a A.* b ⟧ B.+ β B.* eval β (a P.· p) 
      ≈⟨ B.+-congʳ (IsMagmaHomo.homo (*-isMagmaHomo f) a b) ⟩
    (⟦ a ⟧ B.* ⟦ b ⟧) B.+ β B.* eval β (a P.· p)  
      ≈⟨ B.+-congˡ (B.*-congˡ (eval-· β a p)) ⟩
    (⟦ a ⟧ B.* ⟦ b ⟧) B.+ β B.* (eval β (a ∷ []) B.* (eval β p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-congˡ (B.zeroʳ β)))) ⟩
    (⟦ a ⟧ B.* ⟦ b ⟧) B.+ β B.* ((⟦ a ⟧ B.+ B.0#) B.* (eval β p))
       ≈⟨ B.+-congˡ (B.*-congˡ (B.*-congʳ (B.+-identityʳ ⟦ a ⟧))) ⟩
    ⟦ a ⟧ B.* ⟦ b ⟧ B.+ β B.* ((⟦ a ⟧ B.* eval β p)) 
      ≈⟨ B.+-congˡ (B.*-assoc β ⟦ a ⟧ (eval β p)) ⟨
    ⟦ a ⟧ B.* ⟦ b ⟧ B.+ (β B.* (⟦ a ⟧) B.* (eval β p)) 
      ≈⟨ B.+-congˡ (B.*-congʳ (B.*-comm β ⟦ a ⟧)) ⟩
    (⟦ a ⟧ B.* ⟦ b ⟧) B.+ (⟦ a ⟧ B.* β) B.* eval β p
      ≈⟨ B.+-congˡ (B.*-assoc ⟦ a ⟧ β (eval β p)) ⟩
    (⟦ a ⟧ B.* ⟦ b ⟧) B.+ ⟦ a ⟧ B.* (β B.* eval β p)
      ≈⟨ proj₁ B.distrib  ⟦ a ⟧ ⟦ b ⟧ ( β B.* eval β p)  ⟨
    (⟦ a ⟧) B.* (⟦ b ⟧ B.+ β B.* eval β p)
      ≈⟨ B.*-congʳ (B.+-identityʳ ⟦ a ⟧) ⟨
    (⟦ a ⟧ B.+ B.0#) B.* (⟦ b ⟧ B.+ β B.* eval β p) 
      ≈⟨ B.*-congʳ (B.+-congˡ (B.zeroʳ β)) ⟨
    (⟦ a ⟧ B.+ β B.* B.0#) B.* (⟦ b ⟧ B.+ β B.* eval β p)
      ∎

  eval-shift : (β : B) → (p : Poly) → eval β (shift 1 p) B.≈ β B.* eval β p
  eval-shift β p = begin
    ⟦ A.0# ⟧ B.+ β B.* eval β p
      ≈⟨ B.+-congʳ (MonHomo.ε-homo (+-monoidHom f)) ⟩
    B.0# B.+ β B.* eval β p 
      ≈⟨ B.+-identityˡ (β B.* eval β p) ⟩
    β B.* eval β p
      ∎

  eval-* : (β : B) → (p q : Poly)
           → eval β (p P.* q) B.≈ eval β p B.* eval β q
  eval-* β [] q = begin
    eval β ([] P.* q)  ≈⟨ eval-cong β (P.zeroˡ q) ⟩
    eval β []  ≈⟨ B.zeroˡ (eval β q) ⟨
    eval β [] B.* eval β q  ∎
  eval-* β (a ∷ p) q = begin
    eval β ((a ∷ p) P.* q)
      ≈⟨ eval-cong {p = (a ∷ p) P.* q} β P.refl ⟩
    eval β (a P.· q P.+ p P.* (shift 1 q))
      ≈⟨ eval-+ β (a P.· q) (p P.* (shift 1 q)) ⟩
    eval β (a P.· q) B.+ eval β (p P.* (shift 1 q))
      ≈⟨ B.+-cong (eval-· β a q) (eval-* β p (shift 1 q)) ⟩
    ((eval β (a ∷ []) B.* eval β q) B.+ (eval β p B.* eval β (shift 1 q)))
       ≈⟨ B.+-congˡ (B.*-congˡ (eval-shift β q)) ⟩
    (eval β (a ∷ []) B.* eval β q) B.+ (eval β p B.* (β B.* eval β q))
      ≈⟨ B.+-congˡ step ⟩
    (eval β (a ∷ []) B.* eval β q) B.+ ((β B.* eval β p) B.* eval β q)
      ≈⟨ proj₂ B.distrib (eval β q) (eval β (a ∷ [])) (β B.* eval β p) ⟨
    ((eval β (a ∷ []) B.+ β B.* eval β p) B.* eval β q)
      ≈⟨ B.*-congʳ ((B.+-congʳ (B.trans (B.+-congˡ
         (B.zeroʳ β)) (B.+-identityʳ ⟦ a ⟧)))) ⟩
    (eval β (a ∷ p) B.* eval β q)
      ∎
      where
      step : eval β p B.* (β B.* eval β q) B.≈ (β B.* eval β p) B.* eval β q
      step = begin
        eval β p B.* (β B.* eval β q)
          ≈⟨ B.*-assoc (eval β p) β (eval β q) ⟨
        (eval β p B.* β) B.* eval β q
          ≈⟨ B.*-congʳ (B.*-comm (eval β p) β) ⟩
        (β B.* eval β p) B.* eval β q
          ∎
    
  eval‿- : (β : B) → (p : Poly) →
              eval β (P.- p) B.≈ B.- (eval β p)
  eval‿- β [] = B.sym (ε⁻¹≈ε B.+-group)
  eval‿- β (a ∷ p) = begin
    eval β (P.- (a ∷ p)) 
      ≈⟨ B.+-congˡ (B.*-congˡ (eval‿- β p)) ⟩
    ⟦ A.- a ⟧ B.+ β B.* (B.- (eval β p))
      ≈⟨ B.+-congˡ (-‿distribʳ-* (B.ring) β (eval β p)) ⟨
    ⟦ A.- a ⟧ B.+ B.- (β B.* eval β p)
      ≈⟨ B.+-congʳ (RingHomo.-‿homo f a) ⟩
    B.- ⟦ a ⟧ B.+ B.- (β B.* eval β p)
      ≈⟨ B.+-comm (B.- (β B.* eval β p)) (B.- ⟦ a ⟧) ⟨
    B.- (β B.* eval β p) B.+ B.- ⟦ a ⟧
      ≈⟨ ⁻¹-anti-homo-∙ B.+-group ⟦ a ⟧ (β B.* eval β p) ⟨
    B.- eval β (a ∷ p)
      ∎

  eval-isRingHomomorphism : (β : B) → IsRingHomo
    (CommutativeRing.rawRing P.+-*-commutativeRing) (B.rawRing) (eval β)
  eval-isRingHomomorphism β = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = eval-cong β }
            ; homo = eval-+ β
            }
          ; ε-homo = B.refl
          }
        ; *-homo = eval-* β
        }
      ; 1#-homo = eval-1# β
      }
    ; -‿homo = eval‿- β
    }

---------------- Universal Property of Polynomial Rings ----------------

  eval-id# : (β : B) → eval β  (shift 1 1#) B.≈ β
  eval-id# β = begin
    ⟦ A.0# ⟧ B.+ β B.* (⟦ A.1# ⟧ B.+ β B.* B.0#)
      ≈⟨ B.+-congʳ (MonHomo.ε-homo (+-monoidHom f)) ⟩
    B.0# B.+ (β B.* (⟦ A.1# ⟧ B.+ β B.* B.0#))
      ≈⟨ B.+-identityˡ (β B.* (⟦ A.1# ⟧ B.+ β B.* B.0#))⟩
    β B.* (⟦ A.1# ⟧ B.+ β B.* B.0#)
      ≈⟨ B.*-congˡ (B.+-cong (RingHomo.1#-homo f) (B.zeroʳ β)) ⟩
    β B.* (B.1# B.+ B.0#)
      ≈⟨ B.*-congˡ (B.+-identityʳ B.1#) ⟩
    β B.* B.1#
      ≈⟨ B.*-identityʳ β ⟩
    β
      ∎

  eval-inject : (β : B) → ∀ (r : A.Carrier) → ⟦ r ⟧ B.≈ eval β (inject r)
  eval-inject β r = begin
    ⟦ r ⟧
      ≈⟨ B.+-identityʳ ⟦ r ⟧ ⟨
    ⟦ r ⟧ B.+ B.0#
      ≈⟨ B.+-congˡ (B.zeroʳ β) ⟨
    eval β (r ∷ [])
      ∎

-- Proof of existence and uniqueness

  module _
    (β : B)
    (ϕ : RingHomo {ℓ₁} {ℓ₁ L.⊔ ℓ₂} P.rawRing B.rawRing)
    (ϕ-inject : (r : A.Carrier) → RingHomo.⟦ ϕ ⟧ (inject r) B.≈ ⟦ r ⟧)
    (ϕ-id# : RingHomo.⟦ ϕ ⟧ (shift 1 1#) B.≈ β)
      where
      
      eval-unique : (p : Poly) → RingHomo.⟦ ϕ ⟧ p B.≈ eval β p
      eval-unique [] = MonHomo.ε-homo (+-monoidHom ϕ)
      eval-unique (a ∷ p)  = begin
        RingHomo.⟦ ϕ ⟧ (a ∷ p)
          ≈⟨ S.IsRelHomo.cong (isRelHomo ϕ)
            (cons ((A.+-identityʳ a)) (P.+-identityˡ p)) ⟨
        RingHomo.⟦ ϕ ⟧ ((a ∷ []) P.+ (shift 1 p))
          ≈⟨ IsMagmaHomo.homo (+-isMagmaHomo ϕ)
            (a ∷ [])  (shift 1 p) ⟩
        RingHomo.⟦ ϕ ⟧ (a ∷ []) B.+ RingHomo.⟦ ϕ ⟧  (shift 1 p)
          ≈⟨ B.+-congˡ (S.IsRelHomo.cong (isRelHomo ϕ) (shiftp≈x*p p)) ⟩
        RingHomo.⟦ ϕ ⟧  (a ∷ []) B.+ RingHomo.⟦ ϕ ⟧ ((shift 1 1#) P.*  p)
          ≈⟨ B.+-congˡ (IsMagmaHomo.homo (*-isMagmaHomo ϕ) (shift 1 1#) p) ⟩
        RingHomo.⟦ ϕ ⟧  (a ∷ []) B.+ RingHomo.⟦ ϕ ⟧
        (shift 1 1#) B.* (RingHomo.⟦ ϕ ⟧ p)
          ≈⟨ B.+-congˡ (B.*-cong ϕ-id# (eval-unique p)) ⟩
        RingHomo.⟦ ϕ ⟧ (inject a) B.+ β B.* eval β p
          ≈⟨ B.+-congʳ (ϕ-inject a) ⟩
        eval β (a ∷ p)
          ∎

