open import Algebra.Bundles using (Semiring)

module Algebra.Polynomial.Poly.Properties.Semiring 
  {ℓ₁ ℓ₂} (SR : Semiring ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw 
import Algebra.Definitions as Def
open import Algebra.Polynomial.Poly.Base.Semiring SR as P public
  using ( Poly; _+_; _*_; _·_; shift; _≈_; refl; trans; sym
        ; IsZero; []≈ ; ≈[]; cons; zeros-unique; consˡ; consʳ)
open import Algebra.Structures
  using ( IsMagma; IsSemigroup; IsCommutativeSemigroup; IsMonoid
        ; IsSemiring; IsCommutativeMonoid)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All ; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base as ℕ using (ℕ; suc; pred; _⊔_)
open import Data.Product using (_,_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Core using (cong)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary using (Dec; yes; no)

open Def _≈_

module SR = Semiring SR
open SR
  renaming
  ( Carrier to A
  ; _≈_ to _≈A_
  ; _+_ to _+A_
  ; _*_ to _*A_
  )
  using (0#; 1#)

private
  variable
    a b c d : A
    p : Poly 
    q : Poly 
    r : Poly 
    s : Poly 

---------------------------------------------------
-- Equational reasoning for Polynomials

≈-setoid : Setoid _ _
≈-setoid = record
  { Carrier       = Poly
  ; _≈_           = _≈_
  ; isEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }
  }

open module ≈-Reasoning = SetoidReasoning ≈-setoid 

--Properties of zero polynomial

IsZero⇒p≈[] : IsZero p → p ≈ []
IsZero⇒p≈[] [] = refl
IsZero⇒p≈[] (a≈0 ∷ p≈0) = ≈[] (_) (a≈0 ∷ p≈0)

p≈[]⇒IsZero : p ≈ [] → IsZero p
p≈[]⇒IsZero ([]≈ [] q≈0) = q≈0
p≈[]⇒IsZero (≈[] _ p≈0)   = p≈0

IsZero⇒IsZero : IsZero p → IsZero q → p ≈ q
IsZero⇒IsZero [] q≈0 = []≈ _ q≈0
IsZero⇒IsZero (a≈0 ∷ p≈0) [] = ≈[] (_ ∷ _) (a≈0 ∷ p≈0)
IsZero⇒IsZero (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = cons (SR.trans a≈0 (SR.sym b≈0))
         (trans (IsZero⇒IsZero p≈0 p≈0) (IsZero⇒IsZero p≈0 q≈0))

p≈[]⇒0∷p≈0 : p ≈ [] → IsZero (0# ∷ p)
p≈[]⇒0∷p≈0 ([]≈ [] refl) = SR.refl ∷ refl
p≈[]⇒0∷p≈0 (≈[] p p≈[]) = SR.refl ∷ p≈[]

a∷p≈[]⇒a≈0 : (a ∷ p) ≈ [] → a ≈A 0#
a∷p≈[]⇒a≈0 (≈[] a∷p (a≈0 ∷ p≈0)) = a≈0

p≈[]⇒0∷p≈p : p ≈ [] → p ≈ (0# ∷ p)
p≈[]⇒0∷p≈p ([]≈ [] refl) = []≈ (0# ∷ []) (SR.refl ∷ refl)
p≈[]⇒0∷p≈p (≈[] [] p≈[]) = []≈ (0# ∷ []) (SR.refl ∷ p≈[])
p≈[]⇒0∷p≈p (≈[] (a ∷ p) (a≈0 ∷ p≈0))
  = IsZero⇒IsZero (a≈0 ∷ p≈0) (SR.refl ∷ a≈0 ∷ p≈0)

p≈[]∧q≈[]⇒p+q≈[] : IsZero p → IsZero q → IsZero (p + q)
p≈[]∧q≈[]⇒p+q≈[] [] [] = []
p≈[]∧q≈[]⇒p+q≈[] [] (b≈0 ∷ q≈0) = b≈0 ∷ q≈0
p≈[]∧q≈[]⇒p+q≈[] (a≈0 ∷ p≈0) [] = a≈0 ∷ p≈0
p≈[]∧q≈[]⇒p+q≈[] (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = SR.trans (SR.+-cong a≈0 b≈0) (SR.+-identityʳ 0#) ∷ p≈[]∧q≈[]⇒p+q≈[] p≈0 q≈0

-------------------------------------------
--Properties of polynomial addition

+-comm : (p : Poly) → (q : Poly) → p + q ≈ q + p
+-comm [] [] = refl
+-comm [] (a ∷ p) = refl
+-comm (a ∷ p) [] = refl
+-comm (a ∷ p) (b ∷ q) = cons (SR.+-comm a b) (+-comm p q)

+-idʳ : (p : Poly) → (q : Poly) → IsZero q → p + q ≈ p
+-idʳ [] q [] = refl
+-idʳ (a ∷ p) q [] = refl
+-idʳ [] (a ∷ q) (a≈0 ∷ q≈0) = ≈[] (a ∷ q) (a≈0 ∷ q≈0)
+-idʳ (a ∷ p) (b ∷ q) (b≈0 ∷ q≈0)
  = cons (SR.trans (SR.+-congˡ b≈0) (SR.+-identityʳ a)) (+-idʳ p q q≈0)

+-idˡ : (p : Poly) → (q : Poly) → IsZero p → p + q ≈ q
+-idˡ p q p≈0 = begin
  p + q  ≈⟨ +-comm p q ⟩
  q + p  ≈⟨ +-idʳ q p p≈0 ⟩
  q ∎

+-identityˡ : (p : Poly) → [] + p ≈ p
+-identityˡ p = +-idˡ [] p []

+-identityʳ : (p : Poly) → p + [] ≈ p
+-identityʳ p = +-idʳ p [] []

+-cong : p ≈ q → r ≈ s → p + r ≈ q + s
+-cong {r = r} {s = s} ([]≈ q q≈0) r≈s = begin
  [] + r  ≈⟨ +-idˡ [] r [] ⟩
  r       ≈⟨ r≈s ⟩
  s       ≈⟨ +-idˡ q s q≈0 ⟨
  q + s   ∎
+-cong {r = r} {s = s} (≈[] p p≈0) r≈s = begin
  p + r   ≈⟨ +-idˡ p r p≈0 ⟩
  r       ≈⟨ r≈s ⟩
  s       ≈⟨ +-idˡ [] s [] ⟨
  [] + s  ∎
+-cong {p = a ∷ p} {q = b ∷ q} (cons a≈b p≈q) ([]≈ s s≈0) = begin
  a ∷ p        ≈⟨ cons a≈b p≈q ⟩
  b ∷ q        ≈⟨ +-idʳ (b ∷ q) s s≈0 ⟨
  (b ∷ q) + s  ∎
+-cong {p = a ∷ p} {q = b ∷ q} (cons a≈b p≈q) (≈[] r r≈0) = begin
  (a ∷ p) + r  ≈⟨ +-idʳ (a ∷ p) r r≈0 ⟩
  a ∷ p        ≈⟨ cons a≈b p≈q ⟩
  b ∷ q        ∎
+-cong (cons a≈b p≈q) (cons c≈d r≈s)
  = cons (SR.+-cong a≈b c≈d) (+-cong p≈q r≈s)

+-congˡ : p ≈ q → p + r ≈ q + r
+-congˡ p≈q = +-cong p≈q refl

+-congʳ : q ≈ r → p + q ≈ p + r
+-congʳ q≈r = +-cong refl q≈r

+-assoc : (p : Poly) → (q : Poly) → (r : Poly) →
        (p + q) + r ≈ p + (q + r) 
+-assoc [] q r =  begin
  [] + q + r ≈⟨ +-congˡ (+-idˡ [] q []) ⟩
  q + r        ≈⟨ +-idˡ [] (q + r) [] ⟨
  [] + (q + r) ∎
+-assoc (a ∷ p) [] r = +-congʳ (sym (+-idˡ [] r []))
+-assoc (a ∷ p) (b ∷ q) [] = refl
+-assoc (a ∷ p) (b ∷ q) (c ∷ r)
  = cons (SR.+-assoc a b c) (+-assoc p q r)

middleFour : (p : Poly) → (q : Poly) → (r : Poly) → (w : Poly) →
             (p + q) + (r + w) ≈ (p + r) + (q + w)   
middleFour p q r w = begin
  (p + q) + (r + w)  ≈⟨ +-assoc (p + q) r w ⟨
  (p + q + r) + w    ≈⟨ +-congˡ (+-assoc p q r) ⟩
  (p + (q + r)) + w  ≈⟨ +-congˡ (+-congʳ (+-comm q r))  ⟩
  (p + (r + q)) + w  ≈⟨ +-congˡ (+-assoc p r q) ⟨
  (p + r + q) + w    ≈⟨ +-assoc (p + r) q w ⟩
  (p + r) + (q + w)  ∎

--------------------------------------------------------------------
-- Properties of polynomial shifting

*-distrib-shift : (p : Poly) → (q : Poly) →
                 p * (shift q) ≈ shift (p * q)
*-distrib-shift [] q = begin
  [] * (0# ∷ q)
    ≈⟨ []≈ [] [] ⟩
  []
    ≈⟨ ≈[] (0# ∷ [] * q) (SR.refl ∷ []) ⟨
  0# ∷ [] * q ∎
*-distrib-shift (a ∷ p) q = begin
  (a ∷ p) * (0# ∷ q)
    ≈⟨ +-congˡ (consˡ (SR.zeroʳ a)) ⟩
  (0# ∷ a · q) + p * (0# ∷ 0# ∷ q)
    ≈⟨  +-congʳ (*-distrib-shift p (0# ∷ q)) ⟩
  (0# ∷ a · q) + (0# ∷ (p * (0# ∷ q)))
    ≈⟨  consˡ (SR.+-identityˡ 0#) ⟩
  0# ∷ (a · q + p * (0# ∷ q))
    ≈⟨  consʳ refl ⟨ 
  0# ∷ ((a ∷ p) * q)
    ∎

·-distrib-shift : (a : A) → (p : Poly) → a · (shift p) ≈ shift (a · p)
·-distrib-shift a [] = cons (SR.zeroʳ a) (refl)
·-distrib-shift a (b ∷ p) = consˡ (SR.zeroʳ a)

----------------------------------------------------------------
-- Properties of polynomial scaling

a·p≈a∷[]*p : (a : A) → (p : Poly) → a · p ≈ (a ∷ []) * p
a·p≈a∷[]*p a [] = refl
a·p≈a∷[]*p a (b ∷ p) = begin
  a · (b ∷ p) ≈⟨ +-idʳ (a · (b ∷ p)) ([] * (0# ∷ b ∷ p)) [] ⟨
  (a ∷ []) * (b ∷ p) ∎

1·p≈p : (p : Poly) → 1# · p ≈ p
1·p≈p [] = refl
1·p≈p (a ∷ p) = cons (SR.*-identityˡ a) (1·p≈p p)

pIsZero⇒a·pIsZero : (a : A) → (p : Poly) → IsZero p → IsZero (a · p) 
pIsZero⇒a·pIsZero a p [] =  []
pIsZero⇒a·pIsZero a (b ∷ p) (b≈0 ∷ p≈0)
  = (SR.trans (SR.*-congˡ b≈0) (SR.zeroʳ a)) ∷ pIsZero⇒a·pIsZero a p p≈0

a≈0⇒a·pIsZero : (a : A) → (p : Poly) → a ≈A 0# → IsZero (a · p)
a≈0⇒a·pIsZero a [] a≈0 = []
a≈0⇒a·pIsZero a (b ∷ p) a≈0
  = SR.trans (SR.*-congʳ a≈0) (SR.zeroˡ b) ∷ (a≈0⇒a·pIsZero a p a≈0)

·-cong : a ≈A b → p ≈ q → a · p ≈ b · q
·-cong {a = a} {b = b} _ ([]≈ q q≈0)
  = sym (≈[] (b · q) (pIsZero⇒a·pIsZero b q q≈0))
·-cong {a = a} {b = b} _ (≈[] p p≈0)
  = sym ([]≈ (a · p) (pIsZero⇒a·pIsZero a p p≈0))
·-cong {a = a} {b = b} c≈d (cons a≈b p≈q)
  = cons (SR.*-cong c≈d a≈b) (·-cong c≈d p≈q)

·-congˡ : a ≈A b → a · p ≈ b · p
·-congˡ a≈b  = ·-cong a≈b refl

·-congʳ : p ≈ q → a · p ≈ a · q
·-congʳ = ·-cong SR.refl

·-dist : a · (p + q) ≈ (a · p) + (a · q)
·-dist {p = []} {q = []} = refl
·-dist {p = []} {q = b ∷ q} = refl
·-dist {p = b ∷ p} {q = []} = refl
·-dist {a = a} {p = b ∷ p} {q = c ∷ q} = cons (SR.distribˡ a b c) ·-dist

·-assoc : a · (b · p) ≈ (a *A b) · p
·-assoc {p = []} = refl
·-assoc {a = a} {b = b} {p = c ∷ p} = cons (SR.sym (SR.*-assoc a b c)) ·-assoc

a·-cong : p ≈ q → a · p ≈ a · q
a·-cong = ·-cong SR.refl

·-distrib-+A : (a b : A) → (p : Poly) → (a +A b) · p ≈ a · p + b · p
·-distrib-+A a b [] = refl
·-distrib-+A a b (c ∷ p) = cons (SR.distribʳ c a b) (·-distrib-+A a b p)

-----------------------------------------------------------------
-- Properties of polynomial multiplication

pIsZero⇒p*qIsZero : (q : Poly) → IsZero p → IsZero (p * q)
pIsZero⇒p*qIsZero q [] = []
pIsZero⇒p*qIsZero {p = a ∷ p} q (a≈0 ∷ p≈0)
  = p≈[]∧q≈[]⇒p+q≈[] (a≈0⇒a·pIsZero a q a≈0) (pIsZero⇒p*qIsZero (0# ∷ q) p≈0)

pIsZero⇒q*pIsZero : (q : Poly) → IsZero p → IsZero (q * p)
pIsZero⇒q*pIsZero [] p≈0 = []
pIsZero⇒q*pIsZero {p = p} (b ∷ q) p≈0
  = p≈[]∧q≈[]⇒p+q≈[] (pIsZero⇒a·pIsZero b p p≈0)
    (pIsZero⇒q*pIsZero q (SR.refl ∷ p≈0))

p≈[]⇒p*q≈[] : (q : Poly) → p ≈ [] → p * q ≈ []
p≈[]⇒p*q≈[] q p≈[]
  = IsZero⇒p≈[] (pIsZero⇒p*qIsZero q (p≈[]⇒IsZero p≈[]))

p≈[]⇒q*p≈[] : (q : Poly) → p ≈ [] → q * p ≈ []
p≈[]⇒q*p≈[] q p≈[]
  = IsZero⇒p≈[] (pIsZero⇒q*pIsZero q (p≈[]⇒IsZero p≈[]))

zeroˡ : (p : Poly) → [] * p ≈ []
zeroˡ p = refl

zeroʳ : (p : Poly) → p * [] ≈ []
zeroʳ [] = refl
zeroʳ (a ∷ p) = begin
  (a ∷ p) * []
    ≈⟨ +-idˡ [] (p * (0# ∷ [])) [] ⟩
  p * (0# ∷ [])
    ≈⟨ ≈[] (p * (0# ∷ [])) (pIsZero⇒q*pIsZero p (SR.refl ∷ [])) ⟩
  []
  ∎

*-cong : {p : Poly} → {q : Poly} → {r : Poly} → {s : Poly} →
     p ≈ q → r ≈ s → p * r ≈ q * s
*-cong {q = q} {r = r} {s = s} ([]≈ q q≈0) r≈s = begin
  [] * r  ≈⟨ zeroˡ r ⟩
  []      ≈⟨ p≈[]⇒p*q≈[] s (IsZero⇒p≈[] q≈0) ⟨
  q * s   ∎
*-cong {q = q} {r = r} {s = s} (≈[] p p≈0) r≈s = begin
  p * r   ≈⟨ p≈[]⇒p*q≈[] r (IsZero⇒p≈[] p≈0) ⟩
  []      ≈⟨ zeroˡ p ⟨
  [] * s  ∎
*-cong {p = a ∷ p} {q = b ∷ q} (cons a≈b p≈q) ([]≈ s s≈0) = begin
  (a ∷ p) * []  ≈⟨ zeroʳ (a ∷ p) ⟩
  []            ≈⟨ p≈[]⇒q*p≈[] (b ∷ q) (IsZero⇒p≈[] s≈0) ⟨
  (b ∷ q) * s   ∎
*-cong {p = a ∷ p} {q = b ∷ q} (cons a≈b p≈q) (≈[] r r≈0) = begin
  (a ∷ p) * r  ≈⟨ p≈[]⇒q*p≈[] (a ∷ p) (IsZero⇒p≈[] r≈0) ⟩
  []           ≈⟨ zeroʳ (b ∷ q) ⟨
  (b ∷ q) * [] ∎
*-cong {a ∷ p} {b ∷ q} {c ∷ r} {d ∷ s} (cons a≈b p≈q) (cons c≈d r≈s) = begin
  (a ∷ p) * (c ∷ r)
    ≈⟨ refl ⟩
  (a *A c ∷ a · r) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consˡ (SR.*-cong a≈b c≈d)) ⟩
  (b *A d ∷ a · r) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consʳ (·-cong a≈b r≈s)) ⟩
  (b *A d ∷ b · s) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congʳ (*-cong p≈q (consʳ (cons c≈d r≈s))) ⟩
  (b *A d ∷ b · s) + q * (0# ∷ d ∷ s)
    ≈⟨ refl ⟩
  (b ∷ q) * (d ∷ s)
    ∎

*-congʳ : q ≈ r → p * q ≈ p * r
*-congʳ {p = p} q≈r = *-cong {p = p} refl q≈r

*-congˡ : p ≈ q → p * r ≈ q * r
*-congˡ p≈q = *-cong p≈q refl

shift-distrib-+ : (p : Poly) → (q : Poly) →
                  shift (p + q) ≈ (shift p) + (shift q)
shift-distrib-+ p q = cons (SR.sym (SR.+-identityʳ 0#)) refl

*-identityʳ : (p : Poly) → p * (1# ∷ []) ≈ p
*-identityʳ [] = zeroˡ []
*-identityʳ (a ∷ p) = begin
  (a ∷ p) * (1# ∷ [])
    ≈⟨ refl ⟩
  (a *A 1# ∷ []) + (p * (0# ∷ 1# ∷ []))
    ≈⟨ +-congˡ (consˡ (SR.*-identityʳ a)) ⟩
  (a ∷ []) + (p * (0# ∷ 1# ∷ []))
    ≈⟨ +-congʳ (*-distrib-shift p (1# ∷ [])) ⟩
  (a ∷ []) + (0# ∷ (p * (1# ∷ [])))
    ≈⟨ cons (SR.+-identityʳ a) (+-identityˡ (p * (1# ∷ []))) ⟩
  a ∷ (p * (1# ∷ []))
    ≈⟨ consʳ (*-identityʳ p) ⟩
  a ∷ p ∎

*-identityˡ : (p : Poly) → (1# ∷ []) * p ≈ p
*-identityˡ [] = refl
*-identityˡ (a ∷ p) = begin
  (1# ∷ []) * (a ∷ p)
    ≈⟨ consʳ refl ⟩
  1# · (a ∷ p) + [] * (0# ∷ a ∷ p)
    ≈⟨ +-identityʳ (1# · (a ∷ p) + []) ⟩
  1# · (a ∷ p) + []
    ≈⟨ +-identityʳ  (1# · (a ∷ p)) ⟩
  1# · (a ∷ p)
    ≈⟨ cons (SR.*-identityˡ a) (1·p≈p p) ⟩
  a ∷ p ∎

shiftp≈p*x :  (p : Poly) → shift p ≈ p * (0# ∷ 1# ∷ [])
shiftp≈p*x [] = sym (begin
  [] * (0# ∷ 1# ∷ [])
    ≈⟨ refl ⟩
  []
    ≈⟨ p≈[]⇒0∷p≈p refl ⟩
  0# ∷ [] ∎)
shiftp≈p*x (a ∷ p) = begin
 0# ∷ a ∷ p
   ≈⟨ cons (SR.+-identityˡ 0#) (cons (SR.+-identityʳ a) (+-identityˡ p)) ⟨
 (0# ∷ a ∷ []) + shift (shift p)
   ≈⟨ consʳ (consʳ (+-congʳ (*-identityʳ p))) ⟨
 (0# ∷ a ∷ []) + (shift (shift (p * (1# ∷ []))))
   ≈⟨ +-congʳ {p = 0# ∷ a ∷ []} (consʳ (*-distrib-shift p (1# ∷ []))) ⟨
 (0# ∷ a ∷ []) + shift (p * shift (1# ∷ []))
   ≈⟨ +-congʳ {p = 0# ∷ a ∷ []} (*-distrib-shift p (0# ∷ 1# ∷ [])) ⟨
 (0# ∷ a ∷ []) + p * shift (shift (1# ∷ []))
   ≈⟨ +-congˡ (cons (SR.zeroʳ a) (consˡ (SR.*-identityʳ a))) ⟨
 a · (0# ∷ 1# ∷ []) + p * (0# ∷ 0# ∷ 1# ∷ [])
   ≈⟨ refl ⟨
 (a ∷ p) * (0# ∷ 1# ∷ []) ∎

shiftp≈x*p : (p : Poly) → shift p ≈ (0# ∷ 1# ∷ []) * p
shiftp≈x*p [] = begin
  0# ∷ []
    ≈⟨ p≈[]⇒0∷p≈p refl ⟨
  []
    ≈⟨ zeroʳ (0# ∷ 1# ∷ []) ⟨
  (0# ∷ 1# ∷ []) * []
    ∎
shiftp≈x*p (a ∷ p) = begin
  0# ∷ a ∷ p
    ≈⟨ 1·p≈p (0# ∷ a ∷ p) ⟨
  1# · (0# ∷ a ∷ p)
    ≈⟨ +-identityʳ (1# · (0# ∷ a ∷ p)) ⟨
  1# · (0# ∷ a ∷ p) + []
    ≈⟨ refl ⟨
  (1# ∷ []) * (0# ∷ a ∷ p)
    ≈⟨ +-idˡ (0# · (a ∷ p)) ((1# ∷ []) * (0# ∷ a ∷ p))
      (a≈0⇒a·pIsZero 0# (a ∷ p) SR.refl)⟨
  (0# · (a ∷ p)) + ((1# ∷ []) * (0# ∷ a ∷ p))
    ≈⟨ refl ⟨
  (0# ∷ 1# ∷ []) * (a ∷ p)
  ∎

·-distrib-* : (p : Poly) → (q : Poly) → (a : A) →
              a · (p * q) ≈ (a · p) * q
·-distrib-* [] q a = refl
·-distrib-* (b ∷ p) [] a = begin
   a · ((b ∷ p) * [])
    ≈⟨ a·-cong ( +-idʳ [] (p * (0# ∷ []))
      (pIsZero⇒q*pIsZero p (p≈[]⇒0∷p≈0 refl))) ⟩
  []
    ≈⟨ zeroʳ (a · (b ∷ p)) ⟨
  (a · (b ∷ p)) * []
    ∎
·-distrib-* (b ∷ p) (c ∷ q) a = begin
  a · ((b ∷ p) * (c ∷ q))
    ≈⟨ refl ⟩
  a · ((b · (c ∷ q)) + (p * (0# ∷ c ∷ q)))
    ≈⟨ ·-dist ⟩
  a · (b *A c ∷ (b · q)) + a · (p * (0# ∷ c ∷ q))
    ≈⟨ +-congˡ (cons (SR.sym (SR.*-assoc a b c)) ·-assoc) ⟩
  (a *A b *A c ∷ ((a *A b) · q)) + a · (p * (0# ∷ c ∷ q))
    ≈⟨ +-congʳ (·-distrib-* p (0# ∷ c ∷ q) a) ⟩
  (a *A b) · (c ∷ q) + (a · p) * (0# ∷ c ∷ q)
    ≈⟨ refl ⟩
  (a · (b ∷ p)) * (c ∷ q) ∎

0∷[p*q]≈[0∷p]*q : (p : Poly) → (q : Poly) → shift (p * q) ≈ (shift p) * q
0∷[p*q]≈[0∷p]*q [] q = begin
  shift ([] * q)
    ≈⟨ consʳ (refl) ⟩
  shift []
    ≈⟨ p≈[]⇒0∷p≈p refl  ⟨
  []
    ≈⟨ p≈[]⇒p*q≈[] q (sym (p≈[]⇒0∷p≈p refl)) ⟨
  (0# ∷ []) * q
    ∎
0∷[p*q]≈[0∷p]*q (a ∷ p) q = begin
  shift ((a ∷ p) * q)
    ≈⟨ *-distrib-shift (a ∷ p) q ⟨
  (a ∷ p) * shift q
    ≈⟨ refl ⟩
  a · shift q + p * (0# ∷ shift q)
    ≈⟨ +-idˡ (0# · q) (a · (0# ∷ q) + p * (0# ∷ 0# ∷ q))
      (a≈0⇒a·pIsZero 0# q SR.refl) ⟨
  0# · q + (a · (0# ∷ q) + p * (0# ∷ 0# ∷ q))
    ≈⟨ refl ⟩
  shift (a ∷ p) * q
    ∎
                  
*-distribˡ-+ : (p : Poly) → (q : Poly) → (r : Poly) →
                p * (q + r) ≈ p * q + p * r
*-distribˡ-+ [] q r = begin
  [] * (q + r) ≈⟨ zeroˡ (q + r) ⟩
  [] ≈⟨ refl ⟩
  [] * q + [] * r ∎
*-distribˡ-+ (a ∷ p) q r = begin
   (a ∷ p) * (q + r)
    ≈⟨ refl ⟩
  a · (q + r) + p * (0# ∷ q + r)
    ≈⟨ +-cong ·-dist (*-distrib-shift p (q + r)) ⟩
  (a · q + a · r) + (0# ∷ (p * (q + r)))
    ≈⟨ +-congʳ (consʳ (*-distribˡ-+ p q r)) ⟩
  (a · q + a · r) + (0# ∷ (p * q + p * r))
    ≈⟨ +-congʳ (consˡ (SR.+-identityʳ 0#)) ⟨
  (a · q + a · r) + ((0# ∷ (p * q)) + (0# ∷ (p * r)))
    ≈⟨ middleFour (a · q) (a · r) (0# ∷ p * q) (0# ∷ p * r) ⟩
  ((a · q) + (0# ∷ (p * q))) + ((a · r) + (0# ∷ (p * r)))
    ≈⟨ +-cong (+-congʳ (*-distrib-shift p q)) (+-congʳ (*-distrib-shift p r)) ⟨
  (a · q + p * (0# ∷ q)) +  (a · r + p * (0# ∷ r))
    ≈⟨ refl ⟨
  (a ∷ p) * q + (a ∷ p) * r
    ∎

*-distribʳ-+ : (p : Poly) → (q : Poly) → (r : Poly) →
               (q + r) * p ≈ (q * p) + (r * p)
*-distribʳ-+  p [] [] = sym (+-identityʳ ([]))
*-distribʳ-+  p [] (c ∷ r) = begin
  ([] + (c ∷ r)) * p   ≈⟨ refl ⟩
  (c ∷ r) * p          ≈⟨ +-identityˡ ((c ∷ r) * p) ⟨
  [] * p + (c ∷ r) * p ∎
*-distribʳ-+  p (b ∷ q) [] = begin
 ((b ∷ q) + []) * p    ≈⟨ refl ⟩
 (b ∷ q) * p           ≈⟨ +-identityʳ ((b ∷ q) * p) ⟨
 (b ∷ q) * p + [] * p  ∎
*-distribʳ-+  p (b ∷ q) (c ∷ r) = begin
  ((b ∷ q) + (c ∷ r)) * p
    ≈⟨ refl ⟩
  (b +A c) · p + (q + r) * (0# ∷ p)
    ≈⟨ +-cong (·-distrib-+A b c p) (*-distribʳ-+ (0# ∷ p) q r) ⟩
  ((b · p) + (c · p)) + (q * (0# ∷ p) + r * (0# ∷ p))
    ≈⟨ middleFour (b · p) (c · p) (q * (0# ∷ p)) (r * (0# ∷ p)) ⟩
  (b · p + q * (0# ∷ p)) + (c · p + r * (0# ∷ p))
    ≈⟨ refl ⟨
  (b ∷ q) * p + (c ∷ r) * p
    ∎

*-assoc : (p : Poly) → (q : Poly) → (r : Poly) →
          (p * q) * r ≈ p * (q * r)
*-assoc [] q r = refl
*-assoc (a ∷ p) q r = begin
  ((a ∷ p) * q) * r
    ≈⟨ refl ⟩
  ((a · q) + (p * (0# ∷ q))) * r
    ≈⟨ *-congˡ (+-congʳ {p = a · q} (*-distrib-shift p q)) ⟩
  ((a · q) + (0# ∷ (p * q))) * r
    ≈⟨ *-distribʳ-+ r (a · q) (0# ∷ p * q) ⟩
  ((a · q) * r) + ((0# ∷ (p * q)) * r)
    ≈⟨  +-congʳ step1 ⟨
  ((a · q) * r) + (0# ∷ (p * (q * r)))
    ≈⟨ +-congˡ (·-distrib-* q r a) ⟨
  (a · (q * r)) + (0# ∷ (p * (q * r)))
    ≈⟨ +-congʳ (*-distrib-shift p (q * r)) ⟨
  (a · (q * r)) + (p * (0# ∷ (q * r)))
    ≈⟨ refl ⟩
  (a ∷ p) * (q * r)
    ∎
    where
    step1 = begin
      0# ∷ (p * (q * r))
        ≈⟨ consʳ (*-assoc p q r) ⟨
      0# ∷ ((p * q) * r)
        ≈⟨ 0∷[p*q]≈[0∷p]*q (p * q) r ⟩
      (0# ∷ (p * q)) * r
        ≈⟨ refl ⟩
      (0# · r) + ((p * q) * (0# ∷ r))
        ≈⟨ +-congˡ (IsZero⇒p≈[] (a≈0⇒a·pIsZero 0# r SR.refl) ) ⟩
      [] + ((p * q) * (0# ∷ r))
        ≈⟨ +-congʳ (*-distrib-shift (p * q) r) ⟩
      [] + (0# ∷ ((p * q) * r))
        ≈⟨ +-congʳ (0∷[p*q]≈[0∷p]*q (p * q) r) ⟩
      [] + ((0# ∷ (p * q)) * r)
        ≈⟨ +-identityˡ ((0# ∷ (p * q)) * r) ⟩
      (0# ∷ (p * q)) * r
        ∎

--------------------------------------------------------------
-- Algebraic properties of addition
+-identity : Identity [] _+_
+-identity = +-identityˡ , +-identityʳ

---------------------------------------------------------------
-- Additive structures

isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

+-isMagma : IsMagma _≈_ _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = +-cong
  }

+-isSemigroup : IsSemigroup _≈_ _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc = +-assoc
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm = +-comm
  }

+-isMonoid : IsMonoid _≈_ _+_ []
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity
  }

+-isCommutativeMonoid : IsCommutativeMonoid _≈_ _+_ []
+-isCommutativeMonoid = record
  { isMonoid = +-isMonoid
  ; comm = +-comm
  }

---------------------------------------------------------------
-- Additive raw bundles
+-rawMagma : Algebra.Bundles.Raw.RawMagma _ _
+-rawMagma = record
  { Carrier = Poly
  ; _≈_ = _≈_
  ; _∙_ = _+_
  }

+-rawSemiring : Algebra.Bundles.Raw.RawSemiring _ _
+-rawSemiring = record
  { Carrier = Poly
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = []
  ; 1# = 1# ∷ []
  }

-- Additive bundles

+-magma : Algebra.Bundles.Magma _ _
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Algebra.Bundles.Semigroup _ _
+-semigroup = record
  { isSemigroup =  +-isSemigroup
  }

+-commutativeSemigroup : Algebra.Bundles.CommutativeSemigroup _ _
+-commutativeSemigroup = record
  {  isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-monoid : Algebra.Bundles.Monoid _ _
+-monoid = record
  { isMonoid =   +-isMonoid
  }

+-commutativeMonoid : Algebra.Bundles.CommutativeMonoid _ _
+-commutativeMonoid = record
  { isCommutativeMonoid =  +-isCommutativeMonoid
  }

*-identity : Identity (1# ∷ []) _*_
*-identity =  *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero [] _*_
*-zeroˡ p = zeroˡ p

*-zeroʳ : RightZero [] _*_
*-zeroʳ p = zeroʳ p

*-zero : Zero [] _*_
*-zero =  *-zeroˡ , *-zeroʳ

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

------------------------------------------------------------------
-- Multiplicative structure

*-isMagma : IsMagma _≈_ _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong  = *-cong
  }

*-isSemigroup : IsSemigroup _≈_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc = *-assoc
  }

*-isMonoid : IsMonoid _≈_ _*_ (1# ∷ [])
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity = *-identity
  }

+-*-isSemiring : IsSemiring _≈_ _+_ _*_ [] (1# ∷ [])
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-cong = *-cong
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

---------------------------------------------------------------
-- Multiplicative bundles

*-magma :  Algebra.Bundles.Magma _ _
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Algebra.Bundles.Semigroup _ _
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-monoid : Algebra.Bundles.Monoid _ _
*-monoid = record
  { isMonoid = *-isMonoid
  }

+-*-semiring : Semiring _ _
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

------------------------------------------------------
-- Degree function and polynomial normalization

module _ (_≟0 : ∀ a → Dec (a ≈A 0#)) where

-- true degree function of a polynomial
  deg : Poly → Maybe ℕ
  deg [] = nothing
  deg (a ∷ p) with deg p
  ... | just n = just (suc n)
  ... | nothing with a ≟0
  ...   | yes _ = nothing
  ...   | no  _ = just 0

-- normalization operation for a polynomial
  norm : Poly → Poly
  norm [] = []
  norm (a ∷ p) with norm p
  ... | b ∷ q = a ∷ b ∷ q
  ... | [] with a ≟0
  ...   | yes _ = []
  ...   | no _ = a ∷ []

  just≢nothing : ∀ {n : ℕ} → just n ≢ nothing
  just≢nothing ()

  IsZero⇒deg≡nothing : ∀ {p} → IsZero p → deg p ≡ nothing
  IsZero⇒deg≡nothing [] = Eq.refl
  IsZero⇒deg≡nothing {a ∷ p} (a≈0 ∷ p≈0) 
    rewrite IsZero⇒deg≡nothing p≈0 with a ≟0
  ... | yes _   = Eq.refl
  ... | no ¬a≈0 = ⊥-elim (¬a≈0 a≈0)

  deg≡nothing⇒IsZero : ∀ {p} → deg p ≡ nothing → IsZero p
  deg≡nothing⇒IsZero {[]} eq = []
  deg≡nothing⇒IsZero {a ∷ p} eq with deg p in taildeg
  ... | just n = ⊥-elim (just≢nothing eq)
  ... | nothing with a ≟0
  ...   | yes a≈0 = a≈0 ∷ deg≡nothing⇒IsZero {p} taildeg
  ...   | no   _  = ⊥-elim (just≢nothing eq)

  deg-cong : ∀ {p q} → p ≈ q → deg p ≡ deg q
  deg-cong ([]≈ q []≈q) = Eq.sym (IsZero⇒deg≡nothing []≈q)
  deg-cong (≈[] p p≈[]) = IsZero⇒deg≡nothing p≈[]
  deg-cong {a ∷ p} {b ∷ q} (cons a≈b p≈q)
    rewrite deg-cong p≈q with deg q
  ... | just n = Eq.refl
  ... | nothing with a ≟0 | b ≟0
  ...   | yes _   | yes _    = Eq.refl
  ...   | no _    | no  _    = Eq.refl
  ...   | yes a≈0 | no  ¬b≈0 = ⊥-elim (¬b≈0 (SR.trans (SR.sym a≈b) a≈0))
  ...   | no ¬a≈0 | yes  b≈0 = ⊥-elim (¬a≈0 (SR.trans a≈b b≈0))

