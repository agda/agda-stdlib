open import Algebra.Bundles using (CommutativeRing)

module Algebra.Polynomial.Poly.Properties
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where

open import Algebra.Polynomial.Poly.Base R as P
  using ( Poly; _+_ ; _*_ ; _·_ ; -_; shift; _≈_; refl; trans; sym; zeros
        ; IsZero; []≈ ; ≈[]; cons; zeros-unique; consˡ; consʳ; cast-lem)
open import Algebra.Properties.Ring
open import Data.Nat.Base as ℕ using (ℕ; suc; pred; _⊔_)
import Data.Nat.Properties as ℕ
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All ; []; _∷_; head; tail)
import Level as L
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Core using (cong) 

module CR = CommutativeRing R
open CR
  renaming
  ( Carrier to A
  ; _≈_ to _≈A_
  ; _+_ to _+A_
  ; _*_ to _*A_
  ; -_ to -A_)
  using (0#; 1#)

private
  variable
    m n k l : ℕ
    a b c d : A
    p : Poly m
    q : Poly n
    r : Poly k
    s : Poly l

---------------------------------------------------------------------
-- Equational reasoning for Poly n and Poly m
-- where m is not necesarily the same as n
private

  infix 4 _IsRelatedTo_

  data _IsRelatedTo_ (p : Poly m) (q : Poly n) : Set (ℓ₁ L.⊔ ℓ₂) where
    relTo : (p≈q : p ≈ q) → p IsRelatedTo q

  start : _IsRelatedTo_ {m} {n} ⇒ _≈_
  start (relTo p≈q) = p≈q

  ∼-go : Trans (_≈_) (_IsRelatedTo_ {n} {k}) (_IsRelatedTo_ {m} {k})
  ∼-go p≈q (relTo q≈r) = relTo (trans p≈q q≈r)

  stop : Reflexive (_IsRelatedTo_ {m} {m})
  stop = relTo refl

  forward : (p : Poly m) → q IsRelatedTo r → p ≈ q → p IsRelatedTo r
  forward p qRr p≈q = ∼-go p≈q qRr

  backward : (p : Poly m) → q IsRelatedTo r → q ≈ p → p IsRelatedTo r
  backward p qRr q≈p = ∼-go (sym q≈p) qRr

  infix 1 begin_
  begin_ : p IsRelatedTo q → p ≈ q
  begin_ = start

  infixr 2 step-∼-⟩
  step-∼-⟩ = forward
  syntax step-∼-⟩ p qRr p≈q = p ≈⟨ p≈q ⟩ qRr

  infixr 2 step-∼-⟨
  step-∼-⟨ = backward
  syntax step-∼-⟨ p qRr q≈p = p ≈⟨ q≈p ⟨ qRr
  
  infix 3 _∎
  _∎ : (p : Poly m) → p IsRelatedTo p
  p ∎ = stop

-----------------------------------------------------------------
-- Properties of zero polynomial

zerosIsZero : (n : ℕ) → IsZero (zeros n)
zerosIsZero 0 = []
zerosIsZero (suc n) = CR.refl ∷ (zerosIsZero n)

zerosm≈zerosn : zeros m ≈ zeros n
zerosm≈zerosn {m} {n} = zeros-unique (zerosIsZero m) (zerosIsZero n)

≈0⇒IsZero : p ≈ zeros m → IsZero p
≈0⇒IsZero ([]≈ zeros zeros≈0) = []
≈0⇒IsZero (≈[] p p≈0) = p≈0
≈0⇒IsZero (cons a≈0 p≈0) = a≈0 ∷ ≈0⇒IsZero p≈0

IsZero⇒≈0 : IsZero p → p ≈ zeros m
IsZero⇒≈0 {m = m} p≈0 = zeros-unique p≈0 (zerosIsZero m)

All-p≈0∧q≈0⇒p+q≈0 : All (_≈A 0#) p → All (_≈A 0#) q → All (_≈A 0#) (p + q)
All-p≈0∧q≈0⇒p+q≈0 {p = _} {q = _} [] [] = []
All-p≈0∧q≈0⇒p+q≈0 {p = _} {q = _} [] (b≈0 ∷ q≈0) = b≈0 ∷ q≈0
All-p≈0∧q≈0⇒p+q≈0 {p = _} {q = _} (a≈0 ∷ p≈0) [] = a≈0 ∷ p≈0
All-p≈0∧q≈0⇒p+q≈0 {p = a ∷ p} {q = b ∷ q} (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = CR.trans (CR.+-cong a≈0 b≈0) (CR.+-identityˡ 0#) ∷ All-p≈0∧q≈0⇒p+q≈0 p≈0 q≈0

------------------------------------------------------
-- Additive inverse

[-p]+pIsZero : {p : Poly m} → IsZero ((- p) + p)
[-p]+pIsZero {p = []} = []
[-p]+pIsZero {p = a ∷ p} = CR.-‿inverseˡ a ∷ [-p]+pIsZero

p+[-p]IsZero : {p : Poly m} → IsZero (p + (- p))
p+[-p]IsZero {p = []} = []
p+[-p]IsZero {p = a ∷ p} = CR.-‿inverseʳ a ∷ p+[-p]IsZero

+-inverseˡ : (p : Poly m) → (- p) + p ≈ []
+-inverseˡ [] = refl
+-inverseˡ (a ∷ p)
  = ≈[] ((- (a ∷ p)) + (a ∷ p)) (CR.-‿inverseˡ a ∷ [-p]+pIsZero)

+-inverseʳ : (p : Poly m) → p + (- p) ≈ []
+-inverseʳ []  = refl
+-inverseʳ (a ∷ p)
  = ≈[] ((a ∷ p) + (- (a ∷ p))) ((CR.-‿inverseʳ a) ∷ p+[-p]IsZero)

-------------------------------------------------------
-- Negation is congruent

-⁺ : IsZero p → IsZero (- p)
-⁺ [] = []
-⁺ (a≈0 ∷ p≈0) = x≈ε⇒x⁻¹≈ε CR.ring a≈0 ∷ (-⁺ p≈0)

-⁻ : IsZero (- p) → IsZero p
-⁻ {p = []} -p≈0 = -p≈0
-⁻ {p = a ∷ p} (-a≈0 ∷ -p≈0) = x⁻¹≈ε⇒x≈ε CR.ring -a≈0 ∷ (-⁻ -p≈0)

-‿cong : p ≈ q → - p ≈ - q
-‿cong ([]≈ q q≈0) = []≈ (- q) (-⁺ q≈0)
-‿cong (≈[] p p≈0) = ≈[] (- p) (-⁺ p≈0)
-‿cong (cons a≈b p≈q) = cons (CR.-‿cong a≈b) (-‿cong p≈q)

-----------------------------------------------------
-- Properties of polynomial addition

+-comm : (p : Poly m) → (q : Poly n) → p + q ≈ q + p
+-comm [] [] = refl
+-comm [] (a ∷ p) = refl
+-comm (a ∷ p) [] = refl
+-comm (a ∷ p) (b ∷ q) = cons (CR.+-comm a b) (+-comm p q)

+-idʳ : (p : Poly n) → (q : Poly m) → IsZero q → p + q ≈ p
+-idʳ [] q [] = refl
+-idʳ (a ∷ p) q [] = refl
+-idʳ [] (a ∷ q) (a≈0 ∷ q≈0) = ≈[] (a ∷ q) (a≈0 ∷ q≈0)
+-idʳ (a ∷ p) (b ∷ q) (b≈0 ∷ q≈0)
  = cons (CR.trans (CR.+-congˡ b≈0) (CR.+-identityʳ a)) (+-idʳ p q q≈0)

+-idˡ : (p : Poly n) → (q : Poly m) → IsZero p → p + q ≈ q
+-idˡ p q p≈0 = begin
  p + q  ≈⟨ +-comm p q ⟩
  q + p  ≈⟨ +-idʳ q p p≈0 ⟩
  q ∎

+-identityʳ : (p : Poly n) → p + (zeros m) ≈ p
+-identityʳ {m = m} p = +-idʳ p (zeros m) (zerosIsZero m)

+-identityˡ : (p : Poly n) → (zeros m) + p ≈ p
+-identityˡ {m = m} p = +-idˡ (zeros m) p (zerosIsZero m)

+-cong : p ≈ q → r ≈ s → p + r ≈ q + s
+-cong {p = _} {q = _} {r = r} {s = s} ([]≈ q q≈0) r≈s = begin
  [] + r  ≈⟨ +-identityˡ r ⟩
  r       ≈⟨ r≈s ⟩
  s       ≈⟨ +-idˡ q s q≈0 ⟨
  q + s   ∎
+-cong {p = _} {q = _} {r = r} {s = s} (≈[] p p≈0) r≈s = begin
  p + r   ≈⟨ +-idˡ p r p≈0 ⟩
  r       ≈⟨ r≈s ⟩
  s       ≈⟨ +-identityˡ s ⟨
  [] + s  ∎
+-cong {p = a ∷ p} {q = b ∷ q} {r = _} {s = s} (cons a≈b p≈q) ([]≈ s s≈0) = begin
  a ∷ p        ≈⟨ cons a≈b p≈q ⟩
  b ∷ q        ≈⟨ +-idʳ (b ∷ q) s s≈0 ⟨
  (b ∷ q) + s  ∎
+-cong {p = a ∷ p} {q = b ∷ q} {r = r} {s = _} (cons a≈b p≈q) (≈[] r r≈0) = begin
  (a ∷ p) + r  ≈⟨ +-idʳ (a ∷ p) r r≈0 ⟩
  a ∷ p        ≈⟨ cons a≈b p≈q ⟩
  b ∷ q        ∎
+-cong (cons a≈b p≈q) (cons c≈d r≈s)
  = cons (CR.+-cong a≈b c≈d) (+-cong p≈q r≈s)

+-congˡ : p ≈ q → p + r ≈ q + r
+-congˡ p≈q = +-cong p≈q refl

+-congʳ : q ≈ r → p + q ≈ p + r
+-congʳ q≈r = +-cong refl q≈r

+-assoc : (p : Poly m) → (q : Poly n) → (r : Poly k) →
        (p + q) + r ≈ p + (q + r) 
+-assoc [] q r =  begin
  ([] + q) + r ≈⟨ +-congˡ (+-identityˡ q) ⟩
  q + r        ≈⟨ +-identityˡ (q + r) ⟨
  [] + (q + r) ∎
+-assoc (a ∷ p) [] r = +-congʳ (sym (+-identityˡ r))
+-assoc (a ∷ p) (b ∷ q) [] = refl
+-assoc (a ∷ p) (b ∷ q) (c ∷ r)
  = cons (CR.+-assoc a b c) (+-assoc p q r)

middleFour : (p : Poly m) → (q : Poly n) → (r : Poly k) → (w : Poly l) →
             (p + q) + (r + w) ≈ (p + r) + (q + w)   
middleFour p q r w = begin
  (p + q) + (r + w)  ≈⟨ +-assoc (p + q) r w ⟨
  (p + q + r) + w    ≈⟨ +-congˡ (+-assoc p q r) ⟩
  (p + (q + r)) + w  ≈⟨ +-congˡ (+-congʳ (+-comm q r))  ⟩
  (p + (r + q)) + w  ≈⟨ +-congˡ (+-assoc p r q) ⟨
  (p + r + q) + w    ≈⟨ +-assoc (p + r) q w ⟩
  (p + r) + (q + w)  ∎

------------------------------------------------------------------
-- Vector casting lemmas

private
  n+1≡sucn+0 : (n ℕ.+ 1) ≡ suc (n ℕ.+ 0)
  n+1≡sucn+0 {0} = Eq.refl
  n+1≡sucn+0 {suc n} = cong suc n+1≡sucn+0

  cast-p≈0⇒p≈0 : (m≡n : m ≡ n) → All (_≈A 0#) p →
                 All (_≈A 0#) (Vec.cast m≡n p)
  cast-p≈0⇒p≈0 {n = 0} {[]} m≡n [] = []
  cast-p≈0⇒p≈0 {n = suc n} {a ∷ p} m≡n (a≈0 ∷ p≈0)
    = a≈0 ∷ cast-p≈0⇒p≈0 (cong pred m≡n) p≈0

  cast-p≈p : (m≡n : m ≡ n) → Vec.cast m≡n p ≈ p
  cast-p≈p {n = 0} {[]} Eq.refl = refl
  cast-p≈p {n = suc n} {a ∷ p} m≡n = consʳ (cast-p≈p (cong pred m≡n))

------------------------------------------------------------------
-- Properties of polynomial shifting

*-distrib-shift : (p : Poly m) → (q : Poly n) →
                  p * (shift q) ≈ shift (p * q)
*-distrib-shift {_} {_} [] qs = zerosm≈zerosn
*-distrib-shift {suc m} {n} (a ∷ p) q = begin
  (a ∷ p) * (0# ∷ q)
    ≈⟨ cast-p≈p (cast-lem (suc n) m) ⟩  
  a · (0# ∷ q) + p * (0# ∷ 0# ∷ q)
    ≈⟨ +-congˡ (consˡ (CR.zeroʳ a)) ⟩
  (0# ∷ a · q) + p * (0# ∷ 0# ∷ q)
    ≈⟨ +-congʳ (*-distrib-shift p (0# ∷ q)) ⟩
  (0# ∷ a · q) + (0# ∷ (p * (0# ∷ q)))
    ≈⟨ consˡ (CR.+-identityˡ 0#) ⟩
  0# ∷ (a · q + p * (0# ∷ q))
    ≈⟨ consʳ (cast-p≈p (cast-lem n m)) ⟨
  0# ∷ ((a ∷ p) * q)
    ∎ 

·-distrib-shift : (a : A) → (p : Poly m) → a · (shift p) ≈ shift (a · p)
·-distrib-shift a [] = cons (CR.zeroʳ a) (refl)
·-distrib-shift a (b ∷ p) = consˡ (CR.zeroʳ a) 

----------------------------------------------------------------
-- Properties of polynomial scaling

a·p≈a∷[]*p : (a : A) → (p : Poly n) → a · p ≈ (a ∷ []) * p
a·p≈a∷[]*p {_} a [] = refl
a·p≈a∷[]*p {suc n} a (b ∷ p) = begin
  a · (b ∷ p)
    ≈⟨ cons (CR.+-identityʳ (a *A b)) (+-identityʳ (a · p)) ⟨
  a *A b +A 0# ∷ (a · p + zeros n)
    ≈⟨ consʳ (cast-p≈p (ℕ.⊔-idem n)) ⟨
  (a ∷ []) * (b ∷ p) ∎

pIsZero⇒a·pIsZero : (a : A) → (p : Poly n) → IsZero p → IsZero (a · p) 
pIsZero⇒a·pIsZero a p [] = []
pIsZero⇒a·pIsZero a (b ∷ p) (b≈0 ∷ p≈0)
  = (CR.trans (CR.*-congˡ b≈0) (CR.zeroʳ a)) ∷ pIsZero⇒a·pIsZero a p p≈0

a≈0⇒a·pIsZero : (a : A) → (p : Poly n) → a ≈A 0# → IsZero (a · p)
a≈0⇒a·pIsZero a [] a≈0 = []
a≈0⇒a·pIsZero a (b ∷ p) a≈0
  = CR.trans (CR.*-congʳ a≈0) (CR.zeroˡ b) ∷ (a≈0⇒a·pIsZero a p a≈0)

·-cong : a ≈A b → p ≈ q → a · p ≈ b · q
·-cong {a = _} {b = b} _ ([]≈ q q≈0)
  = sym (IsZero⇒≈0 (pIsZero⇒a·pIsZero b q q≈0))                
·-cong {a = a} {b = _}  _ (≈[] p p≈0)
  = IsZero⇒≈0 (pIsZero⇒a·pIsZero a p p≈0)                                       
·-cong {a = _} {b = _} c≈d (cons a≈b p≈q)
  = cons (CR.*-cong c≈d a≈b) (·-cong c≈d p≈q)

·-congˡ : a ≈A b → a · p ≈ b · p
·-congˡ a≈b  = ·-cong a≈b refl

·-congʳ : p ≈ q → a · p ≈ a · q
·-congʳ = ·-cong CR.refl

·-dist : a · (p + q) ≈ (a · p) + (a · q)
·-dist {a = _} {p = []} {q = []} = refl
·-dist {a = _} {p = []} {q = b ∷ q} = refl
·-dist {a = _} {p = b ∷ p} {q = []} = refl
·-dist {a = a} {p = b ∷ p} {q = c ∷ q} = cons (CR.distribˡ a b c) ·-dist

·-assoc : a · (b · p) ≈ (a *A b) · p
·-assoc {_} {_} {p = []} = refl
·-assoc {a} {b} {p = c ∷ p} = cons (CR.sym (CR.*-assoc a b c)) ·-assoc

a·-cong : p ≈ q → a · p ≈ a · q
a·-cong = ·-cong CR.refl

-----------------------------------------------------------------
-- Properties of polynomial multiplication

zeroˡ : (p : Poly m) → [] * p ≈ []
zeroˡ p = zerosm≈zerosn

zeroʳ : (p : Poly m) → p * [] ≈ []
zeroʳ {_} [] = refl
zeroʳ {m} (a ∷ p) = begin
  (a ∷ p) * []              ≈⟨ cast-p≈p (cong pred  n+1≡sucn+0) ⟩
  (a · []) + p * (0# ∷ [])  ≈⟨ +-identityˡ (p * (0# ∷ [])) ⟩
  p * (0# ∷ [])             ≈⟨ *-distrib-shift p [] ⟩
  0# ∷ (p * [])             ≈⟨ consʳ (zeroʳ p) ⟩
  0# ∷ []                   ≈⟨ zerosm≈zerosn ⟩
  []                        ∎

pIsZero⇒p*qIsZero : (q : Poly n) → IsZero p → IsZero (p * q)
pIsZero⇒p*qIsZero {n} {_} {p = []} q [] = zerosIsZero (pred n)
pIsZero⇒p*qIsZero {n} {suc m} {p = a ∷ p} q (a≈0 ∷ p≈0)
  = cast-p≈0⇒p≈0 (cast-lem n m)
    (All-p≈0∧q≈0⇒p+q≈0 (a≈0⇒a·pIsZero a q a≈0) (pIsZero⇒p*qIsZero (0# ∷ q) p≈0))
    
p≈[]⇒p*q≈[] : (q : Poly n) → p ≈ [] → p * q ≈ []
p≈[]⇒p*q≈[] q p≈0 = IsZero⇒≈0 (pIsZero⇒p*qIsZero q (≈0⇒IsZero p≈0))

*-cong : {p : Poly m} → {q : Poly n} → {r : Poly k} → {s : Poly l} →
         p ≈ q → r ≈ s → p * r ≈ q * s
*-cong {k = k} {q = q} {r} {s} ([]≈ q q≈0) r≈s = begin 
  [] * r  ≈⟨ p≈[]⇒p*q≈[] r refl ⟩
  []      ≈⟨ p≈[]⇒p*q≈[] s (IsZero⇒≈0 q≈0) ⟨
  q * s   ∎        
*-cong {k = k} {q = q} {r} {s} (≈[] p p≈0) r≈s = begin
  p * r   ≈⟨ p≈[]⇒p*q≈[] r (IsZero⇒≈0 p≈0) ⟩ 
  []      ≈⟨ zerosm≈zerosn ⟩
  [] * s  ∎
*-cong {n = suc n} {l = l} {a ∷ p} {b ∷ q} (cons a≈b p≈q) ([]≈ s s≈0) = begin
  (a ∷ p) * []
    ≈⟨ cast-p≈p (cong pred n+1≡sucn+0) ⟩
  [] + p * (0# ∷ [])
    ≈⟨ +-congʳ (*-cong (sym p≈q) (consʳ (IsZero⇒≈0 s≈0))) ⟨
  [] + q * (0# ∷ s)
    ≈⟨ +-congˡ (zerosm≈zerosn) ⟩
  zeros l + q * (0# ∷ s)
    ≈⟨ +-congˡ (IsZero⇒≈0 (pIsZero⇒a·pIsZero b s s≈0)) ⟨
  (b · s) + q * (0# ∷ s)
    ≈⟨ cast-p≈p (cast-lem l n) ⟨
  (b ∷ q) * s
    ∎            
*-cong {suc m} {k = k} {p = a ∷ p} {b ∷ q} (cons a≈b p≈q) (≈[] r s≈0) = begin
  (a ∷ p) * r
    ≈⟨ cast-p≈p (cast-lem k m) ⟩
  (a · r) + p * (0# ∷ r)
    ≈⟨ +-congʳ (*-cong (sym p≈q) (consʳ ([]≈ r s≈0))) ⟨
  (a · r) + q * (0# ∷ [])
    ≈⟨ +-congˡ (IsZero⇒≈0 (pIsZero⇒a·pIsZero a r s≈0)) ⟩
  zeros k + q * (0# ∷ [])
    ≈⟨ +-congˡ zerosm≈zerosn ⟩                           
  (b · []) + q * (0# ∷ [])
    ≈⟨ cast-p≈p (cong pred n+1≡sucn+0) ⟨
  (b ∷ q) * []
    ∎   
*-cong {suc m} {suc n} {suc k} {suc l} {a ∷ p} {b ∷ q} {c ∷ r} {d ∷ s} (cons a≈b p≈q) (cons c≈d r≈s) = begin
  (a ∷ p) * (c ∷ r)
    ≈⟨ cast-p≈p (cast-lem (suc k) m)⟩
  (a *A c ∷ a · r) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consˡ (CR.*-cong (CR.sym a≈b) (CR.sym c≈d))) ⟨
  (b *A d ∷ a · r) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consʳ ((·-cong (CR.sym a≈b) (sym r≈s)))) ⟨
  (b *A d ∷ b · s) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congʳ (*-cong p≈q (consʳ (cons c≈d r≈s))) ⟩
  (b *A d ∷ b · s) + q * (0# ∷ d ∷ s)
    ≈⟨ cast-p≈p (cast-lem (suc l) n) ⟨
  (b ∷ q) * (d ∷ s)
    ∎ 

*-congʳ : q ≈ r → p * q ≈ p * r
*-congʳ {p = p} q≈r = *-cong {p = p} refl q≈r

*-congˡ : p ≈ q → p * r ≈ q * r
*-congˡ p≈q = *-cong p≈q refl

qIsZero⇒p*qIsZero : (p : Poly m) → IsZero q → IsZero (p * q)
qIsZero⇒p*qIsZero {m} {_} {q = []} p [] = ≈0⇒IsZero (zeroʳ p)
qIsZero⇒p*qIsZero {m} {suc n} {q = b ∷ q} p (b≈0 ∷ q≈0)
  = ≈0⇒IsZero (
      begin
      p * (b ∷ q)     ≈⟨ *-congʳ {p = p} (consˡ b≈0) ⟩
      p * (0# ∷ q)    ≈⟨ *-distrib-shift p q ⟩
      0# ∷ (p * q)    ≈⟨ consʳ (IsZero⇒≈0 (qIsZero⇒p*qIsZero p q≈0)) ⟩
      0# ∷ (zeros m)  ≈⟨ zerosm≈zerosn ⟩
      zeros m  ∎
      )
              
q≈[]→p*q≈[] : (p : Poly n) → q ≈ [] → p * q ≈ []
q≈[]→p*q≈[] p q≈0 = IsZero⇒≈0 (qIsZero⇒p*qIsZero p (≈0⇒IsZero q≈0))

*-comm : (p : Poly m) → (q : Poly n) → p * q ≈ q * p
*-comm {_} {_} [] [] = refl
*-comm {_} {suc n} [] (b ∷ q) = sym ( begin
  (b ∷ q) * []
    ≈⟨ cast-p≈p (cong pred n+1≡sucn+0) ⟩
  [] + (q * (0# ∷ []))
    ≈⟨ +-congʳ (q≈[]→p*q≈[] q zerosm≈zerosn) ⟩
  [] + []
    ≈⟨ zerosm≈zerosn ⟩
  zeros (pred (0 ℕ.+ suc n))
    ∎)                   
*-comm {suc m} {_} (a ∷ p) [] = begin
   (a ∷ p) * []
     ≈⟨(cast-p≈p (cong pred n+1≡sucn+0))⟩
   [] + p * (0# ∷ [])
     ≈⟨ +-congʳ (q≈[]→p*q≈[] p zerosm≈zerosn) ⟩                
   [] + []
     ≈⟨ zerosm≈zerosn ⟩ 
   zeros (pred (0 ℕ.+ suc m))
     ∎                                               
*-comm {suc m} {suc n} (a ∷ p) (b ∷ q) = begin
  (a ∷ p) * (b ∷ q)
    ≈⟨ cast-p≈p (cast-lem (suc n) m) ⟩        
  a · (b ∷ q) + p * (0# ∷ b ∷ q)
    ≈⟨ +-congˡ (*-comm-lem (a *A b) a) ⟩         
  (a *A b ∷ []) + a · (0# ∷ q) + p * (0# ∷ b ∷ q)
    ≈⟨ +-congˡ (consˡ (CR.+-congʳ (CR.*-comm a b))) ⟩
  (b *A a ∷ []) + a · (0# ∷ q) + p * (0# ∷ b ∷ q)
    ≈⟨ +-congʳ step1  ⟩
  (b *A a ∷ []) + (a · (0# ∷ q)) + ((b · (0# ∷ p)) + (0# ∷ 0# ∷ p * q))
    ≈⟨ step2 ⟩
  ((b *A a ∷ []) + b · (0# ∷ p)) + (a · (0# ∷ q) + (0# ∷ 0# ∷ p * q))
    ≈⟨ step3 ⟩
  (b · (a ∷ p)) + (a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q)))
    ≈⟨ +-congʳ step4 ⟨
  (b · (a ∷ p) + q * (0# ∷ a ∷ p))
    ≈⟨ cast-p≈p (cast-lem (suc m) n) ⟨
  (b ∷ q) * (a ∷ p)
    ∎
  where
    *-comm-lem : ∀ {m} → {p : Poly m} → (a b : A) →
                 a ∷ (b · p) ≈ (a ∷ []) + (b · (0# ∷ p))
    *-comm-lem {p = []} a b
      = consˡ (CR.sym (CR.trans (CR.+-congˡ (CR.zeroʳ b)) (CR.+-identityʳ a)))
    *-comm-lem {p = a ∷ p} b c
      = consˡ (CR.sym (CR.trans (CR.+-congˡ (CR.zeroʳ c)) (CR.+-identityʳ b)))
      
    step1 = begin
      p * (0# ∷ b ∷ q)
        ≈⟨ *-distrib-shift p (b ∷ q) ⟩
      0# ∷ (p * (b ∷ q))
        ≈⟨ consʳ (*-comm p (b ∷ q)) ⟩
      0# ∷ ((b ∷ q) * p)
        ≈⟨ consʳ (cast-p≈p (cast-lem m n)) ⟩
      0# ∷ (b · p + q * (0# ∷ p))
        ≈⟨ consˡ (CR.sym (CR.+-identityʳ 0#)) ⟩ 
      (0# ∷ (b · p)) + (0# ∷ (q * (0# ∷ p)))
        ≈⟨ +-congˡ {r = (0# ∷ (q * (0# ∷ p)))} (·-distrib-shift b p) ⟨
      (b · (0# ∷ p)) + (0# ∷ (q * (0# ∷ p)))
        ≈⟨ +-congʳ {p = b · (0# ∷ p)} (consʳ (*-distrib-shift q p)) ⟩
      b · (0# ∷ p) + (0# ∷ 0# ∷ (q * p))
        ≈⟨ +-congʳ {p = b · (0# ∷ p)} (consʳ (consʳ (*-comm q p))) ⟩
      b · (0# ∷ p) + (0# ∷ 0# ∷ (p * q))
        ∎
        
    step2
      = middleFour (b *A a ∷ []) (a · (0# ∷ q))
        (b · (0# ∷ p)) (0# ∷ 0# ∷ (p * q))
        
    step3
      = +-congˡ {r = a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q))}
        (sym (*-comm-lem {p = p} (b *A a) b))
        
    step4 = begin
      q * (0# ∷ a ∷ p)
        ≈⟨ *-distrib-shift q (a ∷ p) ⟩
      0# ∷ (q * (a ∷ p))
        ≈⟨ consʳ (*-comm q (a ∷ p)) ⟩
      0# ∷ ((a ∷ p) * q)
        ≈⟨ consʳ (cast-p≈p (cast-lem n m)) ⟩
      0# ∷ (a · q + p * (0# ∷ q))
        ≈⟨ consˡ (CR.sym (CR.+-identityʳ 0#)) ⟩
      (0# ∷ (a · q)) + (0# ∷ (p * (0# ∷ q)))
        ≈⟨ +-congˡ {r = (0# ∷ (p * (0# ∷ q)))} (·-distrib-shift a q) ⟨
      a · (0# ∷ q) + (0# ∷ (p * (0# ∷ q)))
        ≈⟨ +-congʳ {p = a · (0# ∷ q)} (consʳ (*-distrib-shift p q))⟩
      a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q))
        ∎         

shift-distrib-+ : (p : Poly m) → (q : Poly n) →
                  shift (p + q) ≈ (shift p) + (shift q)
shift-distrib-+ p q = cons (CR.sym (CR.+-identityʳ 0#)) refl

0∷[p*q]≈[0∷p]*q : (p : Poly m) → (q : Poly n) → shift (p * q) ≈ (shift p) * q
0∷[p*q]≈[0∷p]*q p q =  begin
  0# ∷ (p * q)       ≈⟨ consʳ (*-comm p q) ⟩
  0# ∷ (q * p)       ≈⟨ *-distrib-shift q p ⟨
  q * (0# ∷ p)       ≈⟨ *-comm q (0# ∷ p) ⟩
  (0# ∷ p) * q       ∎               

0∷[p*q]≈q*[0∷p] : (p : Poly m) → (q : Poly n) → shift (p * q) ≈ q * (shift p)
0∷[p*q]≈q*[0∷p] p q =  begin
   0# ∷ (p * q)       ≈⟨ 0∷[p*q]≈[0∷p]*q p q ⟩
   (0# ∷ p) * q       ≈⟨ *-comm (0# ∷ p) q ⟩
   q * (0# ∷ p)       ∎

*-distribʳ-+ : (p : Poly m) → (q : Poly n) → (r : Poly k) →
               (q + r) * p ≈ (q * p) + (r * p)
*-distribʳ-+ {_} {_} {_} [] q r = begin
  (q + r) * []
    ≈⟨ q≈[]→p*q≈[] (q + r) refl ⟩
  [] + []
    ≈⟨ +-cong (zeroʳ q) (zeroʳ r)⟨   
  (q * []) + (r * [])
    ∎
*-distribʳ-+ {suc m} {n} {k} (a ∷ p) q r = begin
  ((q + r) * (a ∷ p))
    ≈⟨ *-comm  (q + r) (a ∷ p) ⟩
  ((a ∷ p) * (q + r))
    ≈⟨ cast-p≈p (cast-lem (n ⊔ k) m)  ⟩       
  (a · (q + r)) + (p * (0# ∷ (q + r)))
    ≈⟨ +-cong ·-dist (*-distrib-shift p (q + r)) ⟩        
  (a · q + a · r) + (0# ∷ (p * (q + r)))
    ≈⟨ +-congʳ step5 ⟩
  (a · q + a · r) + ((0# ∷ (q * p)) + (0# ∷ (r * p)))
    ≈⟨ middleFour (a · q) (a · r) (0# ∷ (q * p)) (0# ∷ (r * p)) ⟩ 
  (a · q + (0# ∷ (q * p))) + (a · r + (0# ∷ (r * p)))
    ≈⟨ +-congˡ step6 ⟩
  q * (a ∷ p) + (a · r + (0# ∷ r * p)) 
    ≈⟨ +-congʳ step7 ⟩
    (q * (a ∷ p) + r * (a ∷ p))
       ∎
    where
    step5 = begin
      0# ∷ p * (q + r)
        ≈⟨ consʳ (*-comm p (q + r)) ⟩
      0# ∷ ((q + r) * p)
        ≈⟨ consʳ (*-distribʳ-+ p q r) ⟩
      0# ∷ q * p + r * p
        ≈⟨ shift-distrib-+ (q * p) (r * p) ⟩
      (0# ∷ q * p) + (0# ∷ r * p) ∎
      
    step6 = begin
      a · q + (0# ∷ q * p)
        ≈⟨ +-congʳ (0∷[p*q]≈q*[0∷p] q p) ⟩
      a · q + p * (0# ∷ q)
        ≈⟨ cast-p≈p (cast-lem n m) ⟨
      (a ∷ p) * q
        ≈⟨ *-comm (a ∷ p) q ⟩
      q * (a ∷ p) ∎
      
    step7 = begin
      a · r + (0# ∷ r * p)
        ≈⟨ +-congʳ (0∷[p*q]≈q*[0∷p] r p) ⟩
      a · r + p * (0# ∷ r)
        ≈⟨ cast-p≈p (cast-lem k m) ⟨
      (a ∷ p) * r
        ≈⟨ *-comm (a ∷ p) r ⟩
      r * (a ∷ p) ∎
      
·-distrib-* : (p : Poly m) → (q : Poly n) → (a : A) →
              a · (p * q) ≈ (a · p) * q
·-distrib-* {_} {n} [] q a = begin
  a · ([] * q) ≈⟨ ·-congʳ zerosm≈zerosn ⟩
  a · [] ≈⟨ zerosm≈zerosn ⟨
  (a · []) * q ∎
·-distrib-* {suc m} {_} (b ∷ p) [] a = begin
  a · ((b ∷ p) * [])
    ≈⟨ a·-cong (cast-p≈p (cong pred n+1≡sucn+0)) ⟩
  a · ((b · []) + (p * (0# ∷ [])))
    ≈⟨ a·-cong (+-identityˡ (p * (0# ∷ []))) ⟩
  a · (p * (0# ∷ []))
    ≈⟨ a·-cong (q≈[]→p*q≈[] p zerosm≈zerosn) ⟩
  []
    ≈⟨ q≈[]→p*q≈[] ((a · p)) zerosm≈zerosn ⟨
  (a · p) * (0# ∷ [])
    ≈⟨ +-identityˡ ((a · p) * (0# ∷ [])) ⟨
  ((a *A b) · []) + ((a · p) * (0# ∷ []))
    ≈⟨ cast-p≈p (cong pred n+1≡sucn+0) ⟨
  (a · (b ∷ p)) * []
    ∎
·-distrib-* {suc m} {suc n} (b ∷ p) (c ∷ q) a = begin
  a · ((b ∷ p) * (c ∷ q))
    ≈⟨ a·-cong (cast-p≈p (cast-lem (suc n) m)) ⟩
  a · ((b · (c ∷ q)) + (p * (0# ∷ c ∷ q)))
    ≈⟨ ·-dist ⟩
  a · (b *A c ∷ (b · q)) + a · (p * (0# ∷ c ∷ q))
    ≈⟨ +-congˡ (cons (CR.sym (CR.*-assoc a b c)) ·-assoc) ⟩
  (a *A b *A c ∷ ((a *A b) · q)) + a · (p * (0# ∷ c ∷ q))
    ≈⟨ +-congʳ (·-distrib-* p (0# ∷ c ∷ q) a) ⟩
  (a *A b) · (c ∷ q) + (a · p) * (0# ∷ c ∷ q)
    ≈⟨ cast-p≈p (cast-lem (suc n) m) ⟨
  (a · (b ∷ p)) * (c ∷ q)
    ∎

*-assoc : (p : Poly m) → (q : Poly n) → (r : Poly k) →
          (p * q) * r ≈ p * (q * r)
*-assoc {_} {n} {k} [] q r =  begin
  zeros (n ℕ.∸ 1) * r
    ≈⟨ p≈[]⇒p*q≈[] r (IsZero⇒≈0 (zerosIsZero (n ℕ.∸ 1))) ⟩
  []
    ≈⟨ zerosm≈zerosn ⟩
  zeros (pred (0 ℕ.+ pred (n ℕ.+ k)))
    ∎      
*-assoc {suc m} {n} {k} (a ∷ p) q r = begin
  ((a ∷ p) * q) * r
    ≈⟨ *-congˡ (cast-p≈p (cast-lem n m)) ⟩
  ((a · q) + (p * (0# ∷ q))) * r
    ≈⟨ *-congˡ (+-congʳ {p = a · q} (*-distrib-shift p q)) ⟩
  ((a · q) + (0# ∷ (p * q))) * r
    ≈⟨ *-distribʳ-+ r (a · q) (0# ∷ p * q) ⟩
  ((a · q) * r) + ((0# ∷ (p * q)) * r)
    ≈⟨  +-congʳ step8 ⟨
  ((a · q) * r) + (0# ∷ (p * (q * r)))
    ≈⟨ +-congˡ (·-distrib-* q r a) ⟨
  (a · (q * r)) + (0# ∷ (p * (q * r)))
    ≈⟨ +-congʳ (*-distrib-shift p (q * r)) ⟨
  (a · (q * r)) + (p * (0# ∷ (q * r)))
    ≈⟨ cast-p≈p (cast-lem (pred (n ℕ.+ k)) m) ⟨
  (a ∷ p) * (q * r)
    ∎
    where
    step8 = begin
      0# ∷ (p * (q * r))
        ≈⟨ consʳ (*-assoc p q r) ⟨
      0# ∷ ((p * q) * r)
        ≈⟨ 0∷[p*q]≈[0∷p]*q (p * q) r ⟩
      (0# ∷ (p * q)) * r
        ≈⟨ cast-p≈p (cast-lem k (m ℕ.+ n ℕ.∸ 1)) ⟩
      (0# · r) + ((p * q) * (0# ∷ r))
        ≈⟨ +-congˡ (IsZero⇒≈0 (a≈0⇒a·pIsZero 0# r CR.refl) ) ⟩
      zeros k + ((p * q) * (0# ∷ r))
        ≈⟨ +-congʳ (*-distrib-shift (p * q) r) ⟩
      zeros k + (0# ∷ ((p * q) * r))
        ≈⟨ +-congʳ (0∷[p*q]≈[0∷p]*q (p * q) r) ⟩
      zeros k + ((0# ∷ (p * q)) * r)
        ≈⟨ +-identityˡ ((0# ∷ (p * q)) * r) ⟩
      (0# ∷ (p * q)) * r
        ∎

---------------------------------------------------------------------
-- Multiplicative identity

*-identityʳ : (p : Poly n) → p * (1# ∷ []) ≈ p
*-identityʳ {0} [] = zerosm≈zerosn
*-identityʳ {suc n} (a ∷ p) = begin
  (a ∷ p) * (1# ∷ [])
    ≈⟨ cast-p≈p (cast-lem 1 n) ⟩
  (a *A 1# ∷ []) + (p * (0# ∷ 1# ∷ []))
    ≈⟨ +-congˡ (consˡ (CR.*-identityʳ a)) ⟩
  (a ∷ []) + (p * (0# ∷ 1# ∷ []))
    ≈⟨ +-congʳ (*-distrib-shift p (1# ∷ [])) ⟩
  (a ∷ []) + (0# ∷ (p * (1# ∷ [])))
    ≈⟨ cons (CR.+-identityʳ a) (+-identityˡ (p * (1# ∷ []))) ⟩
  a ∷ (p * (1# ∷ []))
    ≈⟨ consʳ (*-identityʳ p) ⟩
  a ∷ p ∎
