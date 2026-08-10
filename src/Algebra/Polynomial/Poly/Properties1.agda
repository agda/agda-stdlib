open import Algebra.Bundles using (Ring)

module Algebra.Polynomial.Poly.Properties1
  {ℓ₁ ℓ₂} (R : Ring ℓ₁ ℓ₂)
  where

open import Algebra.Polynomial.Poly.Base1 R as P
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

module R = Ring R
open R
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

-- Properties of zero polynomial

zerosIsZero : (n : ℕ) → IsZero (zeros n)
zerosIsZero 0 = []
zerosIsZero (suc n) = R.refl ∷ (zerosIsZero n)

zerosm≈zerosn : zeros m ≈ zeros n
zerosm≈zerosn {m} {n} = zeros-unique (zerosIsZero m) (zerosIsZero n)

≈0⇒IsZero : p ≈ zeros m → IsZero p
≈0⇒IsZero ([]≈ zeros zeros≈0) = []
≈0⇒IsZero (≈[] p p≈0) = p≈0
≈0⇒IsZero (cons a≈0 p≈0) = a≈0 ∷ ≈0⇒IsZero p≈0

IsZero⇒≈0 : IsZero p → p ≈ zeros m
IsZero⇒≈0 {m = m} p≈0 = zeros-unique p≈0 (zerosIsZero m)

All-p≈0∧q≈0⇒p+q≈0 : IsZero p → IsZero q → IsZero (p + q)
All-p≈0∧q≈0⇒p+q≈0 {p = _} {q = _} [] [] = []
All-p≈0∧q≈0⇒p+q≈0 {p = _} {q = _} [] (b≈0 ∷ q≈0) = b≈0 ∷ q≈0
All-p≈0∧q≈0⇒p+q≈0 {p = _} {q = _} (a≈0 ∷ p≈0) [] = a≈0 ∷ p≈0
All-p≈0∧q≈0⇒p+q≈0 {p = a ∷ p} {q = b ∷ q} (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = R.trans (R.+-cong a≈0 b≈0) (R.+-identityˡ 0#) ∷ All-p≈0∧q≈0⇒p+q≈0 p≈0 q≈0

------------------------------------------------------
-- Additive inverse

[-p]+pIsZero : {p : Poly m} → IsZero ((- p) + p)
[-p]+pIsZero {p = []} = []
[-p]+pIsZero {p = a ∷ p} = R.-‿inverseˡ a ∷ [-p]+pIsZero

p+[-p]IsZero : {p : Poly m} → IsZero (p + (- p))
p+[-p]IsZero {p = []} = []
p+[-p]IsZero {p = a ∷ p} = R.-‿inverseʳ a ∷ p+[-p]IsZero

+-inverseˡ : (p : Poly m) → (- p) + p ≈ []
+-inverseˡ [] = refl
+-inverseˡ (a ∷ p)
  = ≈[] ((- (a ∷ p)) + (a ∷ p)) (R.-‿inverseˡ a ∷ [-p]+pIsZero)

+-inverseʳ : (p : Poly m) → p + (- p) ≈ []
+-inverseʳ []  = refl
+-inverseʳ (a ∷ p)
  = ≈[] ((a ∷ p) + (- (a ∷ p))) ((R.-‿inverseʳ a) ∷ p+[-p]IsZero)

-------------------------------------------------------
-- Negation is congruent

-⁺ : IsZero p → IsZero (- p)
-⁺ [] = []
-⁺ (a≈0 ∷ p≈0) = x≈ε⇒x⁻¹≈ε R a≈0 ∷ (-⁺ p≈0)

-⁻ : IsZero (- p) → IsZero p
-⁻ {p = []} -p≈0 = -p≈0
-⁻ {p = a ∷ p} (-a≈0 ∷ -p≈0) = x⁻¹≈ε⇒x≈ε R -a≈0 ∷ (-⁻ -p≈0)

-‿cong : p ≈ q → - p ≈ - q
-‿cong ([]≈ q q≈0) = []≈ (- q) (-⁺ q≈0)
-‿cong (≈[] p p≈0) = ≈[] (- p) (-⁺ p≈0)
-‿cong (cons a≈b p≈q) = cons (R.-‿cong a≈b) (-‿cong p≈q)

-----------------------------------------------------
-- Properties of polynomial addition

+-comm : (p : Poly m) → (q : Poly n) → p + q ≈ q + p
+-comm [] [] = refl
+-comm [] (a ∷ p) = refl
+-comm (a ∷ p) [] = refl
+-comm (a ∷ p) (b ∷ q) = cons (R.+-comm a b) (+-comm p q)

+-idʳ : (p : Poly n) → (q : Poly m) → IsZero q → p + q ≈ p
+-idʳ [] q [] = refl
+-idʳ (a ∷ p) q [] = refl
+-idʳ [] (a ∷ q) (a≈0 ∷ q≈0) = ≈[] (a ∷ q) (a≈0 ∷ q≈0)
+-idʳ (a ∷ p) (b ∷ q) (b≈0 ∷ q≈0)
  = cons (R.trans (R.+-congˡ b≈0) (R.+-identityʳ a)) (+-idʳ p q q≈0)

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
  = cons (R.+-cong a≈b c≈d) (+-cong p≈q r≈s)

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
  = cons (R.+-assoc a b c) (+-assoc p q r)

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
    ≈⟨ +-congˡ (consˡ (R.zeroʳ a)) ⟩
  (0# ∷ a · q) + p * (0# ∷ 0# ∷ q)
    ≈⟨ +-congʳ (*-distrib-shift p (0# ∷ q)) ⟩
  (0# ∷ a · q) + (0# ∷ (p * (0# ∷ q)))
    ≈⟨ consˡ (R.+-identityˡ 0#) ⟩
  0# ∷ (a · q + p * (0# ∷ q))
    ≈⟨ consʳ (cast-p≈p (cast-lem n m)) ⟨
  0# ∷ ((a ∷ p) * q)
    ∎ 

·-distrib-shift : (a : A) → (p : Poly m) → a · (shift p) ≈ shift (a · p)
·-distrib-shift a [] = cons (R.zeroʳ a) (refl)
·-distrib-shift a (b ∷ p) = consˡ (R.zeroʳ a)

----------------------------------------------------------------
-- Properties of polynomial scaling

a·p≈a∷[]*p : (a : A) → (p : Poly n) → a · p ≈ (a ∷ []) * p
a·p≈a∷[]*p {_} a [] = refl
a·p≈a∷[]*p {suc n} a (b ∷ p) = begin
  a · (b ∷ p)
    ≈⟨ cons (R.+-identityʳ (a *A b)) (+-identityʳ (a · p)) ⟨
  a *A b +A 0# ∷ (a · p + zeros n)
    ≈⟨ consʳ (cast-p≈p (ℕ.⊔-idem n)) ⟨
  (a ∷ []) * (b ∷ p) ∎

1·p≈p : (p : Poly n) → 1# · p ≈ p
1·p≈p [] = refl
1·p≈p (a ∷ p) = cons (R.*-identityˡ a) (1·p≈p p)


pIsZero⇒a·pIsZero : (a : A) → (p : Poly n) → IsZero p → IsZero (a · p) 
pIsZero⇒a·pIsZero a p [] = []
pIsZero⇒a·pIsZero a (b ∷ p) (b≈0 ∷ p≈0)
  = (R.trans (R.*-congˡ b≈0) (R.zeroʳ a)) ∷ pIsZero⇒a·pIsZero a p p≈0

a≈0⇒a·pIsZero : (a : A) → (p : Poly n) → a ≈A 0# → IsZero (a · p)
a≈0⇒a·pIsZero a [] a≈0 = []
a≈0⇒a·pIsZero a (b ∷ p) a≈0
  = R.trans (R.*-congʳ a≈0) (R.zeroˡ b) ∷ (a≈0⇒a·pIsZero a p a≈0)

·-cong : a ≈A b → p ≈ q → a · p ≈ b · q
·-cong {a = _} {b = b} _ ([]≈ q q≈0)
  = sym (IsZero⇒≈0 (pIsZero⇒a·pIsZero b q q≈0))                
·-cong {a = a} {b = _}  _ (≈[] p p≈0)
  = IsZero⇒≈0 (pIsZero⇒a·pIsZero a p p≈0)                                       
·-cong {a = _} {b = _} c≈d (cons a≈b p≈q)
  = cons (R.*-cong c≈d a≈b) (·-cong c≈d p≈q)

·-congˡ : a ≈A b → a · p ≈ b · p
·-congˡ a≈b  = ·-cong a≈b refl

·-congʳ : p ≈ q → a · p ≈ a · q
·-congʳ = ·-cong R.refl

·-dist : a · (p + q) ≈ (a · p) + (a · q)
·-dist {p = []} {q = []} = refl
·-dist {p = []} {q = b ∷ q} = refl
·-dist {p = b ∷ p} {q = []} = refl
·-dist {a = a} {p = b ∷ p} {q = c ∷ q} = cons (R.distribˡ a b c) ·-dist

·-assoc : a · (b · p) ≈ (a *A b) · p
·-assoc {p = []} = refl
·-assoc {a} {b} {p = c ∷ p} = cons (R.sym (R.*-assoc a b c)) ·-assoc

a·-cong : p ≈ q → a · p ≈ a · q
a·-cong = ·-cong R.refl

·-distrib-+A : (a b : A) → (p : Poly m) → (a +A b) · p ≈ a · p + b · p
·-distrib-+A a b [] = refl
·-distrib-+A a b (c ∷ p) = cons (R.distribʳ c a b) (·-distrib-+A a b p)

-----------------------------------------------------------------
-- Properties of polynomial multiplication

zeroˡ : (p : Poly m) → [] * p ≈ []
zeroˡ p = zerosm≈zerosn

zeroʳ : (p : Poly m) → p * [] ≈ []
zeroʳ [] = refl
zeroʳ {m} (a ∷ p) = begin
  (a ∷ p) * []              ≈⟨ cast-p≈p (cong pred  n+1≡sucn+0) ⟩
  (a · []) + p * (0# ∷ [])  ≈⟨ +-identityˡ (p * (0# ∷ [])) ⟩
  p * (0# ∷ [])             ≈⟨ *-distrib-shift p [] ⟩
  0# ∷ (p * [])             ≈⟨ consʳ (zeroʳ p) ⟩
  0# ∷ []                   ≈⟨ zerosm≈zerosn ⟩
  []                        ∎

pIsZero⇒p*qIsZero : (q : Poly n) → IsZero p → IsZero (p * q)
pIsZero⇒p*qIsZero {n} {p = []} q [] = zerosIsZero (pred n)
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
    ≈⟨ +-congˡ (consˡ (R.*-cong a≈b c≈d)) ⟩
  (b *A d ∷ a · r) + p * (0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consʳ (·-cong a≈b r≈s)) ⟩
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
qIsZero⇒p*qIsZero {m} {q = []} p [] = ≈0⇒IsZero (zeroʳ p)
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

shift-distrib-+ : (p : Poly m) → (q : Poly n) →
                  shift (p + q) ≈ (shift p) + (shift q)
shift-distrib-+ p q = cons (R.sym (R.+-identityʳ 0#)) refl

*-identityʳ : (p : Poly n) → p * (1# ∷ []) ≈ p
*-identityʳ {0} [] = zerosm≈zerosn
*-identityʳ {suc n} (a ∷ p) = begin
  (a ∷ p) * (1# ∷ [])
    ≈⟨ cast-p≈p (cast-lem 1 n) ⟩
  (a *A 1# ∷ []) + (p * (0# ∷ 1# ∷ []))
    ≈⟨ +-congˡ (consˡ (R.*-identityʳ a)) ⟩
  (a ∷ []) + (p * (0# ∷ 1# ∷ []))
    ≈⟨ +-congʳ (*-distrib-shift p (1# ∷ [])) ⟩
  (a ∷ []) + (0# ∷ (p * (1# ∷ [])))
    ≈⟨ cons (R.+-identityʳ a) (+-identityˡ (p * (1# ∷ []))) ⟩
  a ∷ (p * (1# ∷ []))
    ≈⟨ consʳ (*-identityʳ p) ⟩
  a ∷ p ∎

*-identityˡ : (p : Poly n) → (1# ∷ []) * p ≈ p
*-identityˡ [] = refl
*-identityˡ {suc n} (a ∷ p) = begin
  (1# ∷ []) * (a ∷ p)
    ≈⟨ consʳ (cast-p≈p (ℕ.⊔-idem n)) ⟩
  1# · (a ∷ p) + [] * (0# ∷ a ∷ p)
    ≈⟨ +-identityʳ {m = pred (suc (suc n))} (1# · (a ∷ p) + []) ⟩
  1# · (a ∷ p) + []
    ≈⟨ +-identityʳ {m = 0} (1# · (a ∷ p)) ⟩
  1# · (a ∷ p)
    ≈⟨ cons (R.*-identityˡ a) (1·p≈p p) ⟩
  a ∷ p ∎

-- (0# ∷ 1# ∷ []) is the center of a polynomial ring
shiftp≈p*x :  (p : Poly n) → shift p ≈ p * (0# ∷ 1# ∷ [])
shiftp≈p*x [] = refl
shiftp≈p*x {suc n} (a ∷ p) = begin
 0# ∷ a ∷ p
   ≈⟨ cons (R.+-identityˡ 0#) (cons (R.+-identityʳ a) (+-identityˡ p)) ⟨
 (0# ∷ a ∷ []) + shift (shift p)
   ≈⟨ consʳ (consʳ (+-congʳ (*-identityʳ p))) ⟨
 (0# ∷ a ∷ []) + (shift (shift (p * (1# ∷ []))))
   ≈⟨ +-congʳ {p = 0# ∷ a ∷ []} (consʳ (*-distrib-shift p (1# ∷ []))) ⟨
 (0# ∷ a ∷ []) + shift (p * shift (1# ∷ []))
   ≈⟨ +-congʳ {p = 0# ∷ a ∷ []} (*-distrib-shift p (0# ∷ 1# ∷ [])) ⟨
 (0# ∷ a ∷ []) + p * shift (shift (1# ∷ []))
   ≈⟨ +-congˡ (cons (R.zeroʳ a) (consˡ (R.*-identityʳ a))) ⟨
 a · (0# ∷ 1# ∷ []) + p * (0# ∷ 0# ∷ 1# ∷ [])
   ≈⟨ cast-p≈p (cast-lem 2 n) ⟨
 (a ∷ p) * (0# ∷ 1# ∷ []) ∎

shiftp≈x*p : (p : Poly n) → shift p ≈ (0# ∷ 1# ∷ []) * p
shiftp≈x*p [] = consˡ (R.sym (R.trans (R.+-identityʳ (1# *A 0#)) (R.zeroʳ 1#)))
shiftp≈x*p {suc n} (a ∷ p) = begin
 0# ∷ a ∷ p
   ≈⟨ *-identityˡ (0# ∷ a ∷ p) ⟨
 (1# ∷ []) * (0# ∷ a ∷ p)
   ≈⟨ +-identityˡ {m = 0} ((1# ∷ []) * (0# ∷ a ∷ p)) ⟨
 [] + (1# ∷ []) * (0# ∷ a ∷ p)
   ≈⟨ +-identityˡ {m = 0} ((1# ∷ []) * (0# ∷ a ∷ p)) ⟩
 (1# ∷ []) * (0# ∷ a ∷ p)
   ≈⟨ +-idˡ (0# *A a ∷ 0# · p) ((1# ∷ []) * (0# ∷ a ∷ p))
      ((R.zeroˡ a) ∷ a≈0⇒a·pIsZero 0# p R.refl) ⟨
 0# · (a ∷ p) + (1# ∷ []) * (0# ∷ a ∷ p)
   ≈⟨ consʳ (cast-p≈p (ℕ.m≤n⇒m⊔n≡n (ℕ.n≤1+n n))) ⟨
 (0# ∷ 1# ∷ []) * (a ∷ p) ∎

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
    ≈⟨ +-congˡ (cons (R.sym (R.*-assoc a b c)) ·-assoc) ⟩
  (a *A b *A c ∷ ((a *A b) · q)) + a · (p * (0# ∷ c ∷ q))
    ≈⟨ +-congʳ (·-distrib-* p (0# ∷ c ∷ q) a) ⟩
  (a *A b) · (c ∷ q) + (a · p) * (0# ∷ c ∷ q)
    ≈⟨ cast-p≈p (cast-lem (suc n) m) ⟨
  (a · (b ∷ p)) * (c ∷ q)
    ∎

0∷[p*q]≈[0∷p]*q : (p : Poly m) → (q : Poly n) →
                  shift (p * q) ≈ (shift p) * q
0∷[p*q]≈[0∷p]*q {n = n} [] q = begin
  shift ([] * q)
    ≈⟨ consʳ zerosm≈zerosn ⟩
  shift []
    ≈⟨ IsZero⇒≈0 (All-p≈0∧q≈0⇒p+q≈0 (a≈0⇒a·pIsZero 0# q R.refl)
       (≈0⇒IsZero {m = n} zerosm≈zerosn)) ⟨
  0# · q + zeros (pred (suc n))
    ≈⟨ cast-p≈p (ℕ.⊔-idem (pred (1 ℕ.+ n))) ⟨
  shift [] * q   ∎
0∷[p*q]≈[0∷p]*q {m = suc m} {n = n} (a ∷ p) (q) = begin
  shift ((a ∷ p) * q)
    ≈⟨ *-distrib-shift (a ∷ p) q ⟨
  (a ∷ p) * shift q
    ≈⟨ cast-p≈p (cast-lem (suc n) m) ⟩
  a · shift q + p * (0# ∷ shift q)
    ≈⟨ +-idˡ (0# · q) (a · (0# ∷ q) + p * (0# ∷ 0# ∷ q))
       (a≈0⇒a·pIsZero 0# q R.refl) ⟨
  0# · q + (a · (0# ∷ q) + p * (0# ∷ 0# ∷ q))
    ≈⟨ +-congʳ (cast-p≈p (cast-lem (suc n) m)) ⟨
  0# · q + (a ∷ p) * (0# ∷ q)
    ≈⟨ cast-p≈p (cast-lem n (suc m)) ⟨
  shift (a ∷ p) * q ∎

*-distribˡ-+ : (p : Poly m) → (q : Poly n) → (r : Poly k) →
                p * (q + r) ≈ p * q + p * r
*-distribˡ-+ [] q r = begin
  [] * (q + r)
    ≈⟨ zerosm≈zerosn ⟩
  []
    ≈⟨ IsZero⇒≈0 (All-p≈0∧q≈0⇒p+q≈0 (≈0⇒IsZero refl) (≈0⇒IsZero refl)) ⟨
  [] * q + [] * r  ∎
*-distribˡ-+ {m = suc m} {n = n} {k = k} (a ∷ p) q r = begin
  (a ∷ p) * (q + r)
    ≈⟨ cast-p≈p (cast-lem (n ⊔ k) m) ⟩
  a · (q + r) + p * (0# ∷ q + r)
    ≈⟨ +-cong ·-dist (*-distrib-shift p (q + r)) ⟩
  (a · q + a · r) + (0# ∷ (p * (q + r)))
    ≈⟨ +-congʳ (consʳ (*-distribˡ-+ p q r)) ⟩
  (a · q + a · r) + (0# ∷ (p * q + p * r))
    ≈⟨ +-congʳ (consˡ (R.+-identityʳ 0#)) ⟨
  (a · q + a · r) + ((0# ∷ (p * q)) + (0# ∷ (p * r)))
    ≈⟨ middleFour (a · q) (a · r) (0# ∷ p * q) (0# ∷ p * r) ⟩
  ((a · q) + (0# ∷ (p * q))) + ((a · r) + (0# ∷ (p * r)))
    ≈⟨ +-cong (+-congʳ (*-distrib-shift p q)) (+-congʳ (*-distrib-shift p r)) ⟨
  (a · q + p * (0# ∷ q)) +  (a · r + p * (0# ∷ r))
    ≈⟨ +-cong (cast-p≈p (cast-lem n m)) (cast-p≈p (cast-lem k m)) ⟨
  (a ∷ p) * q + (a ∷ p) * r
    ∎

*-distribʳ-+ : (p : Poly m) → (q : Poly n) → (r : Poly k) →
               (q + r) * p ≈ (q * p) + (r * p)
*-distribʳ-+ {m = m} p [] [] = sym (+-identityʳ (zeros (m ℕ.∸ 1)))
*-distribʳ-+ {m = m} {k = suc k} p [] (c ∷ r) = begin
  ([] + (c ∷ r)) * p
    ≈⟨ cast-p≈p (cast-lem m k) ⟩
  c · p + r * (0# ∷ p)
    ≈⟨ cast-p≈p (cast-lem m k) ⟨
  (c ∷ r) * p
    ≈⟨ +-identityˡ ((c ∷ r) * p) ⟨
  [] * p + (c ∷ r) * p
    ∎
*-distribʳ-+ {m = m} {n = suc n} p (b ∷ q) [] = begin
  ((b ∷ q) + []) * p
    ≈⟨ cast-p≈p (cast-lem m n) ⟩
  b · p + q * (0# ∷ p)
    ≈⟨ cast-p≈p (cast-lem m n) ⟨
  (b ∷ q) * p
    ≈⟨ +-identityʳ ((b ∷ q) * p) ⟨
  (b ∷ q) * p + [] * p
  ∎
*-distribʳ-+ {m} {suc n} {suc k} p (b ∷ q) (c ∷ r) = begin
  ((b ∷ q) + (c ∷ r)) * p
    ≈⟨ cast-p≈p (cast-lem m (n ⊔ k)) ⟩
  (b +A c) · p + (q + r) * (0# ∷ p)
    ≈⟨ +-cong (·-distrib-+A b c p) (*-distribʳ-+ (0# ∷ p) q r) ⟩
  ((b · p) + (c · p)) + (q * (0# ∷ p) + r * (0# ∷ p))
    ≈⟨ middleFour (b · p) (c · p) (q * (0# ∷ p)) (r * (0# ∷ p)) ⟩
  (b · p + q * (0# ∷ p)) + (c · p + r * (0# ∷ p))
    ≈⟨ +-cong (cast-p≈p (cast-lem m n)) (cast-p≈p (cast-lem m k)) ⟨
  (b ∷ q) * p + (c ∷ r) * p
    ∎

*-assoc : (p : Poly m) → (q : Poly n) → (r : Poly k) →
          (p * q) * r ≈ p * (q * r)
*-assoc {n = n} {k} [] q r =  begin
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
    ≈⟨  +-congʳ step1 ⟨
  ((a · q) * r) + (0# ∷ (p * (q * r)))
    ≈⟨ +-congˡ (·-distrib-* q r a) ⟨
  (a · (q * r)) + (0# ∷ (p * (q * r)))
    ≈⟨ +-congʳ (*-distrib-shift p (q * r)) ⟨
  (a · (q * r)) + (p * (0# ∷ (q * r)))
    ≈⟨ cast-p≈p (cast-lem (pred (n ℕ.+ k)) m) ⟨
  (a ∷ p) * (q * r)
    ∎
    where
    step1 = begin
      0# ∷ (p * (q * r))
        ≈⟨ consʳ (*-assoc p q r) ⟨
      0# ∷ ((p * q) * r)
        ≈⟨ 0∷[p*q]≈[0∷p]*q (p * q) r ⟩
      (0# ∷ (p * q)) * r
        ≈⟨ cast-p≈p (cast-lem k (m ℕ.+ n ℕ.∸ 1)) ⟩
      (0# · r) + ((p * q) * (0# ∷ r))
        ≈⟨ +-congˡ (IsZero⇒≈0 (a≈0⇒a·pIsZero 0# r R.refl) ) ⟩
      zeros k + ((p * q) * (0# ∷ r))
        ≈⟨ +-congʳ (*-distrib-shift (p * q) r) ⟩
      zeros k + (0# ∷ ((p * q) * r))
        ≈⟨ +-congʳ (0∷[p*q]≈[0∷p]*q (p * q) r) ⟩
      zeros k + ((0# ∷ (p * q)) * r)
        ≈⟨ +-identityˡ ((0# ∷ (p * q)) * r) ⟩
      (0# ∷ (p * q)) * r
        ∎
        

