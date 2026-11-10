open import Algebra.Bundles
  using ( Magma; Semigroup; CommutativeSemigroup; Monoid
        ; CommutativeMonoid; Semiring)
  
module Algebra.Polynomial.Poly.Properties.Semiring 
  {ℓ₁ ℓ₂} (SR : Semiring ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw
open import Algebra.Consequences.Setoid using (comm∧assoc⇒middleFour)
import Algebra.Definitions as Def
open import Algebra.Polynomial.Poly.Base.Semiring SR
  using ( Poly; _+_; _*_; _·_; shift; _≈_; IsZero
        ; inject; []≈ ; ≈[]; cons; 0#; 1#; degree)
open import Algebra.Structures
  using ( IsMagma; IsSemigroup; IsCommutativeSemigroup; IsMonoid
        ; IsSemiring; IsCommutativeMonoid)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All ; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; suc; pred; _⊔_)
open import Data.Product using (_,_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Core using (cong)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary using (Dec; yes; no; contradiction)
open import Relation.Nullary.Construct.Add.Infimum
  using (_₋; ⊥₋; [_])

open Def _≈_

module A = Semiring SR
open A
  using ()
  renaming (Carrier to A)
 
private
  variable
    a b c d : A
    p q r s : Poly

-- _≈_ is an equivalence relation

zeros-unique : IsZero p → IsZero q → p ≈ q
zeros-unique [] [] = []≈ [] []
zeros-unique [] (a≈0 ∷ p≈0) = []≈ (_ ∷ _) (a≈0 ∷ p≈0)
zeros-unique (a≈0 ∷ p≈0) [] = ≈[] (_ ∷ _) (a≈0 ∷ p≈0)
zeros-unique (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = cons (A.trans a≈0 (A.sym b≈0)) (zeros-unique p≈0 q≈0)

IsZero-cong : IsZero p → p ≈ q → IsZero q
IsZero-cong [] ([]≈ q q≈0) = q≈0
IsZero-cong [] (≈[] p p≈0) = p≈0
IsZero-cong (a≈0 ∷ p≈0) (≈[] a∷p a∷p≈0) = []
IsZero-cong (a≈0 ∷ p≈0) (cons a≈b p≈q)
  = (A.trans (A.sym a≈b) a≈0) ∷ IsZero-cong p≈0 p≈q

refl : p ≈ p
refl {p = []} = []≈ [] []
refl {p = a ∷ p} = cons A.refl refl

sym : p ≈ q → q ≈ p
sym ([]≈ q q≈0) = ≈[] q q≈0
sym (≈[] p p≈0) = []≈ p p≈0
sym (cons a≈b p≈q) = cons (A.sym a≈b) (sym p≈q)

trans : p ≈ q → q ≈ r → p ≈ r
trans {r = r} ([]≈ q q≈0) q≈r = []≈ r (IsZero-cong q≈0 q≈r) 
trans (≈[] p p≈0) q≈r = zeros-unique p≈0 (IsZero-cong [] q≈r)
trans (cons a≈b p≈q) (≈[] q q≈0)
  = ≈[] _ (IsZero-cong q≈0 (sym (cons a≈b p≈q)))
trans (cons a≈b p≈q) (cons b≈c q≈r)
  = cons (A.trans a≈b b≈c) (trans p≈q q≈r)

consˡ : (a A.≈ b) → (a ∷ p) ≈ (b ∷ p)
consˡ a≈b = cons a≈b refl

consʳ : p ≈ q → (a ∷ p) ≈ (a ∷ q)
consʳ = cons A.refl
  
---------------------------------------------------
-- Equational reasoning for Polynomials

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

≈-setoid : Setoid _ _
≈-setoid = record
  { Carrier       = Poly
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

open module ≈-Reasoning = SetoidReasoning ≈-setoid

--Properties of zero polynomial

IsZero⇒p≈[] : IsZero p → p ≈ 0#
IsZero⇒p≈[] [] = refl
IsZero⇒p≈[] (a≈0 ∷ p≈0) = ≈[] (_) (a≈0 ∷ p≈0)

p≈[]⇒IsZero : p ≈ 0# → IsZero p
p≈[]⇒IsZero ([]≈ [] q≈0) = q≈0
p≈[]⇒IsZero (≈[] _ p≈0)   = p≈0

IsZero-∷⁺ : p ≈ 0# → IsZero (shift 1 p)
IsZero-∷⁺ ([]≈ [] refl) = A.refl ∷ refl
IsZero-∷⁺ (≈[] p p≈[]) = A.refl ∷ p≈[]

IsZero-shift⁺ : (n : ℕ) → IsZero p → IsZero (shift n p)
IsZero-shift⁺ ℕ.zero p≈0 = p≈0
IsZero-shift⁺ (suc n) p≈0 = A.refl ∷ IsZero-shift⁺ n p≈0

IsZero-shift⁻ : (n : ℕ) → IsZero (shift n p) → IsZero p
IsZero-shift⁻ ℕ.zero q≈0 = q≈0
IsZero-shift⁻ (suc n) (a≈0 ∷ q≈0) = IsZero-shift⁻ n q≈0

IsZero-unique : IsZero p → IsZero q → p ≈ q
IsZero-unique [] q≈0 = []≈ _ q≈0
IsZero-unique (a≈0 ∷ p≈0) [] = ≈[] (_ ∷ _) (a≈0 ∷ p≈0)
IsZero-unique (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = cons (A.trans a≈0 (A.sym b≈0))
         (trans (IsZero-unique p≈0 p≈0) (IsZero-unique p≈0 q≈0))

a∷p≈[]⇒a≈0 : (a ∷ p) ≈ 0# → a A.≈ A.0#
a∷p≈[]⇒a≈0 (≈[] a∷p (a≈0 ∷ p≈0)) = a≈0

p≈[]⇒0∷p≈p : p ≈ 0# → p ≈ (shift 1 p)
p≈[]⇒0∷p≈p ([]≈ [] refl) = []≈ (A.0# ∷ []) (A.refl ∷ refl)
p≈[]⇒0∷p≈p (≈[] [] p≈[]) = []≈ (A.0# ∷ []) (A.refl ∷ p≈[])
p≈[]⇒0∷p≈p (≈[] (a ∷ p) (a≈0 ∷ p≈0))
  = IsZero-unique (a≈0 ∷ p≈0) (A.refl ∷ a≈0 ∷ p≈0)

IsZero-+⁺ : IsZero p → IsZero q → IsZero (p + q)
IsZero-+⁺ [] [] = []
IsZero-+⁺ [] (b≈0 ∷ q≈0) = b≈0 ∷ q≈0
IsZero-+⁺ (a≈0 ∷ p≈0) [] = a≈0 ∷ p≈0
IsZero-+⁺ (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = A.trans (A.+-cong a≈0 b≈0) (A.+-identityʳ A.0#) ∷ IsZero-+⁺ p≈0 q≈0

-------------------------------------------
--Properties of polynomial addition

+-comm : Commutative _+_
+-comm [] [] = refl
+-comm [] (a ∷ p) = refl
+-comm (a ∷ p) [] = refl
+-comm (a ∷ p) (b ∷ q) = cons (A.+-comm a b) (+-comm p q)

+-idʳ : (p : Poly) → (q : Poly) → IsZero q → p + q ≈ p
+-idʳ [] q [] = refl
+-idʳ (a ∷ p) q [] = refl
+-idʳ [] (a ∷ q) (a≈0 ∷ q≈0) = ≈[] (a ∷ q) (a≈0 ∷ q≈0)
+-idʳ (a ∷ p) (b ∷ q) (b≈0 ∷ q≈0)
  = cons (A.trans (A.+-congˡ b≈0) (A.+-identityʳ a)) (+-idʳ p q q≈0)

+-idˡ : (p : Poly) → (q : Poly) → IsZero p → p + q ≈ q
+-idˡ p q p≈0 = begin
  p + q  ≈⟨ +-comm p q ⟩
  q + p  ≈⟨ +-idʳ q p p≈0 ⟩
  q ∎

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ p = +-idˡ [] p []

+-identityʳ : RightIdentity 0# _+_
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
  = cons (A.+-cong a≈b c≈d) (+-cong p≈q r≈s)

+-congˡ : p ≈ q → p + r ≈ q + r
+-congˡ p≈q = +-cong p≈q refl

+-congʳ : q ≈ r → p + q ≈ p + r
+-congʳ q≈r = +-cong refl q≈r

+-assoc : Associative _+_
+-assoc [] q r =  begin
  [] + q + r ≈⟨ +-congˡ (+-idˡ [] q []) ⟩
  q + r        ≈⟨ +-idˡ [] (q + r) [] ⟨
  [] + (q + r) ∎
+-assoc (a ∷ p) [] r = +-congʳ (sym (+-idˡ [] r []))
+-assoc (a ∷ p) (b ∷ q) [] = refl
+-assoc (a ∷ p) (b ∷ q) (c ∷ r)
  = cons (A.+-assoc a b c) (+-assoc p q r)

middleFour : (p q r w : Poly) → (p + q) + (r + w) ≈ (p + r) + (q + w)   
middleFour = comm∧assoc⇒middleFour ≈-setoid {_∙_ = _+_}
             +-cong +-comm +-assoc 

--------------------------------------------------------------------
-- Properties of polynomial shifting

·-distrib-shift : (a : A) → (p : Poly) → a · (shift 1 p) ≈ shift 1 (a · p)
·-distrib-shift a [] = cons (A.zeroʳ a) (refl)
·-distrib-shift a (b ∷ p) = consˡ (A.zeroʳ a)

----------------------------------------------------------------
-- Properties of polynomial scaling

a·p≈a∷[]*p : (a : A) → (p : Poly) → a · p ≈ (a ∷ []) * p
a·p≈a∷[]*p a [] = refl
a·p≈a∷[]*p a (b ∷ p) = begin
  a · (b ∷ p)
    ≈⟨ +-idʳ (a · (b ∷ p)) ([] * (A.0# ∷ b ∷ p)) [] ⟨
  (a ∷ []) * (b ∷ p) ∎

pIsZero⇒a·pIsZero : (a : A) → (p : Poly) → IsZero p → IsZero (a · p) 
pIsZero⇒a·pIsZero a p [] =  []
pIsZero⇒a·pIsZero a (b ∷ p) (b≈0 ∷ p≈0)
  = (A.trans (A.*-congˡ b≈0) (A.zeroʳ a)) ∷ pIsZero⇒a·pIsZero a p p≈0

IsZero-·⁺ : (p : Poly) → IsZero (A.0# · p)
IsZero-·⁺ [] = []
IsZero-·⁺ (a ∷ p) = A.zeroˡ a ∷ IsZero-·⁺ p

·-cong : a A.≈ b → p ≈ q → a · p ≈ b · q
·-cong {a = a} {b = b} _ ([]≈ q q≈0)
  = sym (≈[] (b · q) (pIsZero⇒a·pIsZero b q q≈0))
·-cong {a = a} {b = b} _ (≈[] p p≈0)
  = sym ([]≈ (a · p) (pIsZero⇒a·pIsZero a p p≈0))
·-cong {a = a} {b = b} c≈d (cons a≈b p≈q)
  = cons (A.*-cong c≈d a≈b) (·-cong c≈d p≈q)

·-congˡ : a A.≈ b → a · p ≈ b · p
·-congˡ a≈b  = ·-cong a≈b refl

·-congʳ : p ≈ q → a · p ≈ a · q
·-congʳ = ·-cong A.refl

0·p≈p : (p : Poly) → A.0# · p ≈ 0#
0·p≈p p = IsZero⇒p≈[] (IsZero-·⁺ p)

1·p≈p : (p : Poly) → A.1# · p ≈ p
1·p≈p [] = refl
1·p≈p (a ∷ p) = cons (A.*-identityˡ a) (1·p≈p p)

·-dist : a · (p + q) ≈ (a · p) + (a · q)
·-dist {p = []} {q = []} = refl
·-dist {p = []} {q = b ∷ q} = refl
·-dist {p = b ∷ p} {q = []} = refl
·-dist {a = a} {p = b ∷ p} {q = c ∷ q} = cons (A.distribˡ a b c) ·-dist

·-assoc : a · (b · p) ≈ (a A.* b) · p
·-assoc {p = []} = refl
·-assoc {a = a} {b = b} {p = c ∷ p} = cons (A.sym (A.*-assoc a b c)) ·-assoc

a·-cong : p ≈ q → a · p ≈ a · q
a·-cong = ·-cong A.refl

+-distribˡ-⊔ : (a b : A) → (p : Poly) → (a A.+ b) · p ≈ a · p + b · p
+-distribˡ-⊔ a b [] = refl
+-distribˡ-⊔ a b (c ∷ p) = cons (A.distribʳ c a b) (+-distribˡ-⊔ a b p)

-----------------------------------------------------------------
-- Properties of polynomial multiplication

shift-*ʳ : (p q : Poly) → shift 1 (p * q) ≈ p * (shift 1 q)
shift-*ʳ [] q = ≈[] (A.0# ∷ []) (A.refl ∷ [])
shift-*ʳ (a ∷ p) q = begin
  A.0# ∷ ((a ∷ p) * q)
    ≈⟨ consˡ (A.+-identityˡ A.0#) ⟨
  (A.0# ∷ a · q) + (A.0# ∷ (p * (A.0# ∷ q)))
    ≈⟨ +-congʳ (shift-*ʳ p (A.0# ∷ q)) ⟩
  (A.0# ∷ a · q) + p * (A.0# ∷ A.0# ∷ q)
    ≈⟨ +-congˡ (consˡ (A.zeroʳ a)) ⟨
  (a ∷ p) * (A.0# ∷ q)
    ∎

shift-*ˡ : (p q : Poly) → shift 1 (p * q) ≈ (shift 1 p) * q
shift-*ˡ p q = begin
  shift 1 (p * q)
    ≈⟨ shift-*ʳ p q ⟩
  p * (shift 1 q)
    ≈⟨ +-idˡ (A.0# · q) (p * shift 1 q) ((IsZero-·⁺ q)) ⟨
  (shift 1 p) * q
    ∎
    
IsZero-*ˡ⁺ : (q : Poly) → IsZero p → IsZero (p * q)
IsZero-*ˡ⁺ q [] = []
IsZero-*ˡ⁺ {p = a ∷ p} q (a≈0 ∷ p≈0)
  = IsZero-+⁺ (p≈[]⇒IsZero (trans (·-congˡ a≈0) (0·p≈p q)))
    (IsZero-*ˡ⁺ (shift 1 q) p≈0)

IsZero-*ʳ⁺ : (q : Poly) → IsZero p → IsZero (q * p)
IsZero-*ʳ⁺ [] p≈0 = []
IsZero-*ʳ⁺ {p = p} (b ∷ q) p≈0
  = IsZero-+⁺ (pIsZero⇒a·pIsZero b p p≈0)
    (IsZero-*ʳ⁺ q (A.refl ∷ p≈0))

p≈[]⇒p*q≈[] : (q : Poly) → p ≈ [] → p * q ≈ []
p≈[]⇒p*q≈[] q p≈[]
  = IsZero⇒p≈[] (IsZero-*ˡ⁺ q (p≈[]⇒IsZero p≈[]))

p≈[]⇒q*p≈[] : (q : Poly) → p ≈ [] → q * p ≈ []
p≈[]⇒q*p≈[] q p≈[]
  = IsZero⇒p≈[] (IsZero-*ʳ⁺ q (p≈[]⇒IsZero p≈[]))

zeroˡ : (p : Poly) → 0# * p ≈ 0#
zeroˡ p = refl

zeroʳ : (p : Poly) → p * [] ≈ []
zeroʳ [] = refl
zeroʳ (a ∷ p) = begin
  (a ∷ p) * []
    ≈⟨ +-idˡ [] (p * (A.0# ∷ [])) [] ⟩
  p * (A.0# ∷ [])
    ≈⟨ ≈[] (p * (A.0# ∷ [])) (IsZero-*ʳ⁺ p (A.refl ∷ [])) ⟩
  []
  ∎

*-cong : p ≈ q → r ≈ s → p * r ≈ q * s
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
  (a A.* c ∷ a · r) + p * (A.0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consˡ (A.*-cong a≈b c≈d)) ⟩
  (b A.* d ∷ a · r) + p * (A.0# ∷ c ∷ r)
    ≈⟨ +-congˡ (consʳ (·-cong a≈b r≈s)) ⟩
  (b A.* d ∷ b · s) + p * (A.0# ∷ c ∷ r)
    ≈⟨ +-congʳ (*-cong p≈q (consʳ (cons c≈d r≈s))) ⟩
  (b A.* d ∷ b · s) + q * (A.0# ∷ d ∷ s)
    ≈⟨ refl ⟩
  (b ∷ q) * (d ∷ s)
    ∎

*-congʳ : q ≈ r → p * q ≈ p * r
*-congʳ {p = p} q≈r = *-cong {p = p} refl q≈r

*-congˡ : p ≈ q → p * r ≈ q * r
*-congˡ p≈q = *-cong p≈q refl

shift-+ : (p : Poly) → (q : Poly) →
                  shift 1 (p + q) ≈ (shift 1 p) + (shift 1 q)
shift-+ p q = cons (A.sym (A.+-identityʳ A.0#)) refl

*-identityʳ : (p : Poly) → p * 1# ≈ p
*-identityʳ [] = zeroˡ []
*-identityʳ (a ∷ p) = begin
  (a ∷ p) * (1#)
    ≈⟨ refl ⟩
  (a A.* A.1# ∷ []) + (p * (A.0# ∷ 1#))
    ≈⟨ +-congˡ (consˡ (A.*-identityʳ a)) ⟩
  (a ∷ []) + (p * (A.0# ∷ 1#))
    ≈⟨ +-congʳ (shift-*ʳ p 1#) ⟨
  (a ∷ []) + (A.0# ∷ (p * (1#)))
    ≈⟨ cons (A.+-identityʳ a) (+-identityˡ (p * (1#))) ⟩
  a ∷ (p * (1#))
    ≈⟨ consʳ (*-identityʳ p) ⟩
  a ∷ p ∎

*-identityˡ : (p : Poly) → 1# * p ≈ p
*-identityˡ [] = refl
*-identityˡ (a ∷ p) = begin
  1# * (a ∷ p)
    ≈⟨ consʳ refl ⟩
  A.1# · (a ∷ p) + [] * (A.0# ∷ a ∷ p)
    ≈⟨ +-identityʳ (A.1# · (a ∷ p) + []) ⟩
  A.1# · (a ∷ p) + []
    ≈⟨ +-identityʳ  (A.1# · (a ∷ p)) ⟩
  A.1# · (a ∷ p)
    ≈⟨ cons (A.*-identityˡ a) (1·p≈p p) ⟩
  a ∷ p ∎

shiftp≈p*x :  (p : Poly) → shift 1 p ≈ p * (shift 1 1#)
shiftp≈p*x [] = sym (begin
  [] * (A.0# ∷ 1#)
    ≈⟨ refl ⟩
  []
    ≈⟨ p≈[]⇒0∷p≈p refl ⟩
  A.0# ∷ [] ∎)
shiftp≈p*x (a ∷ p) = begin
 A.0# ∷ a ∷ p
   ≈⟨ cons (A.+-identityˡ A.0#) (cons (A.+-identityʳ a) (+-identityˡ p)) ⟨
 (A.0# ∷ a ∷ []) + shift 1 (shift 1 p)
   ≈⟨ consʳ (consʳ (+-congʳ (*-identityʳ p))) ⟨
 (A.0# ∷ a ∷ []) + (shift 1 (shift 1 (p * 1#)))
   ≈⟨ +-congʳ {p = A.0# ∷ a ∷ []} (consʳ (shift-*ʳ p 1#)) ⟩
 (A.0# ∷ a ∷ []) + shift 1 (p * shift 1 1#)
   ≈⟨ +-congʳ {p = A.0# ∷ a ∷ []} (shift-*ʳ p (shift 1 1#)) ⟩
 (A.0# ∷ a ∷ []) + p * shift 1 (shift 1 1#)
   ≈⟨ +-congˡ (cons (A.zeroʳ a) (consˡ (A.*-identityʳ a))) ⟨
 a · (A.0# ∷ 1#) + p * (A.0# ∷ A.0# ∷ 1#)
   ≈⟨ refl ⟨
 (a ∷ p) * (A.0# ∷ 1#) ∎

shiftp≈x*p : (p : Poly) → shift 1 p ≈ (shift 1 1#) * p
shiftp≈x*p [] = begin
  A.0# ∷ []
    ≈⟨ p≈[]⇒0∷p≈p refl ⟨
  []
    ≈⟨ zeroʳ (A.0# ∷ 1#) ⟨
  (A.0# ∷ 1#) * []
    ∎
shiftp≈x*p (a ∷ p) = begin
  A.0# ∷ a ∷ p
    ≈⟨ 1·p≈p (A.0# ∷ a ∷ p) ⟨
  A.1# · (A.0# ∷ a ∷ p)
    ≈⟨ +-identityʳ (A.1# · (A.0# ∷ a ∷ p)) ⟨
  A.1# · (A.0# ∷ a ∷ p) + []
    ≈⟨ refl ⟨
  1# * (A.0# ∷ a ∷ p)
    ≈⟨ +-idˡ (A.0# · (a ∷ p)) (1# * (A.0# ∷ a ∷ p))
      (IsZero-·⁺ (a ∷ p))⟨
  (A.0# · (a ∷ p)) + (1# * (A.0# ∷ a ∷ p))
    ≈⟨ refl ⟨
  (A.0# ∷ 1#) * (a ∷ p)
    ∎

·-distrib-* : (p q : Poly) → (a : A) → a · (p * q) ≈ (a · p) * q
·-distrib-* [] q a = refl
·-distrib-* (b ∷ p) [] a = begin
   a · ((b ∷ p) * [])
    ≈⟨ a·-cong ( +-idʳ [] (p * (A.0# ∷ []))
      (IsZero-*ʳ⁺ p (IsZero-∷⁺ refl))) ⟩
  []
    ≈⟨ zeroʳ (a · (b ∷ p)) ⟨
  (a · (b ∷ p)) * []
    ∎
·-distrib-* (b ∷ p) (c ∷ q) a = begin
  a · ((b ∷ p) * (c ∷ q))
    ≈⟨ refl ⟩
  a · ((b · (c ∷ q)) + (p * (A.0# ∷ c ∷ q)))
    ≈⟨ ·-dist ⟩
  a · (b A.* c ∷ (b · q)) + a · (p * (A.0# ∷ c ∷ q))
    ≈⟨ +-congˡ (cons (A.sym (A.*-assoc a b c)) ·-assoc) ⟩
  (a A.* b A.* c ∷ ((a A.* b) · q)) + a · (p * (A.0# ∷ c ∷ q))
    ≈⟨ +-congʳ (·-distrib-* p (A.0# ∷ c ∷ q) a) ⟩
  (a A.* b) · (c ∷ q) + (a · p) * (A.0# ∷ c ∷ q)
    ≈⟨ refl ⟩
  (a · (b ∷ p)) * (c ∷ q)
    ∎
 
*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ [] q r = begin
  [] * (q + r) ≈⟨ zeroˡ (q + r) ⟩
  [] ≈⟨ refl ⟩
  [] * q + [] * r ∎
*-distribˡ-+ (a ∷ p) q r = begin
   (a ∷ p) * (q + r)
    ≈⟨ refl ⟩
  a · (q + r) + p * (A.0# ∷ q + r)
    ≈⟨ +-cong ·-dist (sym (shift-*ʳ p (q + r))) ⟩
  (a · q + a · r) + (A.0# ∷ (p * (q + r)))
    ≈⟨ +-congʳ (consʳ (*-distribˡ-+ p q r)) ⟩
  (a · q + a · r) + (A.0# ∷ (p * q + p * r))
    ≈⟨ +-congʳ (consˡ (A.+-identityʳ A.0#)) ⟨
  (a · q + a · r) + ((A.0# ∷ (p * q)) + (A.0# ∷ (p * r)))
    ≈⟨ middleFour (a · q) (a · r) (A.0# ∷ p * q) (A.0# ∷ p * r) ⟩
  ((a · q) + (A.0# ∷ (p * q))) + ((a · r) + (A.0# ∷ (p * r)))
    ≈⟨ +-cong (+-congʳ (shift-*ʳ p q)) (+-congʳ (shift-*ʳ p r)) ⟩
  (a · q + p * (A.0# ∷ q)) +  (a · r + p * (A.0# ∷ r))
    ≈⟨ refl ⟨
  (a ∷ p) * q + (a ∷ p) * r
    ∎

*-distribʳ-+ : _*_ DistributesOverʳ _+_
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
  (b A.+ c) · p + (q + r) * (A.0# ∷ p)
    ≈⟨ +-cong (+-distribˡ-⊔ b c p) (*-distribʳ-+ (A.0# ∷ p) q r) ⟩
  ((b · p) + (c · p)) + (q * (A.0# ∷ p) + r * (A.0# ∷ p))
    ≈⟨ middleFour (b · p) (c · p) (q * (A.0# ∷ p)) (r * (A.0# ∷ p)) ⟩
  (b · p + q * (A.0# ∷ p)) + (c · p + r * (A.0# ∷ p))
    ≈⟨ refl ⟨
  (b ∷ q) * p + (c ∷ r) * p
    ∎

*-assoc : Associative _*_ 
*-assoc [] q r = refl
*-assoc (a ∷ p) q r = begin
  ((a ∷ p) * q) * r
    ≡⟨⟩
  ((a · q) + (p * (A.0# ∷ q))) * r
    ≈⟨ *-congˡ (+-congʳ {p = a · q} (shift-*ʳ p q)) ⟨
  ((a · q) + (A.0# ∷ (p * q))) * r
    ≈⟨ *-distribʳ-+ r (a · q) (A.0# ∷ p * q) ⟩
  ((a · q) * r) + ((A.0# ∷ (p * q)) * r)
    ≈⟨ +-congʳ (shift-*ˡ (p * q) r) ⟨
  ((a · q) * r) + (A.0# ∷ ((p * q) * r))
    ≈⟨ +-congʳ (consʳ (*-assoc p q r)) ⟩
  ((a · q) * r) + (A.0# ∷ (p * (q * r)))
    ≈⟨ +-cong (sym (·-distrib-* q r a)) (shift-*ʳ p (q * r)) ⟩
  (a · (q * r)) + (p * (A.0# ∷ (q * r)))
    ≈⟨ refl ⟩
  (a ∷ p) * (q * r)
    ∎

-------------------------------------------------------------
-- Properties of polynomial degree

module _ (_≟0 : ∀ a → Dec (a A.≈ A.0#)) where

  IsZero⇒deg≡⊥₋ : ∀ {p} → IsZero p → degree _≟0 p ≡ ⊥₋
  IsZero⇒deg≡⊥₋ [] = Eq.refl
  IsZero⇒deg≡⊥₋ {a ∷ p} (a≈0 ∷ p≈0) 
    rewrite IsZero⇒deg≡⊥₋ p≈0 with a ≟0
  ... | yes _   = Eq.refl
  ... | no ¬a≈0 = contradiction a≈0 ¬a≈0

  deg≡⊥₋⇒IsZero : ∀ {p} → degree _≟0 p ≡ ⊥₋ → IsZero p
  deg≡⊥₋⇒IsZero {[]} eq = []
  deg≡⊥₋⇒IsZero {a ∷ p} eq with degree _≟0 p in taildeg
  ... | [ n ] with () <- eq
  ... | ⊥₋ with a ≟0
  ...   | yes a≈0 = a≈0 ∷ deg≡⊥₋⇒IsZero {p} taildeg
  ...   | no _ with () <- eq

  deg-cong : ∀ {p q} → p ≈ q → degree _≟0 p ≡ degree _≟0 q
  deg-cong ([]≈ q []≈q) = Eq.sym (IsZero⇒deg≡⊥₋ []≈q)
  deg-cong (≈[] p p≈[]) = IsZero⇒deg≡⊥₋ p≈[]
  deg-cong {a ∷ p} {b ∷ q} (cons a≈b p≈q)
    rewrite deg-cong p≈q with degree _≟0 q
  ... | [ n ] = Eq.refl
  ... | ⊥₋ with a ≟0 | b ≟0
  ...   | yes _   | yes _    = Eq.refl
  ...   | no _    | no  _    = Eq.refl
  ...   | yes a≈0 | no  ¬b≈0 = contradiction (A.trans (A.sym a≈b) a≈0) ¬b≈0
  ...   | no ¬a≈0 | yes  b≈0 = contradiction (A.trans a≈b b≈0) ¬a≈0

--------------------------------------------------------------
-- Algebraic properties of addition
+-identity : Identity 0# _+_
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

+-isMonoid : IsMonoid _≈_ _+_ 0#
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity
  }

+-isCommutativeMonoid : IsCommutativeMonoid _≈_ _+_ 0#
+-isCommutativeMonoid = record
  { isMonoid = +-isMonoid
  ; comm = +-comm
  }

---------------------------------------------------------------
-- Additive raw bundles
+-rawMagma : RawMagma _ _
+-rawMagma = record
  { Carrier = Poly
  ; _≈_ = _≈_
  ; _∙_ = _+_
  }

+-*-rawSemiring : RawSemiring _ _
+-*-rawSemiring = record
  { Carrier = Poly
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0#
  ; 1# = 1#
  }

-- Additive bundles

+-magma : Magma _ _
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup _ _
+-semigroup = record
  { isSemigroup =  +-isSemigroup
  }

+-commutativeSemigroup : CommutativeSemigroup _ _
+-commutativeSemigroup = record
  {  isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-monoid : Monoid _ _
+-monoid = record
  { isMonoid =   +-isMonoid
  }

+-commutativeMonoid : CommutativeMonoid _ _
+-commutativeMonoid = record
  { isCommutativeMonoid =  +-isCommutativeMonoid
  }

*-identity : Identity 1# _*_
*-identity =  *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero 0# _*_
*-zeroˡ p = zeroˡ p

*-zeroʳ : RightZero 0# _*_
*-zeroʳ p = zeroʳ p

*-zero : Zero 0# _*_
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

*-isMonoid : IsMonoid _≈_ _*_ 1#
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity = *-identity
  }

+-*-isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#
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

*-magma :  Magma _ _
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup _ _
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-monoid : Monoid _ _
*-monoid = record
  { isMonoid = *-isMonoid
  }

+-*-semiring : Semiring _ _
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }



