------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the binary representation of natural numbers
------------------------------------------------------------------------

module Data.Bin.Properties where

open import Data.Bin
open import Data.Digit using (Bit)
open import Data.Fin as Fin using (Fin; zero) renaming (suc to 1+_)
open import Data.Fin.Properties as FP using (bounded; strictTotalOrder)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (∷-injective)
open import Data.Nat
  using (ℕ; zero; z≤n; s≤s; ≤-pred)
  renaming (suc to 1+_; _+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties as NP
  using (≤-refl; _+-mono_; _*-mono_; n≤m+n; module ≤-Reasoning)
open import Data.Nat.Properties.Simple using (+-assoc)
open import Data.Product using (proj₁; proj₂)
open import Function using (_on_; _∘_)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; isEquivalence; resp₂)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- (Bin, _≡_) is a decidable setoid

1#-injective : ∀ {as bs} → as 1# ≡ bs 1# → as ≡ bs
1#-injective refl = refl

infix 4 _≟_ _≟LB_

_≟LB_ : Decidable (_≡_ {A = List Bit})
_≟LB_ []       []       = yes refl
_≟LB_ []       (_ ∷ _)  = no λ()
_≟LB_ (_ ∷ _) []        = no λ()
_≟LB_ (x ∷ xs) (y ∷ ys) with x FP.≟ y | xs ≟LB ys
... | _        | no xs≢ys = no (xs≢ys ∘ proj₂ ∘ ∷-injective)
... | no  x≢y  | _        = no (x≢y   ∘ proj₁ ∘ ∷-injective)
... | yes refl | yes refl = yes refl

_≟_ : Decidable {A = Bin} _≡_
0#    ≟ 0#    = yes refl
0#    ≟ bs 1# = no λ()
as 1# ≟ 0#    = no λ()
as 1# ≟ bs 1# with as ≟LB bs
... | yes refl  = yes refl
... | no  as≢bs = no (as≢bs ∘ 1#-injective)

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟_
  }

≡-decSetoid : DecSetoid _ _
≡-decSetoid = record
  { Carrier          = Bin
  ; _≈_              = _≡_
  ; isDecEquivalence = ≡-isDecEquivalence
  }

------------------------------------------------------------------------
-- (Bin _≡_ _<_) is a strict total order

<-trans : Transitive _<_
<-trans (less lt₁) (less lt₂) = less (NP.<-trans lt₁ lt₂)

<-asym : Asymmetric _<_
<-asym (less lt) (less gt) = NP.<-asym lt gt

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (less lt) = NP.<-irrefl refl lt

∷∙ : ∀ {a b as bs} → as 1# < bs 1# → (a ∷ as) 1# < (b ∷ bs) 1#
∷∙ {a} {b} {as} {bs} (less lt) = less (begin
  1+ (m₁ +ℕ n₁ *ℕ 2) ≤⟨ s≤s (≤-pred (bounded a) +-mono ≤-refl) ⟩
  1+ (1 +ℕ n₁ *ℕ 2)  ≡⟨ refl ⟩
  1+ n₁ *ℕ 2         ≤⟨ lt *-mono ≤-refl ⟩
  n₂ *ℕ 2            ≤⟨ n≤m+n m₂ (n₂ *ℕ 2) ⟩
  m₂ +ℕ n₂ *ℕ 2      ∎)
  where
  open ≤-Reasoning
  m₁ = Fin.toℕ a;   m₂ = Fin.toℕ b
  n₁ = toℕ (as 1#); n₂ = toℕ (bs 1#)
    
∙∷ : ∀ {a b bs} → Fin._<_ a b → (a ∷ bs) 1# < (b ∷ bs) 1#
∙∷ {a} {b} {bs} lt = less (begin
  1 +ℕ (m₁  +ℕ n *ℕ 2)  ≡⟨ sym (+-assoc 1 m₁ (n *ℕ 2)) ⟩
  (1 +ℕ m₁) +ℕ n *ℕ 2   ≤⟨ lt +-mono ≤-refl ⟩
  m₂  +ℕ n *ℕ 2   ∎)
  where
  open ≤-Reasoning
  m₁ = Fin.toℕ a; m₂ = Fin.toℕ b; n = toℕ (bs 1#)

1<[23] : ∀ {b} → [] 1# < (b ∷ []) 1#
1<[23] {b} = less (n≤m+n (Fin.toℕ b) 2)
  
1<2+ : ∀ {b bs} → [] 1# < (b ∷ bs) 1#
1<2+ {_} {[]}     = 1<[23]
1<2+ {_} {b ∷ bs} = <-trans 1<[23] (∷∙ {a = b} 1<2+)
  
0<1+ : ∀ {bs} → 0# < bs 1#
0<1+ {[]}     = less (s≤s z≤n)
0<1+ {b ∷ bs} = <-trans (less (s≤s z≤n)) 1<2+

<⇒≢ : ∀ {a b} → a < b → a ≢ b
<⇒≢ lt eq = asym⟶irr (resp₂ _<_) sym <-asym eq lt
  
<-cmp : Trichotomous _≡_ _<_
<-cmp 0#            0#            = tri≈ (<-irrefl refl) refl (<-irrefl refl)
<-cmp 0#            (_ 1#)        = tri< 0<1+ (<⇒≢ 0<1+) (<-asym 0<1+)
<-cmp (_ 1#)        0#            = tri> (<-asym 0<1+) (<⇒≢ 0<1+ ∘ sym) 0<1+
<-cmp ([] 1#)       ([] 1#)       = tri≈ (<-irrefl refl) refl (<-irrefl refl)
<-cmp ([] 1#)       ((b ∷ bs) 1#) = tri< 1<2+ (<⇒≢ 1<2+) (<-asym 1<2+)
<-cmp ((a ∷ as) 1#) ([] 1#)       = tri> (<-asym 1<2+) (<⇒≢ 1<2+ ∘ sym) 1<2+
<-cmp ((a ∷ as) 1#) ((b ∷ bs) 1#) with <-cmp (as 1#) (bs 1#)
... | tri<  lt ¬eq ¬gt = tri< (∷∙ lt)  (<⇒≢ (∷∙ lt)) (<-asym (∷∙ lt))
... | tri> ¬lt ¬eq  gt = tri> (<-asym (∷∙ gt)) (<⇒≢ (∷∙ gt) ∘ sym) (∷∙ gt)
... | tri≈ ¬lt refl ¬gt with FP.cmp a b
...   | tri≈ ¬lt′ refl ¬gt′ = tri≈ (<-irrefl refl) refl (<-irrefl refl)
...   | tri<  lt′ ¬eq  ¬gt′ = tri< (∙∷ lt′)  (<⇒≢ (∙∷ lt′)) (<-asym (∙∷ lt′))
...   | tri> ¬lt′ ¬eq  gt′  = tri> (<-asym (∙∷ gt′)) (<⇒≢ (∙∷ gt′) ∘ sym) (∙∷ gt′)

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { Carrier            = Bin
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }
