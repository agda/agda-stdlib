------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the binary representation of natural numbers
------------------------------------------------------------------------

module Data.Bin.Properties where

open import Data.Bin
open import Data.Digit using (Bit; fromDigits)
open import Data.Fin as Fin using () renaming (zero to 0b; suc to sucF)
open import Data.Fin.Properties as FinP using (decSetoid; prop-toℕ-≤)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (∷-injective)
open import Data.Nat using (ℕ; zero; z≤n; s≤s; ≤-pred; _∸_)
            renaming (suc to 1+_; _+_ to _+ℕ_; _*_ to _*ℕ_;
                      _<_ to _<ℕ_; _>_ to _>ℕ_; _≤_ to _≤ℕ_; _≰_ to _≰ℕ_
                     )
open import Data.Nat.DivMod as DM using (DivMod; _divMod_; _div_;
                                                           half-n=n-div-2)
open import Data.Nat.Properties as NP using
     (m+n∸n≡m; n≤m+n; _*-mono_; module ≤-Reasoning; natEquiv; natDTO; tail0;
      1*; +cong₁; +cong₂; suc>0; ≤0→=0; <→≢; >→≢; Even; odd-suc; even-2*;
      half; half-n*2; monot-half; half-suc-n≤n
     )
open import Data.Product using (proj₁; proj₂; _×_; _,_; ∃)
open import Function using (_∘_; _$_; case_of_; flip)
open import Relation.Binary renaming (Decidable to Decidable₂)
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≢_)
open import Relation.Nullary using (yes; no; ¬_)

open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary.EqReasoning as EqR
open import Data.Empty using (⊥-elim)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open PE.≡-Reasoning renaming (_≡⟨_⟩_ to _≡[_]_; begin_ to ≡begin_;
                                                                _∎ to _≡end)
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                          _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)




------------------------------------------------------------------------
-- (Bin, _≡_) is a decidable setoid

1#-injective : ∀ {as bs} → as 1# ≡ bs 1# → as ≡ bs
1#-injective PE.refl = PE.refl

infix 4 _≟_ _≟LB_

_≟LB_ : Decidable₂ (_≡_ {A = List Bit})
_≟LB_ []       []       = yes PE.refl
_≟LB_ []       (_ ∷ _)  = no λ()
_≟LB_ (_ ∷ _) []        = no λ()
_≟LB_ (x ∷ xs) (y ∷ ys) with FinP._≟_ x y | xs ≟LB ys
... | _           | no xs≢ys = no (xs≢ys ∘ proj₂ ∘ ∷-injective)
... | no  x≢y     | _        = no (x≢y   ∘ proj₁ ∘ ∷-injective)
... | yes PE.refl | yes PE.refl = yes PE.refl

_≟_ : Decidable₂ {A = Bin} _≡_
0#    ≟ 0#    = yes PE.refl
0#    ≟ bs 1# = no λ()
as 1# ≟ 0#    = no λ()
as 1# ≟ bs 1# with as ≟LB bs
... | yes PE.refl  = yes PE.refl
... | no  as≢bs    = no (as≢bs ∘ 1#-injective)

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = record
  { isEquivalence = PE.isEquivalence
  ; _≟_           = _≟_
  }

≡-decSetoid : DecSetoid _ _
≡-decSetoid = PE.decSetoid _≟_

------------------------------------------------------------------------
-- (Bin _≡_ _<_) is a strict total order

<-trans : Transitive _<_
<-trans (less lt₁) (less lt₂) = less (NP.<-trans lt₁ lt₂)

<-asym : Asymmetric _<_
<-asym (less lt) (less gt) = NP.<-asym lt gt

<-irrefl : Irreflexive _≡_ _<_
<-irrefl PE.refl (less lt) = NP.<-irrefl PE.refl lt

∷ʳ-mono-< : ∀ {a b as bs} → as 1# < bs 1# → (a ∷ as) 1# < (b ∷ bs) 1#
∷ʳ-mono-< {a} {b} {as} {bs} (less lt) = less (≤begin
  1+ (m₁ +ℕ n₁ *ℕ 2)  ≤[ s≤s (NP.+-mono-≤
                             (≤-pred (FinP.bounded a)) NP.≤-refl) ]
  1+ (1 +ℕ n₁ *ℕ 2)  ≡≤[ PE.refl ]
  1+ n₁ *ℕ 2          ≤[ NP.*-mono-≤ lt NP.≤-refl ]
  n₂ *ℕ 2             ≤[ n≤m+n m₂ (n₂ *ℕ 2) ]
  m₂ +ℕ n₂ *ℕ 2      ≤end)
  where
  m₁ = Fin.toℕ a;   m₂ = Fin.toℕ b
  n₁ = toℕ (as 1#); n₂ = toℕ (bs 1#)

∷ˡ-mono-< : ∀ {a b bs} → a Fin.< b → (a ∷ bs) 1# < (b ∷ bs) 1#
∷ˡ-mono-< {a} {b} {bs} lt = less (≤begin
  1 +ℕ (m₁  +ℕ n *ℕ 2)  ≡≤[ PE.sym (NP.+-assoc 1 m₁ (n *ℕ 2)) ]
  (1 +ℕ m₁) +ℕ n *ℕ 2    ≤[ NP.+-mono-≤ lt NP.≤-refl ]
  m₂  +ℕ n *ℕ 2   ≤end)
  where
  m₁ = Fin.toℕ a; m₂ = Fin.toℕ b; n = toℕ (bs 1#)

1<[23] : ∀ {b} → [] 1# < (b ∷ []) 1#
1<[23] {b} = less (n≤m+n (Fin.toℕ b) 2)

1<2+ : ∀ {b bs} → [] 1# < (b ∷ bs) 1#
1<2+ {_} {[]}     = 1<[23]
1<2+ {_} {b ∷ bs} = <-trans 1<[23] (∷ʳ-mono-< {a = b} 1<2+)

0<1+ : ∀ {bs} → 0# < bs 1#
0<1+ {[]}     = less (s≤s z≤n)
0<1+ {b ∷ bs} = <-trans (less (s≤s z≤n)) 1<2+

<⇒≢ : ∀ {a b} → a < b → a ≢ b
<⇒≢ lt eq = asym⟶irr (PE.resp₂ _<_) PE.sym <-asym eq lt

<-cmp : Trichotomous _≡_ _<_
<-cmp 0#            0#            = tri≈ (<-irrefl PE.refl) PE.refl
                                                      (<-irrefl PE.refl)
<-cmp 0#            (_ 1#)        = tri< 0<1+ (<⇒≢ 0<1+) (<-asym 0<1+)
<-cmp (_ 1#)        0#            = tri> (<-asym 0<1+) (<⇒≢ 0<1+ ∘ PE.sym)
                                                                   0<1+
<-cmp ([] 1#)       ([] 1#)       = tri≈ (<-irrefl PE.refl) PE.refl
                                                            (<-irrefl PE.refl)
<-cmp ([] 1#)       ((b ∷ bs) 1#) = tri< 1<2+ (<⇒≢ 1<2+) (<-asym 1<2+)
<-cmp ((a ∷ as) 1#) ([] 1#)       = tri> (<-asym 1<2+) (<⇒≢ 1<2+ ∘ PE.sym)
                                                                      1<2+
<-cmp ((a ∷ as) 1#) ((b ∷ bs) 1#) with <-cmp (as 1#) (bs 1#)
... | tri<  lt ¬eq ¬gt =
  tri< (∷ʳ-mono-< lt)  (<⇒≢ (∷ʳ-mono-< lt)) (<-asym (∷ʳ-mono-< lt))
... | tri> ¬lt ¬eq  gt =
  tri> (<-asym (∷ʳ-mono-< gt)) (<⇒≢ (∷ʳ-mono-< gt) ∘ PE.sym) (∷ʳ-mono-< gt)
... | tri≈ ¬lt PE.refl ¬gt with FinP.cmp a b
...   | tri≈ ¬lt′ PE.refl ¬gt′ =
  tri≈ (<-irrefl PE.refl) PE.refl (<-irrefl PE.refl)
...   | tri<  lt′ ¬eq  ¬gt′ =
  tri< (∷ˡ-mono-< lt′)  (<⇒≢ (∷ˡ-mono-< lt′)) (<-asym (∷ˡ-mono-< lt′))
...   | tri> ¬lt′ ¬eq  gt′  =
  tri> (<-asym (∷ˡ-mono-< gt′)) (<⇒≢ (∷ˡ-mono-< gt′) ∘ PE.sym) (∷ˡ-mono-< gt′)

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = PE.isEquivalence
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





-- Of proposal by S.M. *******************************************************

-- The instance of  DecTotalOrder for _≤_ on Bin,
-- where (x ≤ y) is defined as (x < y ⊎ x ≡ y).

open Tri

binDTO : DecTotalOrder 0ℓ 0ℓ 0ℓ
binDTO =
   record{ Carrier         = Bin
         ; _≈_             = _≡_ {A = Bin}
         ; _≤_             = _≤'_
         ; isDecTotalOrder = isDecTotalOrder }
   where
   open StrictTotalOrder <-strictTotalOrder using ()
        renaming (_≈_ to _='_; _≟_ to _≟'_; _<_ to _<'_; trans to <'trans;
                  compare to compareBin;
                  strictPartialOrder to binStrictPartialOrder)

   open StrictPartialOrder binStrictPartialOrder using ()
                                           renaming (asymmetric to <'asym)
   infix 4 _≤'_
   _≤'_ : Rel Bin 0ℓ
   x ≤' y =  x <' y ⊎ x ≡ y

   _≤'?_ : Decidable₂ _≤'_
   x ≤'? y  with  compareBin x y
   ... | tri< x<y _   _   =  yes $ inj₁ x<y
   ... | tri≈ _   x≡y _   =  yes $ inj₂ x≡y
   ... | tri> x≮y x≢y x>y =  no x≰y
                             where x≰y : ¬ x ≤' y
                                   x≰y (inj₁ x<y) = x≮y x<y
                                   x≰y (inj₂ x≡y) = x≢y x≡y
   ≤'refl : _≡_ ⇒ _≤'_
   ≤'refl = inj₂

   _>'_ : Rel Bin 0ℓ
   _>'_ = flip _<'_

   ≤'trans : Transitive _≤'_
   ≤'trans (inj₁ x<y) (inj₁ y<z) =  inj₁ $ <'trans x<y y<z
   ≤'trans {x} {_} {_} (inj₁ x<y) (inj₂ y≡z) =
                                              inj₁ $ PE.subst (_<'_ x) y≡z x<y
   ≤'trans {_} {_} {z} (inj₂ x≡y) (inj₁ y<z) =
                                    inj₁ $ PE.subst (_>'_ z) (PE.sym x≡y) y<z
   ≤'trans (inj₂ x≡y) (inj₂ y≡z) =  inj₂ $ PE.trans x≡y y≡z

   isPreorder : IsPreorder _≡_ _≤'_
   isPreorder = record{ isEquivalence = PE.isEquivalence
                      ; reflexive     = ≤'refl
                      ; trans         = ≤'trans }

   ≤'antisym : Antisymmetric _≡_ _≤'_
   ≤'antisym (inj₂ x≡y) _          =  x≡y
   ≤'antisym _          (inj₂ y≡x) =  PE.sym y≡x
   ≤'antisym (inj₁ x<y) (inj₁ y<x) =  ⊥-elim $ <'asym x<y y<x

   isPartialOrder : IsPartialOrder _≡_ _≤'_
   isPartialOrder = record{ isPreorder = isPreorder; antisym = ≤'antisym }

   total : Total _≤'_
   total x y = case compareBin x y of \ { (tri< x<y _   _  ) → inj₁ $ inj₁ x<y
                                        ; (tri≈ _   x≡y _  ) → inj₁ $ inj₂ x≡y
                                        ; (tri> _   _   x>y) → inj₂ $ inj₁ x>y
                                        }

   isTotalOrder : IsTotalOrder _≡_ _≤'_
   isTotalOrder = record{ isPartialOrder = isPartialOrder;  total = total }

   isDecTotalOrder : IsDecTotalOrder _≡_ _≤'_
   isDecTotalOrder =
             record{ isTotalOrder = isTotalOrder;  _≟_ = _≟'_;  _≤?_ = _≤'?_ }

