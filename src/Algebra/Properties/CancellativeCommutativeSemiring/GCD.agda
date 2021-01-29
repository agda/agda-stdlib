------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the Greatest Common Divisor in
-- CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CancellativeCommutativeSemiring)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary using (Decidable)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (Dec; yes; no)

module Algebra.Properties.CancellativeCommutativeSemiring.GCD
  {a ℓ} (R : CancellativeCommutativeSemiring a ℓ)
  (open CancellativeCommutativeSemiring R)
  where

open import Algebra.Properties.Semiring.Primality semiring using (Coprime)
open import Algebra.Properties.Semiring.Divisibility semiring
open EqReasoning setoid
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as Of*CSemig
open import Algebra.Properties.CommutativeSemigroup.Divisibility
  *-commutativeSemigroup using (x∣xy)

---------------------------------------------------------------------------
-- Re-exporting definition of GCD and its properties in semiring

open import Algebra.Properties.Semiring.GCD semiring public

---------------------------------------------------------------------------
-- Properties of GCD

x∣y∧z∣x/y⇒x*z∣y : ∀ {x y z} → ((x/y , _) : x ∣ y) → z ∣ x/y → x * z ∣ y 
x∣y∧z∣x/y⇒x*z∣y {x} {y} {z} (x/y , x/y*x≈y) (p , p*z≈x/y) = p , (begin
  p * (x * z)  ≈⟨ Of*CSemig.x∙yz≈xz∙y p x z ⟩
  (p * z) * x  ≈⟨ *-congʳ p*z≈x/y ⟩
  x/y * x      ≈⟨ x/y*x≈y ⟩
  y            ∎)

x*y∣x⇒y∣1 : ∀ {x y} → x ≉ 0# → x * y ∣ x → y ∣ 1#
x*y∣x⇒y∣1 {x} {y} x≉0 (q , q*xy≈x) = q , *-cancelˡ-nonZero (q * y) 1# x≉0 (begin
  x * (q * y) ≈⟨  Of*CSemig.x∙yz≈y∙xz x q y ⟩
  q * (x * y) ≈⟨  q*xy≈x ⟩
  x           ≈˘⟨ *-identityʳ x ⟩
  x * 1#      ∎)

x≉0⊎y≉0⇒Coprime[x/gcd,y/gcd]2 : ∀ {x y d} → x ≉ 0# ⊎ y ≉ 0# →
                                ((isGCDᶜ (q₁ , _) (q₂ , _) _) : IsGCD x y d) →
                                Coprime q₁ q₂
x≉0⊎y≉0⇒Coprime[x/gcd,y/gcd]2 x≉0∨y≉0 gcd@(isGCDᶜ d∣x d∣y greatest) x/d∣z y/d∣z =
  x*y∣x⇒y∣1 (x≉0∨y≉0⇒gcd≉0 gcd x≉0∨y≉0) (greatest
    (x∣y∧z∣x/y⇒x*z∣y d∣x x/d∣z)
    (x∣y∧z∣x/y⇒x*z∣y d∣y y/d∣z))

------------------------------------------------------------------------------
-- gcd-s for two division-equivalent pairs
-- are division-equivalent

GCD-unique : ∀ {x x' y y' d d'} → x ∣∣ x' → y ∣∣ y' →
             IsGCD x y d → IsGCD x' y' d' → d ∣∣ d'
GCD-unique (x∣x' , x'∣x) (y∣y' , y'∣y)
           (isGCDᶜ d∣x d∣y greatest) (isGCDᶜ d'∣x' d'∣y' greatest') = d∣d' , d'∣d
  where
  d∣x' = ∣-trans d∣x x∣x';    d∣y' = ∣-trans d∣y y∣y';    d∣d' = greatest' d∣x' d∣y'
  d'∣x = ∣-trans d'∣x' x'∣x;  d'∣y = ∣-trans d'∣y' y'∣y;  d'∣d = greatest d'∣x d'∣y

------------------------------------------------------------------------------
-- gcd-distr  is an important lemma of the gcd distributivity:
-- gcd (c*a) (c*b)  is division-equivalent to  c * (gcd a b).

gcd-distr : Decidable _≈_ → ∀ {a b c d d'} → IsGCD a b d →
            IsGCD (c * a) (c * b) d' → d' ∣∣ (c * d)
gcd-distr _≟_ {a} {b} {c} {d} {d'}
  isGCD[a,b,d]@(isGCDᶜ (a' ,  a'd≈a) (b' , b'd≈b) _)
  isGCD[ca,cb,d']@(isGCDᶜ d'∣ca d'∣cb _)  =  aux (c ≟ 0#)
  where
  aux : Dec (c ≈ 0#) → d' ∣∣ (c * d)
  aux (yes c≈0) = d'∣cd , cd∣d'   -- A trivial case. The goal is reduced to 0 ∣∣ 0.
    where
    cd≈0  = trans (*-congʳ c≈0) (zeroˡ d)
    d'∣cd = ∣-respʳ (sym cd≈0) (_∣0 d')     -- the first part of the goal

    ca≈0  = trans (*-congʳ c≈0) (zeroˡ a)
    ca∣∣0 = ∣∣-reflexive ca≈0
    cb≈0  = trans (*-congʳ c≈0) (zeroˡ b)
    cb∣∣0 = ∣∣-reflexive cb≈0
    d'∣∣0 = GCD-unique ca∣∣0 cb∣∣0 isGCD[ca,cb,d'] (isGCD[0,x,x] 0#)
    d'≈0  = 0∣x⇒x≈0 (proj₂ d'∣∣0)
    cd∣0  = _∣0 (c * d)
    cd∣d' = ∣-respʳ (sym d'≈0) cd∣0    -- the second part of the goal

  aux (no c≉0) = d'∣cd , cd∣d'        -- general case
    where
    -- First derive  cd ∣ d'  from that  cd  divides both  ca and cb.
    ca = c * a;  cb = c * b;  cd = c * d

    cd∣ca = a' , a'*cd≈ca
      where
      a'*cd≈ca = begin
        a' * (c * d)   ≈⟨ Of*CSemig.x∙yz≈y∙xz a' c d ⟩
        c * (a' * d)   ≈⟨ *-congˡ a'd≈a ⟩
        c * a          ∎

    cd∣cb = b' , b'*cd≈cb
      where
      b'*cd≈cb = begin
        b' * (c * d)   ≈⟨ Of*CSemig.x∙yz≈y∙xz b' c d ⟩
        c * (b' * d)   ≈⟨ *-congˡ b'd≈b ⟩
        c * b          ∎

    cd∣d' = IsGCD.greatest isGCD[ca,cb,d'] cd∣ca cd∣cb

    -- Now prove  d' ∣ cd  ----------------

    c∣ca = x∣xy c a;  c∣cb = x∣xy c b   -- hence  xc ≈ gcd ca cb = d'  for some x

    c∣d'    = IsGCD.greatest isGCD[ca,cb,d'] c∣ca c∣cb
    x       = proj₁ c∣d'
    xc≈d'   = proj₂ c∣d'
    xc∣ca   = ∣-respˡ (sym xc≈d') d'∣ca
    xc∣cb   = ∣-respˡ (sym xc≈d') d'∣cb
    y       = proj₁ xc∣ca   -- y*xc ≈ ca
    z       = proj₁ xc∣cb   -- z*xc ≈ cb
    ca≈c*yx = begin
      c * a         ≈⟨ sym (proj₂ xc∣ca) ⟩
      y * (x * c)   ≈⟨ Of*CSemig.x∙yz≈z∙xy y x c ⟩
      c * (y * x)   ∎

    cb≈c*zx = begin
      c * b         ≈⟨ sym (proj₂ xc∣cb) ⟩
      z * (x * c)   ≈⟨ Of*CSemig.x∙yz≈z∙xy z x c ⟩
      c * (z * x)   ∎

    yx≈a     = *-cancelˡ-nonZero {c} (y * x) a c≉0 (sym ca≈c*yx)
    zx≈b     = *-cancelˡ-nonZero {c} (z * x) b c≉0 (sym cb≈c*zx)
    x∣a      = y , yx≈a
    x∣b      = z , zx≈b
    x∣d      = IsGCD.greatest isGCD[a,b,d] x∣a x∣b
    x'       = proj₁ x∣d
    x'x≈d    = proj₂ x∣d
    x'*cx≈cd = begin
      x' * (c * x)   ≈⟨ Of*CSemig.x∙yz≈y∙xz x' c x ⟩
      c * (x' * x)   ≈⟨ *-congˡ x'x≈d ⟩
      c * d          ∎

    cx∣cd = x' , x'*cx≈cd
    cx≈d' = trans (*-comm c x) xc≈d'
    d'∣cd = ∣-respˡ cx≈d' cx∣cd
