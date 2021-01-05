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

open import Algebra.Divisibility _≈_ _*_ using (_∣_; _∣∣_)
open import Algebra.Primality _≈_ _*_ 0# 1# using (Coprime)
open import Algebra.Properties.Semiring.Divisibility semiring using (_∣0; 0∣x⇒x≈0)
open EqReasoning setoid
open import Algebra.Properties.Monoid.Divisibility *-monoid using
  (∣-refl; ∣-trans; ∣-respˡ; ∣-respʳ; ∣∣-reflexive)
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as Of*CSemig
open import Algebra.Properties.CommutativeSemigroup.Divisibility
  *-commutativeSemigroup using (x∣xy)

---------------------------------------------------------------------------
-- Re-exporting definition of GCD and its properties in semiring

open import Algebra.Properties.Semiring.GCD semiring public

---------------------------------------------------------------------------
-- Properties of GCD

x≉0⊎y≉0⇒Coprime[x/gcd,y/gcd] :
  ∀ {x y d} → (x ≉ 0#) ⊎ (y ≉ 0#) → (isGCD : IsGCD x y d) →
  let open IsGCD isGCD
  in  Coprime quot₁ quot₂     -- x/gcd(x,y) is coprime with y/gcd(x,y)
                              -- if any of x, y is nonzero

x≉0⊎y≉0⇒Coprime[x/gcd,y/gcd] {x} {y} {d} nz⊎nz isGCD {c}
                             (q₁ , q₁c≈quot₁) (q₂ , q₂c≈quot₂) = c∣1
  where
  open IsGCD isGCD using (greatest; quot₁; quot₂; quot₁∙gcd≈x; quot₂∙gcd≈y)
  d≉0     = x≉0⊎y≉0⇒gcd≉0 isGCD nz⊎nz
  q₁*dc≈x = begin
    q₁ * (d * c)    ≈⟨ Of*CSemig.x∙yz≈xz∙y q₁ d c ⟩
    (q₁ * c) * d    ≈⟨ *-congʳ q₁c≈quot₁ ⟩
    quot₁ * d       ≈⟨ quot₁∙gcd≈x ⟩
    x               ∎

  q₂*dc≈y = begin
    q₂ * (d * c)    ≈⟨ Of*CSemig.x∙yz≈xz∙y q₂ d c ⟩
    (q₂ * c) * d    ≈⟨ *-congʳ q₂c≈quot₂ ⟩
    quot₂ * d       ≈⟨ quot₂∙gcd≈y ⟩
    y               ∎

  dc∣x = q₁ , q₁*dc≈x
  dc∣y = q₂ , q₂*dc≈y
  c∣1  = let
           (q , q*dc≈d) = greatest dc∣x dc∣y
           d*qc≈d*1     = begin
             d * (q * c)   ≈⟨ Of*CSemig.x∙yz≈y∙xz d q c ⟩
             q * (d * c)   ≈⟨ q*dc≈d ⟩
             d             ≈⟨ sym (*-identityʳ d) ⟩
             d * 1#        ∎

           qc≈1 = *-cancelˡ-nonZero {d} (q * c) 1# d≉0 d*qc≈d*1
        in
        q , qc≈1

------------------------------------------------------------------------------
GCD-unique : ∀ {x x' y y' d d'} → x ∣∣ x' → y ∣∣ y' →
             IsGCD x y d → IsGCD x' y' d' → d ∣∣ d'
                                    -- gcd-s for two division-equivalent pairs
                                    -- are division-equivalent
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
gcd-distr _≟_ {a} {b} {c} {d} {d'} isGCD[a,b,d] isGCD[ca,cb,d'] =  aux (c ≟ 0#)
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

    open IsGCD isGCD[a,b,d] using ()
      renaming (quot₁ to a'; quot₂ to b'; quot₁∙gcd≈x to a'd≈a; quot₂∙gcd≈y to b'd≈b)

    open IsGCD isGCD[ca,cb,d'] using () renaming (divides₁ to d'∣ca; divides₂ to d'∣cb)
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
