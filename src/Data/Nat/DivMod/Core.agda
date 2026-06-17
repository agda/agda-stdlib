------------------------------------------------------------------------
-- The Agda standard library
--
-- Core lemmas for division and modulus operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.DivMod.Core where

open import Agda.Builtin.Nat using ()
  renaming (div-helper to divₕ; mod-helper to modₕ)

open import Data.Nat.Base using (zero; suc; _+_; _*_; _∸_; _≤_; _<_;
 _≥_; z≤n; s≤s)
open import Data.Nat.Properties
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; subst; trans)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open ≤-Reasoning

------------------------------------------------------------------------
-- Helper lemmas that have no interpretation for _%_, only for modₕ

private

  mod-cong₃ : ∀ {c n a₁ a₂ b} → a₁ ≡ a₂ → modₕ c n a₁ b ≡ modₕ c n a₂ b
  mod-cong₃ refl = refl

  modₕ-skipTo0 : ∀ acc n a b → modₕ acc n (b + a) a ≡ modₕ (a + acc) n b 0
  modₕ-skipTo0 acc n zero    b = cong (λ v → modₕ acc n v 0) (+-identityʳ b)
  modₕ-skipTo0 acc n (suc a) b = begin-equality
    modₕ acc n (b + suc a) (suc a) ≡⟨ mod-cong₃ (+-suc b a) ⟩
    modₕ acc n (suc b + a) (suc a) ≡⟨⟩
    modₕ (suc acc) n (b + a) a     ≡⟨ modₕ-skipTo0 (suc acc) n a b ⟩
    modₕ (a + suc acc) n b 0       ≡⟨ cong (λ v → modₕ v n b 0) (+-suc a acc) ⟩
    modₕ (suc a + acc) n b 0       ∎

------------------------------------------------------------------------
-- Lemmas for modₕ that also have an interpretation for _%_

a[modₕ]1≡0 : ∀ a → modₕ 0 0 a 0 ≡ 0
a[modₕ]1≡0 zero    = refl
a[modₕ]1≡0 (suc a) = a[modₕ]1≡0 a

n[modₕ]n≡0 : ∀ acc v → modₕ acc (acc + v) (suc v) v ≡ 0
n[modₕ]n≡0 acc v = modₕ-skipTo0 acc (acc + v) v 1

a[modₕ]n<n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n<n acc zero    n       = m≤m+n acc n
a[modₕ]n<n acc (suc d) zero    = a[modₕ]n<n zero d (acc + 0)
a[modₕ]n<n acc (suc d) (suc n) rewrite +-suc acc n = a[modₕ]n<n (suc acc) d n

a[modₕ]n≤a : ∀ acc a n → modₕ acc (acc + n) a n ≤ acc + a
a[modₕ]n≤a acc zero    n       = ≤-reflexive (sym (+-identityʳ acc))
a[modₕ]n≤a acc (suc a) (suc n) = begin
  modₕ acc (acc + suc n) (suc a) (suc n) ≡⟨ cong (λ v → modₕ acc v (suc a) (suc n)) (+-suc acc n) ⟩
  modₕ acc (suc acc + n) (suc a) (suc n) ≤⟨ a[modₕ]n≤a (suc acc) a n ⟩
  suc acc + a                            ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                            ∎
a[modₕ]n≤a acc (suc a) zero    = begin
  modₕ acc (acc + 0) (suc a) 0 ≡⟨ cong (λ v → modₕ acc v (suc a) 0) (+-identityʳ acc) ⟩
  modₕ acc acc (suc a) 0       ≤⟨ a[modₕ]n≤a 0 a acc ⟩
  a                            ≤⟨ n≤1+n a ⟩
  suc a                        ≤⟨ m≤n+m (suc a) acc ⟩
  acc + suc a                  ∎

a≤n⇒a[modₕ]n≡a : ∀ acc n a b → modₕ acc n a (a + b) ≡ acc + a
a≤n⇒a[modₕ]n≡a acc n zero    b = sym (+-identityʳ acc)
a≤n⇒a[modₕ]n≡a acc n (suc a) b = begin-equality
  modₕ (suc acc) n a (a + b) ≡⟨ a≤n⇒a[modₕ]n≡a (suc acc) n a b ⟩
  suc acc + a                ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                ∎

modₕ-idem : ∀ acc a n → modₕ 0 (acc + n) (modₕ acc (acc + n) a n) (acc + n) ≡ modₕ acc (acc + n) a n
modₕ-idem acc zero    n       = a≤n⇒a[modₕ]n≡a 0 (acc + n) acc n
modₕ-idem acc (suc a) zero    rewrite +-identityʳ acc = modₕ-idem 0 a acc
modₕ-idem acc (suc a) (suc n) rewrite +-suc acc n = modₕ-idem (suc acc) a n

a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 : ∀ acc l n → modₕ acc (acc + l) (suc n) l ≡ 0 → modₕ acc (acc + l) n l ≡ acc + l
a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 acc zero    zero    eq rewrite +-identityʳ acc = refl
a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 acc zero    (suc n) eq rewrite +-identityʳ acc = a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 0 acc n eq
a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 acc (suc l) (suc n) eq rewrite +-suc acc l     = a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 (suc acc) l n eq

k<1+a[modₕ]n⇒k≤a[modₕ]n  : ∀ acc k n l → suc k ≤ modₕ acc (acc + l) (suc n) l → k ≤ modₕ acc (acc + l) n l
k<1+a[modₕ]n⇒k≤a[modₕ]n acc k zero    (suc l) (s≤s leq) = leq
k<1+a[modₕ]n⇒k≤a[modₕ]n acc k (suc n) zero    leq rewrite +-identityʳ acc = k<1+a[modₕ]n⇒k≤a[modₕ]n 0 k n acc leq
k<1+a[modₕ]n⇒k≤a[modₕ]n acc k (suc n) (suc l) leq rewrite +-suc acc l     = k<1+a[modₕ]n⇒k≤a[modₕ]n (suc acc) k n l leq

1+a[modₕ]n≤1+k⇒a[modₕ]n≤k : ∀ acc k n l → 0 < modₕ acc (acc + l) (suc n) l →
                            modₕ acc (acc + l) (suc n) l ≤ suc k → modₕ acc (acc + l) n l ≤ k
1+a[modₕ]n≤1+k⇒a[modₕ]n≤k acc k zero    (suc l) 0<mod (s≤s leq) = leq
1+a[modₕ]n≤1+k⇒a[modₕ]n≤k acc k (suc n) zero    0<mod leq rewrite +-identityʳ acc = 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 k n acc 0<mod leq
1+a[modₕ]n≤1+k⇒a[modₕ]n≤k acc k (suc n) (suc l) 0<mod leq rewrite +-suc acc l = 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k (suc acc) k n l 0<mod leq

a+n[modₕ]n≡a[modₕ]n : ∀ acc a n → modₕ acc (acc + n) (acc + a + suc n) n ≡ modₕ acc (acc + n) a n
a+n[modₕ]n≡a[modₕ]n acc zero n rewrite +-identityʳ acc = begin-equality
  modₕ acc (acc + n) (acc + suc n) n   ≡⟨ mod-cong₃ (+-suc acc n) ⟩
  modₕ acc (acc + n) (suc acc + n) n   ≡⟨ modₕ-skipTo0 acc (acc + n) n (suc acc) ⟩
  modₕ (acc + n) (acc + n) (suc acc) 0 ≡⟨⟩
  modₕ 0 (acc + n) acc (acc + n)       ≡⟨ a≤n⇒a[modₕ]n≡a 0 (acc + n) acc n ⟩
  acc                                  ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) zero rewrite +-identityʳ acc = begin-equality
  modₕ acc acc (acc + suc a + 1)   0   ≡⟨ mod-cong₃ (+-comm (acc + suc a) 1) ⟩
  modₕ acc acc (1 + (acc + suc a)) 0   ≡⟨⟩
  modₕ 0   acc (acc + suc a)       acc ≡⟨ mod-cong₃ (+-comm acc (suc a)) ⟩
  modₕ 0   acc (suc a + acc)       acc ≡⟨ mod-cong₃ (sym (+-suc a acc)) ⟩
  modₕ 0   acc (a + suc acc)       acc ≡⟨ a+n[modₕ]n≡a[modₕ]n 0 a acc ⟩
  modₕ 0   acc a                   acc ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) (suc n) rewrite +-suc acc n = begin-equality
  mod₁ (acc + suc a + (2 + n)) (suc n) ≡⟨ cong (λ v → mod₁ (v + suc (suc n)) (suc n)) (+-suc acc a) ⟩
  mod₁ (suc acc + a + (2 + n)) (suc n) ≡⟨⟩
  mod₂ (acc + a + (2 + n))     n       ≡⟨ mod-cong₃ (sym (+-assoc (acc + a) 1 (suc n))) ⟩
  mod₂ (acc + a + 1 + suc n)   n       ≡⟨ mod-cong₃ (cong (_+ suc n) (+-comm (acc + a) 1)) ⟩
  mod₂ (suc acc + a + suc n)   n       ≡⟨ a+n[modₕ]n≡a[modₕ]n (suc acc) a n ⟩
  mod₂ a                       n       ∎
  where
  mod₁ = modₕ acc       (suc acc + n)
  mod₂ = modₕ (suc acc) (suc acc + n)

------------------------------------------------------------------------
-- Helper lemmas that have no interpretation for `_/_`, only for `divₕ`

private

  div-cong₃ : ∀ {c n a₁ a₂ b} → a₁ ≡ a₂ → divₕ c n a₁ b ≡ divₕ c n a₂ b
  div-cong₃ refl = refl

  acc≤divₕ[acc] : ∀ {acc} d n j → acc ≤ divₕ acc d n j
  acc≤divₕ[acc] {acc} d zero    j       = ≤-refl
  acc≤divₕ[acc] {acc} d (suc n) zero    = ≤-trans (n≤1+n acc) (acc≤divₕ[acc] d n d)
  acc≤divₕ[acc] {acc} d (suc n) (suc j) = acc≤divₕ[acc] d n j

  pattern inj₂′ x = inj₂ (inj₁ x)
  pattern inj₃  x = inj₂ (inj₂ x)

  -- This hideous lemma details the conditions needed for two divisions to
  -- be equal when the two offsets (i.e. the 4ᵗʰ parameters) are different.
  -- It may be that this triple sum has an elegant simplification to a
  -- set of inequalities involving the modulus but I can't find it.
  divₕ-offsetEq : ∀ {acc₁ acc₂} d n j k → j ≤ d → k ≤ d →
                  (acc₁ ≡ acc₂     × j ≤ k × k < modₕ 0 d n d) ⊎
                  (acc₁ ≡ acc₂     × modₕ 0 d n d ≤ j × j ≤ k) ⊎
                  (acc₁ ≡ suc acc₂ × k < modₕ 0 d n d × modₕ 0 d n d ≤ j) →
                  divₕ acc₁ d n j ≡ divₕ acc₂ d n k
  divₕ-offsetEq d zero    j       k       j≤d k≤d (inj₁  (refl , _)) = refl
  divₕ-offsetEq d zero    j       k       j≤d k≤d (inj₂′ (refl , _)) = refl
  divₕ-offsetEq d zero    j       k       j≤d k≤d (inj₃ (eq , () , _))
  -- (0 , 0) cases
  divₕ-offsetEq d (suc n) zero    zero    j≤d k≤d (inj₁ (refl , _)) =
    divₕ-offsetEq d n d d ≤-refl ≤-refl (inj₂′ (refl , a[modₕ]n<n 0 n d , ≤-refl))
  divₕ-offsetEq d (suc n) zero    zero    j≤d k≤d (inj₂′ (refl , _)) =
    divₕ-offsetEq d n d d ≤-refl ≤-refl (inj₂′ (refl , a[modₕ]n<n 0 n d , ≤-refl))
  divₕ-offsetEq d (suc n) zero    zero    j≤d k≤d (inj₃ (_ , 0<mod , mod≤0)) =
    contradiction (<-≤-trans 0<mod mod≤0) λ()
  -- (0 , suc) cases
  divₕ-offsetEq d (suc n) zero (suc k)    j≤d k≤d (inj₁  (refl , _ , 1+k<mod)) =
    divₕ-offsetEq d n d k ≤-refl (<⇒≤ k≤d) (inj₃ (refl , k<1+a[modₕ]n⇒k≤a[modₕ]n 0 (suc k) n d 1+k<mod , a[modₕ]n<n 0 n d))
  divₕ-offsetEq d (suc n) zero (suc k)    j≤d k≤d (inj₂′ (refl , mod≤0 , _)) =
    divₕ-offsetEq d n d k ≤-refl (<⇒≤ k≤d) (inj₃ (refl , subst (k <_) (sym (a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 0 d n (n≤0⇒n≡0 mod≤0))) k≤d , a[modₕ]n<n 0 n d))
  divₕ-offsetEq d (suc n) zero (suc k)    j≤d k≤d (inj₃  (_ , 1+k<mod , mod≤0)) =
    contradiction (<-≤-trans 1+k<mod mod≤0) λ()
  -- (suc , 0) cases
  divₕ-offsetEq d (suc n) (suc j) zero j≤d k≤d (inj₁  (_ , () , _))
  divₕ-offsetEq d (suc n) (suc j) zero j≤d k≤d (inj₂′ (_ , _ , ()))
  divₕ-offsetEq d (suc n) (suc j) zero j≤d k≤d (inj₃  (eq , 0<mod , mod≤1+j)) =
    divₕ-offsetEq d n j d (<⇒≤ j≤d) ≤-refl (inj₂′ (eq , 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 j n d 0<mod mod≤1+j , <⇒≤ j≤d))
  -- (suc , suc) cases
  divₕ-offsetEq d (suc n) (suc j) (suc k) j≤d k≤d (inj₁ (eq , s≤s j≤k , 1+k<mod)) =
    divₕ-offsetEq d n j k (<⇒≤ j≤d) (<⇒≤ k≤d) (inj₁ (eq , j≤k , k<1+a[modₕ]n⇒k≤a[modₕ]n 0 (suc k) n d 1+k<mod))
  divₕ-offsetEq d (suc n) (suc j) (suc k) j≤d k≤d (inj₂′ (eq , mod≤1+j , (s≤s j≤k))) with modₕ 0 d (suc n) d ≡? 0
  ... | yes mod≡0 = divₕ-offsetEq d n j k (<⇒≤ j≤d) (<⇒≤ k≤d) (inj₁ (eq , j≤k , subst (k <_) (sym (a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 0 d n mod≡0)) k≤d))
  ... | no  mod≢0 = divₕ-offsetEq d n j k (<⇒≤ j≤d) (<⇒≤ k≤d) (inj₂′ (eq , 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 j n d (n≢0⇒n>0 mod≢0) mod≤1+j , j≤k))
  divₕ-offsetEq d (suc n) (suc j) (suc k) j≤d k≤d (inj₃  (eq , k<mod , mod≤1+j)) =
    divₕ-offsetEq d n j k (<⇒≤ j≤d) (<⇒≤ k≤d) (inj₃ (eq , k<1+a[modₕ]n⇒k≤a[modₕ]n 0 (suc k) n d k<mod , 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 j n d (≤-<-trans z≤n k<mod) mod≤1+j))

------------------------------------------------------------------------
-- Lemmas for divₕ that also have an interpretation for _/_

-- The quotient and remainder are related to the dividend and
-- divisor in the right way.

div-mod-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ * suc (accᵐ + n) + d ≡
    modₕ accᵐ (accᵐ + n) d n + divₕ accᵈ (accᵐ + n) d n * suc (accᵐ + n)
div-mod-lemma accᵐ accᵈ zero    n    = +-identityʳ _
div-mod-lemma accᵐ accᵈ (suc d) zero rewrite +-identityʳ accᵐ = begin-equality
  accᵐ + accᵈ * suc accᵐ + suc d          ≡⟨ +-suc _ d ⟩
  suc accᵈ * suc accᵐ + d                 ≡⟨ div-mod-lemma zero (suc accᵈ) d accᵐ ⟩
  modₕ 0          accᵐ d accᵐ +
  divₕ (suc accᵈ) accᵐ d accᵐ * suc accᵐ  ≡⟨⟩
  modₕ accᵐ accᵐ (suc d) 0 +
  divₕ accᵈ accᵐ (suc d) 0 * suc accᵐ     ∎
div-mod-lemma accᵐ accᵈ (suc d) (suc n) rewrite +-suc accᵐ n = begin-equality
  accᵐ + accᵈ * m + suc d             ≡⟨ +-suc _ d ⟩
  suc (accᵐ + accᵈ * m + d)           ≡⟨ div-mod-lemma (suc accᵐ) accᵈ d n ⟩
  modₕ _ _ d n + divₕ accᵈ _ d n * m  ∎
  where
  m = 2 + accᵐ + n

divₕ-restart : ∀ {acc} d n j → j < n → divₕ acc d n j ≡ divₕ (suc acc) d (n ∸ suc j) d
divₕ-restart d (suc n) zero    j<n       = refl
divₕ-restart d (suc n) (suc j) (s≤s j<n) = divₕ-restart d n j j<n

divₕ-extractAcc : ∀ acc d n j → divₕ acc d n j ≡ acc + divₕ 0 d n j
divₕ-extractAcc acc d zero j          = sym (+-identityʳ acc)
divₕ-extractAcc acc d (suc n) (suc j) = divₕ-extractAcc acc d n j
divₕ-extractAcc acc d (suc n) zero = begin-equality
  divₕ (suc acc)    d n d  ≡⟨ divₕ-extractAcc (suc acc) d n d ⟩
  suc acc +  divₕ 0 d n d  ≡⟨ sym (+-suc acc _) ⟩
  acc + suc (divₕ 0 d n d) ≡⟨ cong (acc +_) (sym (divₕ-extractAcc 1 d n d)) ⟩
  acc +      divₕ 1 d n d  ∎

divₕ-finish : ∀ {acc} d n j → j ≥ n → divₕ acc d n j ≡ acc
divₕ-finish d zero    j       j≥n       = refl
divₕ-finish d (suc n) (suc j) (s≤s j≥n) = divₕ-finish d n j j≥n

n[divₕ]n≡1 : ∀ n m → divₕ 0 n (suc m) m ≡ 1
n[divₕ]n≡1 n zero    = refl
n[divₕ]n≡1 n (suc m) = n[divₕ]n≡1 n m

a[divₕ]1≡a : ∀ acc a → divₕ acc 0 a 0 ≡ acc + a
a[divₕ]1≡a acc zero    = sym (+-identityʳ acc)
a[divₕ]1≡a acc (suc a) = trans (a[divₕ]1≡a (suc acc) a) (sym (+-suc acc a))

a*n[divₕ]n≡a : ∀ acc a n → divₕ acc n (a * suc n) n ≡ acc + a
a*n[divₕ]n≡a acc zero    n = sym (+-identityʳ acc)
a*n[divₕ]n≡a acc (suc a) n = begin-equality
  divₕ acc       n (suc a * suc n)             n ≡⟨ divₕ-restart n (suc a * suc n) n (m≤m+n (suc n) _) ⟩
  divₕ (suc acc) n (suc a * suc n ∸ suc n)     n ≡⟨⟩
  divₕ (suc acc) n (suc n + a * suc n ∸ suc n) n ≡⟨ div-cong₃ (m+n∸m≡n (suc n) (a * suc n)) ⟩
  divₕ (suc acc) n (a * suc n)                 n ≡⟨ a*n[divₕ]n≡a (suc acc) a n ⟩
  suc acc + a                                    ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                                    ∎

+-distrib-divₕ : ∀ acc k m n j → modₕ k (k + j) m j + modₕ 0 (k + j) n (k + j) < suc (k + j) →
                 divₕ acc (k + j) (m + n) j ≡ divₕ acc (k + j) m j + divₕ 0 (k + j) n (k + j)
+-distrib-divₕ acc k (suc m) n zero leq rewrite +-identityʳ k = +-distrib-divₕ (suc acc) 0 m n k leq
+-distrib-divₕ acc k (suc m) n (suc j) leq rewrite +-suc k j = +-distrib-divₕ acc (suc k) m n j leq
+-distrib-divₕ acc k zero n j leq = begin-equality
  divₕ acc (k + j) n j           ≡⟨ divₕ-extractAcc acc (k + j) n j ⟩
  acc + divₕ 0 (k + j) n j       ≡⟨ cong (acc +_) (divₕ-offsetEq _ n j _ (m≤n+m j k) ≤-refl case) ⟩
  acc + divₕ 0 (k + j) n (k + j) ∎
  where
  case = inj₂′ (refl , +-cancelˡ-≤ (suc k) _ _ leq , m≤n+m j k)

divₕ-mono-≤ : ∀ {acc} k {m n o p} → m ≤ n → p ≤ o → divₕ acc (k + o) m o ≤ divₕ acc (k + p) n p
divₕ-mono-≤ {acc} k {0} {n} {_} {p} z≤n p≤o = acc≤divₕ[acc] (k + p) n p
divₕ-mono-≤ {acc} k {_} {_} {suc o} {suc p} (s≤s m≤n) (s≤s p≤o)
  rewrite +-suc k o | +-suc k p = divₕ-mono-≤ (suc k) m≤n p≤o
divₕ-mono-≤ {acc} k {suc m} {suc n} {o} {0}      (s≤s m≤n) z≤n with o <? suc m
... | no  o≮1+m rewrite +-identityʳ k = begin
  divₕ acc (k + o) (suc m) o ≡⟨ divₕ-finish (k + o) (suc m) o (≮⇒≥ o≮1+m) ⟩
  acc                        ≤⟨ n≤1+n acc ⟩
  suc acc                    ≤⟨ acc≤divₕ[acc] k n k ⟩
  divₕ (suc acc) k n k       ∎
... | yes o<1+m rewrite +-identityʳ k = begin
  divₕ acc       (k + o) (suc m) o       ≡⟨ divₕ-restart (k + o) (suc m) o o<1+m ⟩
  divₕ (suc acc) (k + o) (m ∸ o) (k + o) ≤⟨ divₕ-mono-≤ 0 (≤-trans (m∸n≤m m o) m≤n) (m≤m+n k o) ⟩
  divₕ (suc acc) k       n       k       ∎
