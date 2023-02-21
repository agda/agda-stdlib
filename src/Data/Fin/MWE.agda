------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.MWE where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s; z≤n; z<s; s<s; _∸_; _^_)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver
open import Data.Product using (Σ-syntax; ∃; ∃₂; ∄; _×_; _,_; map; proj₁; proj₂; uncurry; <_,_>)
open import Data.Product.Properties using (,-injective)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Sum.Properties using ([,]-map; [,]-∘)
open import Function.Base using (_∘_; id; _$_; flip)
open import Level using (Level)
open import Relation.Binary as B hiding (Decidable; _⇔_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_; module ≡-Reasoning)

private
  variable
    a : Level
    A : Set a
    m n o : ℕ
    i j : Fin n

------------------------------------------------------------------------
-- suc
------------------------------------------------------------------------

suc-injective : Fin.suc i ≡ suc j → i ≡ j
suc-injective refl = refl

------------------------------------------------------------------------
-- toℕ
------------------------------------------------------------------------

toℕ-injective : toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {zero}  {}      {}      _
toℕ-injective {suc n} {zero}  {zero}  eq = refl
toℕ-injective {suc n} {suc i} {suc j} eq =
  cong suc (toℕ-injective (cong ℕ.pred eq))

------------------------------------------------------------------------
-- toℕ-↑ˡ: "i" ↑ˡ n = "i" in Fin (m + n)
------------------------------------------------------------------------

toℕ-↑ˡ : ∀ (i : Fin m) n → toℕ (i ↑ˡ n) ≡ toℕ i
toℕ-↑ˡ zero    n = refl
toℕ-↑ˡ (suc i) n = cong suc (toℕ-↑ˡ i n)

------------------------------------------------------------------------
-- toℕ-↑ʳ: n ↑ʳ "i" = "n + i" in Fin (n + m)
------------------------------------------------------------------------

toℕ-↑ʳ : ∀ n (i : Fin m) → toℕ (n ↑ʳ i) ≡ n ℕ.+ toℕ i
toℕ-↑ʳ zero    i = refl
toℕ-↑ʳ (suc n) i = cong suc (toℕ-↑ʳ n i)

------------------------------------------------------------------------
-- toℕ and the ordering relations
------------------------------------------------------------------------

toℕ≤pred[n] : ∀ (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n] zero                 = z≤n
toℕ≤pred[n] (suc {n = suc n} i)  = s≤s (toℕ≤pred[n] i)

toℕ<n : ∀ (i : Fin n) → toℕ i ℕ.< n
toℕ<n {suc n} i = s<s (toℕ≤pred[n] i)

------------------------------------------------------------------------
-- the ordering relations
------------------------------------------------------------------------

<-cmp : Trichotomous _≡_ (_<_ {n})
<-cmp zero    zero    = tri≈ (λ()) refl  (λ())
<-cmp zero    (suc j) = tri< z<s   (λ()) (λ())
<-cmp (suc i) zero    = tri> (λ()) (λ()) z<s
<-cmp (suc i) (suc j) with <-cmp i j
... | tri< i<j i≢j j≮i = tri< (s<s i<j)         (i≢j ∘ suc-injective) (j≮i ∘ ℕₚ.≤-pred)
... | tri> i≮j i≢j j<i = tri> (i≮j ∘ ℕₚ.≤-pred) (i≢j ∘ suc-injective) (s<s j<i)
... | tri≈ i≮j i≡j j≮i = tri≈ (i≮j ∘ ℕₚ.≤-pred) (cong suc i≡j)        (j≮i ∘ ℕₚ.≤-pred)

<⇒≢ : i < j → i ≢ j
<⇒≢ i<i refl = ℕₚ.n≮n _ i<i

------------------------------------------------------------------------
-- splitAt
------------------------------------------------------------------------

-- Fin (m + n) ↔ Fin m ⊎ Fin n

splitAt-↑ˡ : ∀ m i n → splitAt m (i ↑ˡ n) ≡ inj₁ i
splitAt-↑ˡ (suc m) zero    n = refl
splitAt-↑ˡ (suc m) (suc i) n rewrite splitAt-↑ˡ m i n = refl

splitAt-↑ˡ⁻¹ : ∀ {m} {n} {i} {j} → splitAt m {n} i ≡ inj₁ j → j ↑ˡ n ≡ i
splitAt-↑ˡ⁻¹ {suc m} {n} {0F} {.0F} refl = refl
splitAt-↑ˡ⁻¹ {suc m} {n} {suc i} {j} eq with splitAt m i in EQ
... | inj₁ k with refl ← eq = cong suc (splitAt-↑ˡ⁻¹ {i = i} {j = k} EQ)

splitAt-↑ʳ : ∀ m n i → splitAt m (m ↑ʳ i) ≡ inj₂ {B = Fin n} i
splitAt-↑ʳ zero    n i = refl
splitAt-↑ʳ (suc m) n i rewrite splitAt-↑ʳ m n i = refl

splitAt-↑ʳ⁻¹ : ∀ {m} {n} {i} {j} → splitAt m {n} i ≡ inj₂ j → m ↑ʳ j ≡ i
splitAt-↑ʳ⁻¹ {zero}  {n} {i} {j} refl = refl
splitAt-↑ʳ⁻¹ {suc m} {n} {suc i} {j} eq with splitAt m i in EQ
... | inj₂ k with refl ← eq = cong suc (splitAt-↑ʳ⁻¹ {i = i} {j = k} EQ)

splitAt-join : ∀ m n i → splitAt m (join m n i) ≡ i
splitAt-join m n (inj₁ x) = splitAt-↑ˡ m x n
splitAt-join m n (inj₂ y) = splitAt-↑ʳ m n y

join-splitAt : ∀ m n i → join m n (splitAt m i) ≡ i
join-splitAt zero    n i       = refl
join-splitAt (suc m) n zero    = refl
join-splitAt (suc m) n (suc i) = begin
  [ _↑ˡ n , (suc m) ↑ʳ_ ]′ (splitAt (suc m) (suc i)) ≡⟨ [,]-map (splitAt m i) ⟩
  [ suc ∘ (_↑ˡ n) , suc ∘ (m ↑ʳ_) ]′ (splitAt m i)   ≡˘⟨ [,]-∘ suc (splitAt m i) ⟩
  suc ([ _↑ˡ n , m ↑ʳ_ ]′ (splitAt m i))             ≡⟨ cong suc (join-splitAt m n i) ⟩
  suc i                                                         ∎
  where open ≡-Reasoning

-- splitAt "m" "i" ≡ inj₁ "i" if i < m

splitAt-< : ∀ m {n} (i : Fin (m ℕ.+ n)) (i<m : toℕ i ℕ.< m) →
            splitAt m i ≡ inj₁ (fromℕ< i<m)
splitAt-< (suc m) zero    z<s               = refl
splitAt-< (suc m) (suc i) (s<s i<m) = cong (Sum.map suc id) (splitAt-< m i i<m)

-- splitAt "m" "i" ≡ inj₂ "i - m" if i ≥ m

splitAt-≥ : ∀ m {n} (i : Fin (m ℕ.+ n)) (i≥m : toℕ i ℕ.≥ m) →
            splitAt m i ≡ inj₂ (reduce≥ i i≥m)
splitAt-≥ zero    i       _         = refl
splitAt-≥ (suc m) (suc i) (s≤s i≥m) = cong (Sum.map suc id) (splitAt-≥ m i i≥m)


------------------------------------------------------------------------
-- remQuot
------------------------------------------------------------------------

-- Fin (m * n) ↔ Fin m × Fin n

remQuot-combine : ∀ {n k} (i : Fin n) j → remQuot k (combine i j) ≡ (i , j)
remQuot-combine {suc n} {k} zero    j rewrite splitAt-↑ˡ k j (n ℕ.* k) = refl
remQuot-combine {suc n} {k} (suc i) j rewrite splitAt-↑ʳ k   (n ℕ.* k) (combine i j) =
  cong (Data.Product.map₁ suc) (remQuot-combine i j)

combine-remQuot : ∀ {n} k (i : Fin (n ℕ.* k)) → uncurry combine (remQuot {n} k i) ≡ i
combine-remQuot {suc n} k i with splitAt k i in eq
... | inj₁ j = begin
  join k (n ℕ.* k) (inj₁ j)      ≡˘⟨ cong (join k (n ℕ.* k)) eq ⟩
  join k (n ℕ.* k) (splitAt k i) ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                              ∎
  where open ≡-Reasoning
... | inj₂ j = begin
  k ↑ʳ (uncurry combine (remQuot {n} k j)) ≡⟨ cong (k ↑ʳ_) (combine-remQuot {n} k j) ⟩
  join k (n ℕ.* k) (inj₂ j)                ≡˘⟨ cong (join k (n ℕ.* k)) eq ⟩
  join k (n ℕ.* k) (splitAt k i)           ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                                        ∎
  where open ≡-Reasoning

toℕ-combine : ∀ (i : Fin m) (j : Fin n) → toℕ (combine i j) ≡ n ℕ.* toℕ i ℕ.+ toℕ j
toℕ-combine {suc m} {n} i@0F j = begin
  toℕ (combine i j)          ≡⟨⟩
  toℕ (j ↑ˡ (m ℕ.* n))       ≡⟨ toℕ-↑ˡ j (m ℕ.* n) ⟩
  toℕ j                      ≡⟨⟩
  0 ℕ.+ toℕ j                ≡˘⟨ cong (ℕ._+ toℕ j) (ℕₚ.*-zeroʳ n) ⟩
  n ℕ.* toℕ i ℕ.+ toℕ j      ∎
  where open ≡-Reasoning
toℕ-combine {suc m} {n} (suc i) j = begin
  toℕ (combine (suc i) j)        ≡⟨⟩
  toℕ (n ↑ʳ combine i j)         ≡⟨ toℕ-↑ʳ n (combine i j) ⟩
  n ℕ.+ toℕ (combine i j)        ≡⟨ cong (n ℕ.+_) (toℕ-combine i j) ⟩
  n ℕ.+ (n ℕ.* toℕ i ℕ.+ toℕ j)  ≡⟨ solve 3 (λ n i j → n :+ (n :* i :+ j) := n :* (con 1 :+ i) :+ j) refl n (toℕ i) (toℕ j) ⟩
  n ℕ.* toℕ (suc i) ℕ.+ toℕ j    ∎
  where open ≡-Reasoning; open +-*-Solver

combine-monoˡ-< : ∀ {i j : Fin m} (k l : Fin n) →
                  i < j → combine i k < combine j l
combine-monoˡ-< {m} {n} {i} {j} k l i<j = begin-strict
  toℕ (combine i k)      ≡⟨ toℕ-combine i k ⟩
  n ℕ.* toℕ i ℕ.+ toℕ k  <⟨ ℕₚ.+-monoʳ-< (n ℕ.* toℕ i) (toℕ<n k) ⟩
  n ℕ.* toℕ i ℕ.+ n      ≡⟨ ℕₚ.+-comm _ n ⟩
  n ℕ.+ n ℕ.* toℕ i      ≡⟨ cong (n ℕ.+_) (ℕₚ.*-comm n _) ⟩
  n ℕ.+ toℕ i ℕ.* n      ≡⟨ ℕₚ.*-comm (suc (toℕ i)) n ⟩
  n ℕ.* suc (toℕ i)      ≤⟨ ℕₚ.*-monoʳ-≤ n i<j ⟩
  n ℕ.* toℕ j            ≤⟨ ℕₚ.m≤m+n (n ℕ.* toℕ j) (toℕ l) ⟩
  n ℕ.* toℕ j ℕ.+ toℕ l  ≡˘⟨ toℕ-combine j l ⟩
  toℕ (combine j l)      ∎
  where open ℕₚ.≤-Reasoning; open +-*-Solver

combine-injectiveˡ : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) →
                     combine i j ≡ combine k l → i ≡ k
combine-injectiveˡ i j k l cᵢⱼ≡cₖₗ with <-cmp i k
... | tri< i<k _ _ with () ← <⇒≢ (combine-monoˡ-< j l i<k) cᵢⱼ≡cₖₗ 
... | tri≈ _ i≡k _ = i≡k
... | tri> _ _ i>k  with () ← <⇒≢ (combine-monoˡ-< l j i>k) (sym cᵢⱼ≡cₖₗ)

combine-injectiveʳ : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) →
                     combine i j ≡ combine k l → j ≡ l
combine-injectiveʳ {m} {n} i j k l cᵢⱼ≡cₖₗ with combine-injectiveˡ i j k l cᵢⱼ≡cₖₗ
... | refl = toℕ-injective (ℕₚ.+-cancelˡ-≡ (n ℕ.* toℕ i) _ _ (begin
  n ℕ.* toℕ i ℕ.+ toℕ j ≡˘⟨ toℕ-combine i j ⟩
  toℕ (combine i j)     ≡⟨ cong toℕ cᵢⱼ≡cₖₗ ⟩
  toℕ (combine i l)     ≡⟨ toℕ-combine i l ⟩
  n ℕ.* toℕ i ℕ.+ toℕ l ∎))
  where open ≡-Reasoning

combine-injective : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) →
                    combine i j ≡ combine k l → i ≡ k × j ≡ l
combine-injective i j k l cᵢⱼ≡cₖₗ =
  combine-injectiveˡ i j k l cᵢⱼ≡cₖₗ ,
  combine-injectiveʳ i j k l cᵢⱼ≡cₖₗ

combine-surjectiveOLD : ∀ (i : Fin (m ℕ.* n)) → ∃₂ λ j k → combine j k ≡ i
combine-surjectiveOLD {m} {n} i with remQuot {m} n i | P.inspect (remQuot {m} n) i
... | j , k | P.[ eq ] = j , k , (begin
  combine j k                       ≡˘⟨ uncurry (cong₂ combine) (,-injective eq) ⟩
  uncurry combine (remQuot {m} n i) ≡⟨ combine-remQuot {m} n i ⟩
  i                                 ∎)
  where open ≡-Reasoning

combine-surjectiveNEW : ∀ (i : Fin (m ℕ.* n)) → ∃₂ λ j k → combine {m} {n} j k ≡ i
combine-surjectiveNEW {m = suc m} {n} i with splitAt n i in eq
... | inj₁ j rewrite (splitAt-↑ˡ _ j (m ℕ.* n))
    = zero , j , splitAt-↑ˡ⁻¹ eq
... | inj₂ k with (j₁ , k₁ , refl) ← combine-surjectiveNEW {m} {n} k
    = suc j₁ , k₁ , splitAt-↑ʳ⁻¹ eq

combine-surjectiveBUG : ∀ (i : Fin (m ℕ.* n)) → ∃₂ λ j k → combine {m} {n} j k ≡ i
combine-surjectiveBUG {m} {n} i with remQuot {m} n i in eq
{-
... | j , k | P.[ eq ] = j , k , (begin
  combine j k                       ≡˘⟨ uncurry (cong₂ combine) (,-injective eq) ⟩
  uncurry combine (remQuot {m} n i) ≡⟨ combine-remQuot {m} n i ⟩
  i                                 ∎)
  where open ≡-Reasoning
-}
... | p = ?
