------------------------------------------------------------------------
-- The Agda standard library
--
-- Decomposition of permutations into a list of transpositions.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Permutation.Transposition.List where

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Permutation as P hiding (lift₀)
open import Data.Fin.Properties using (_≟_; suc-injective)
import Data.Fin.Permutation.Components as PC
open import Data.List as L using (List; []; _∷_; _++_; map)
import Data.List.Membership.DecPropositional as L∈
import Data.List.Properties as L
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base as ℕ using (ℕ; suc; zero; parity)
import Data.Nat.Properties as ℕ
open import Data.Parity.Base as ℙ using (Parity; 0ℙ; 1ℙ)
open import Data.Product using (Σ-syntax; ∃₂; _×_; _,_; proj₁; proj₂)
open import Function.Base hiding (id; flip)-- using (_∘_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Definition

-- This decomposition is not a unique representation of the original
-- permutation but can be used to simply proofs about permutations (by
-- instead inducting on the list of transpositions, where a
-- transposition is a permutation swapping two distinct elements and
-- leaving the rest in place).

TranspositionList : ℕ → Set
TranspositionList n = List (∃₂ λ (i j : Fin n) → i ≢ j)

------------------------------------------------------------------------
-- Operations on transposition lists

lift₀ : TranspositionList n → TranspositionList (suc n)
lift₀ xs = map (λ (i , j , i≢j) → (suc i , suc j , i≢j ∘ suc-injective)) xs

eval : TranspositionList n → Permutation′ n
eval []             = id
eval ((i , j , _) ∷ xs) = transpose i j ∘ₚ eval xs

decompose : Permutation′ n → TranspositionList n
decompose {zero}  π = []
decompose {suc n} π with π ⟨$⟩ˡ 0F
... | 0F = lift₀ (decompose (remove 0F π))
... | x@(suc _) = (x , 0F , λ ()) ∷ lift₀ (decompose (remove 0F ((transpose 0F (π ⟨$⟩ˡ 0F)) ∘ₚ π)))

------------------------------------------------------------------------
-- Properties

eval-lift : ∀ (xs : TranspositionList n) → eval (lift₀ xs) ≈ P.lift₀ (eval xs)
eval-lift []               = sym ∘ lift₀-id
eval-lift ((i , j , _) ∷ xs) k = begin
  transpose (suc i) (suc j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k     ≡⟨ cong (eval (lift₀ xs) ⟨$⟩ʳ_) (lift₀-transpose i j k) ⟩
  P.lift₀ (transpose i j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k       ≡⟨ eval-lift xs (P.lift₀ (transpose i j) ⟨$⟩ʳ k) ⟩
  P.lift₀ (eval xs) ⟨$⟩ʳ (P.lift₀ (transpose i j) ⟨$⟩ʳ k) ≡⟨ lift₀-comp (transpose i j) (eval xs) k ⟩
  P.lift₀ (transpose i j ∘ₚ eval xs) ⟨$⟩ʳ k               ∎

eval-decompose : ∀ (π : Permutation′ n) → eval (decompose π) ≈ π
eval-decompose {suc n} π i with π ⟨$⟩ˡ 0F in p
... | 0F = begin
  eval (lift₀ (decompose (remove 0F π)))   ⟨$⟩ʳ i ≡⟨ eval-lift (decompose (remove 0F π)) i ⟩
  P.lift₀ (eval (decompose (remove 0F π))) ⟨$⟩ʳ i ≡⟨ lift₀-cong _ _ (eval-decompose (remove 0F π)) i ⟩
  P.lift₀ (remove 0F π)                    ⟨$⟩ʳ i ≡⟨ lift₀-remove π (trans (cong (π ⟨$⟩ʳ_) (sym p)) (P.inverseʳ π)) i ⟩
  π                                        ⟨$⟩ʳ i ∎
... | x@(suc _) = begin
  tx0 ∘ₚ eval (lift₀ (decompose (remove 0F (t0π ∘ₚ π))))   ⟨$⟩ʳ i ≡⟨ eval-lift (decompose (remove 0F (t0π ∘ₚ π))) (tx0 ⟨$⟩ʳ i) ⟩
  tx0 ∘ₚ P.lift₀ (eval (decompose (remove 0F (t0π ∘ₚ π)))) ⟨$⟩ʳ i ≡⟨ lift₀-cong _ _ (eval-decompose _) (tx0 ⟨$⟩ʳ i) ⟩
  tx0 ∘ₚ P.lift₀ (remove 0F (t0π ∘ₚ π))                    ⟨$⟩ʳ i ≡⟨ lift₀-remove (t0π ∘ₚ π) (inverseʳ π) (tx0 ⟨$⟩ʳ i) ⟩
  tx0 ∘ₚ t0π ∘ₚ π                                          ⟨$⟩ʳ i ≡⟨ cong (λ x′ → tx0 ∘ₚ transpose 0F x′ ∘ₚ π ⟨$⟩ʳ i) p ⟩
  tx0 ∘ₚ transpose 0F x ∘ₚ π                               ⟨$⟩ʳ i ≡⟨ cong (π ⟨$⟩ʳ_) (PC.transpose-inverse 0F x) ⟩
  π                                                       ⟨$⟩ʳ i ∎
    where
      tx0 = transpose x 0F
      t0π = transpose 0F (π ⟨$⟩ˡ 0F)

eval-++ : ∀ (xs ys : TranspositionList n) → eval (xs ++ ys) ≈ eval xs ∘ₚ eval ys
eval-++ [] ys i = refl
eval-++ ((a , b , _) ∷ xs) ys i = eval-++ xs ys (transpose a b ⟨$⟩ʳ i)

eval-reverse : ∀ (xs : TranspositionList n) → eval (L.reverse xs) ≈ flip (eval xs)
eval-reverse [] i = refl
eval-reverse (x@(a , b , _) ∷ xs) i = begin
  eval (L.reverse (x ∷ xs))            ⟨$⟩ʳ i ≡⟨ cong (λ p → eval p ⟨$⟩ʳ i) (L.unfold-reverse x xs) ⟩
  eval (L.reverse xs L.∷ʳ x)           ⟨$⟩ʳ i ≡⟨ eval-++ (L.reverse xs) L.[ x ] i ⟩
  eval (L.reverse xs) ∘ₚ transpose a b ⟨$⟩ʳ i ≡⟨ cong (transpose a b ⟨$⟩ʳ_) (eval-reverse xs i) ⟩
  flip (eval xs) ∘ₚ transpose a b      ⟨$⟩ʳ i ≡⟨ transpose-comm a b (flip (eval xs) ⟨$⟩ʳ i) ⟩
  flip (eval xs) ∘ₚ transpose b a      ⟨$⟩ʳ i ∎

-- Properties of transposition lists that evaluate to the identity

eval[xs]≈id⇒length[xs]≢1 : ∀ (xs : TranspositionList n) → eval xs ≈ id → L.length xs ≢ 1
eval[xs]≈id⇒length[xs]≢1 [] _ = λ ()
eval[xs]≈id⇒length[xs]≢1 ((i , j , i≢j) ∷ []) p with j≡i ← p i rewrite dec-true (i ≟ i) refl = contradiction (sym j≡i) i≢j
eval[xs]≈id⇒length[xs]≢1 (_ ∷ _ ∷ _) _ = λ ()

-- this is the workhorse of the parity theorem!
-- If we have a representation of the identity permutations in 2 + k transpositions we can find one in k transpositions
p₂ : ∀ (xs : TranspositionList n) → eval xs ≈ id → ∀ {k} → L.length xs ≡ 2 ℕ.+ k → Σ[ ys ∈ TranspositionList n ] (eval ys ≈ id × L.length ys ≡ k)
p₂ {n = n} ((i₀ , j , i₀≢j) ∷ xs₀) p q = let (ys , r , s) = machine i₀ i₀≢j xs₀ xs₀[i₀]≡j xs₀[j]≡i₀ (ℕ.suc-injective q) in ys , (λ k → trans (sym (r k)) (p k)) , s
  where
    xs₀[i₀]≡j : eval xs₀ ⟨$⟩ʳ i₀ ≡ j
    xs₀[i₀]≡j = begin
      eval xs₀ ⟨$⟩ʳ i₀                  ≡˘⟨ cong (eval xs₀ ⟨$⟩ʳ_) (PC.transpose-matchʳ i₀ j) ⟩
      transpose i₀ j ∘ₚ eval xs₀ ⟨$⟩ʳ j ≡⟨ p j ⟩
      j                                 ∎

    xs₀[j]≡i₀ : eval xs₀ ⟨$⟩ʳ j ≡ i₀
    xs₀[j]≡i₀ = begin
      eval xs₀ ⟨$⟩ʳ j                    ≡˘⟨ cong (eval xs₀ ⟨$⟩ʳ_) (PC.transpose-matchˡ i₀ j) ⟩
      transpose i₀ j ∘ₚ eval xs₀ ⟨$⟩ʳ i₀ ≡⟨ p i₀ ⟩
      i₀                                 ∎

    open L∈ _≟_

    machine :  ∀ (i : Fin n) (i≢j : i ≢ j) (xs : TranspositionList n) → eval xs ⟨$⟩ʳ i ≡ j → eval xs ⟨$⟩ʳ j ≡ i → ∀ {k} → L.length xs ≡ 1 ℕ.+ k → Σ[ ys ∈ TranspositionList n ] transpose i j ∘ₚ eval xs ≈ eval ys × L.length ys ≡ k
    machine i i≢j ((iₕ , jₕ , iₕ≢jₕ) ∷ xs) xs[i]≡j xs[j]≡i {k} 1+∣xs∣≡1+k with iₕ ∈? i ∷ j ∷ []
    machine i i≢j ((iₕ , jₕ , iₕ≢jₕ) ∷ xs) xs[i]≡j xs[j]≡i {k} 1+∣xs∣≡1+k | no ¬p with jₕ ∈? i ∷ j ∷ []
    ... | no ¬q
      rewrite dec-false (i ≟ iₕ) λ i≡iₕ → ¬p (here (sym i≡iₕ))
      rewrite dec-false (i ≟ jₕ) λ i≡jₕ → ¬q (here (sym i≡jₕ))
      rewrite dec-false (j ≟ iₕ) λ j≡iₕ → ¬p (there (here (sym j≡iₕ)))
      rewrite dec-false (j ≟ jₕ) λ j≡jₕ → ¬q (there (here (sym j≡jₕ)))
      = (iₕ , jₕ , iₕ≢jₕ) ∷ ys , ys′-eval , trans (cong suc (proj₂ (proj₂ rec))) (ℕ.suc-pred k {{ℕ.≢-nonZero k≢0}})
      where
        xs≢[] : xs ≢ []
        xs≢[] refl = i≢j xs[i]≡j

        k≢0 : k ≢ 0
        k≢0 k≡0 = xs≢[] (L.length[xs]≡0⇒xs≡[] (trans (ℕ.suc-injective 1+∣xs∣≡1+k) k≡0))

        k′ : ℕ
        k′ = ℕ.pred k

        rec = machine i i≢j xs xs[i]≡j xs[j]≡i {k′} (trans (ℕ.suc-injective 1+∣xs∣≡1+k) (sym (ℕ.suc-pred k {{ℕ.≢-nonZero k≢0}})))

        ys : TranspositionList n
        ys = proj₁ rec

        ys-eval : transpose i j ∘ₚ eval xs ≈ eval ys
        ys-eval = proj₁ (proj₂ rec)

        ys′-eval : transpose i j ∘ₚ transpose iₕ jₕ ∘ₚ eval xs ≈ transpose iₕ jₕ ∘ₚ eval ys
        ys′-eval k with k ∈? i ∷ j ∷ iₕ ∷ jₕ ∷ []
        ... | no ¬r
          with ys[k] ← ys-eval k
          rewrite dec-false (k ≟ i)  λ k≡i  → ¬r (here k≡i)
          rewrite dec-false (k ≟ j)  λ k≡j  → ¬r (there (here k≡j))
          rewrite dec-false (k ≟ iₕ) λ k≡iₕ → ¬r (there (there (here k≡iₕ)))
          rewrite dec-false (k ≟ jₕ) λ k≡jₕ → ¬r (there (there (there (here k≡jₕ))))
          = ys[k]
        ... | yes (here k≡i)
          with ys[k] ← ys-eval k
          rewrite dec-true  (k ≟ i) k≡i
          rewrite dec-false (k ≟ iₕ) λ k≡iₕ → ¬p (here (trans (sym k≡iₕ) k≡i))
          rewrite dec-false (k ≟ jₕ) λ k≡jₕ → ¬q (here (trans (sym k≡jₕ) k≡i))
          rewrite dec-false (j ≟ iₕ) λ j≡iₕ → ¬p (there (here (sym j≡iₕ)))
          rewrite dec-false (j ≟ jₕ) λ j≡jₕ → ¬q (there (here (sym j≡jₕ)))
          = ys[k]
        ... | yes (there (here k≡j))
          with ys[k] ← ys-eval k
          rewrite dec-false (k ≟ i)  λ k≡i  → i≢j (trans (sym k≡i) k≡j)
          rewrite dec-true  (k ≟ j) k≡j
          rewrite dec-false (k ≟ iₕ) λ k≡iₕ → ¬p (there (here (trans (sym k≡iₕ) k≡j)))
          rewrite dec-false (k ≟ jₕ) λ k≡jₕ → ¬q (there (here (trans (sym k≡jₕ) k≡j)))
          rewrite dec-false (i ≟ iₕ) λ i≡iₕ → ¬p (here (sym i≡iₕ))
          rewrite dec-false (i ≟ jₕ) λ i≡jₕ → ¬q (here (sym i≡jₕ))
          = ys[k]
        ... | yes (there (there (here k≡iₕ)))
          with ys[jₕ] ← ys-eval jₕ
          rewrite dec-false (k ≟ i)  λ k≡i  → ¬p (here (trans (sym k≡iₕ) k≡i))
          rewrite dec-false (k ≟ j)  λ k≡j  → ¬p (there (here (trans (sym k≡iₕ) k≡j)))
          rewrite dec-true  (k ≟ iₕ) k≡iₕ
          rewrite dec-false (jₕ ≟ i) λ jₕ≡i → ¬q (here jₕ≡i)
          rewrite dec-false (jₕ ≟ j) λ jₕ≡j → ¬q (there (here jₕ≡j))
          = ys[jₕ]
        ... | yes (there (there (there (here k≡jₕ))))
          with ys[iₕ] ← ys-eval iₕ
          rewrite dec-false (k ≟ i)  λ k≡i  → ¬q (here (trans (sym k≡jₕ) k≡i))
          rewrite dec-false (k ≟ j)  λ k≡j  → ¬q (there (here (trans (sym k≡jₕ) k≡j)))
          rewrite dec-false (k ≟ iₕ) λ k≡iₕ → iₕ≢jₕ (trans (sym k≡iₕ) k≡jₕ)
          rewrite dec-true  (k ≟ jₕ) k≡jₕ
          rewrite dec-false (iₕ ≟ i) λ iₕ≡i → ¬p (here iₕ≡i)
          rewrite dec-false (iₕ ≟ j) λ iₕ≡j → ¬p (there (here iₕ≡j))
          = ys[iₕ]
    ... | yes (here jₕ≡i)
      rewrite dec-false (i ≟ iₕ) λ i≡iₕ → iₕ≢jₕ (sym (trans jₕ≡i i≡iₕ))
      rewrite dec-true  (i ≟ jₕ) (sym jₕ≡i)
      rewrite dec-false (j ≟ iₕ) λ j≡iₕ → ¬p (there (here (sym j≡iₕ)))
      rewrite dec-false (j ≟ jₕ) λ j≡jₕ → i≢j (sym (trans j≡jₕ jₕ≡i))
      = {!!}
      where
        xs≢[] : xs ≢ []
        xs≢[] refl = i≢j (sym xs[j]≡i)

        k≢0 : k ≢ 0
        k≢0 k≡0 = xs≢[] (L.length[xs]≡0⇒xs≡[] (trans (ℕ.suc-injective 1+∣xs∣≡1+k) k≡0))

        k′ : ℕ
        k′ = ℕ.pred k

        rec = machine iₕ (λ iₕ≡j → ¬p (there (here iₕ≡j))) xs xs[i]≡j {!xs[j]≡i!} {k′} {!!}
        

    ... | yes (there (here jₕ≡j)) = {!!}
    machine i i≢j ((iₕ , jₕ , iₕ≢jₕ) ∷ xs) xs[i]≡j {k} 1+∣xs∣≡1+k | yes (here iₕ≡i) with jₕ ≟ j
    ... | no jₕ≢j = {!!}
    ... | yes jₕ≡j = xs , prop , ℕ.suc-injective 1+∣xs∣≡1+k
      where
        prop : transpose i j ∘ₚ transpose iₕ jₕ ∘ₚ eval xs ≈ eval xs
        prop k rewrite iₕ≡i rewrite jₕ≡j = cong (eval xs ⟨$⟩ʳ_) (PC.transpose-inverse′ i j)
    machine i i≢j ((iₕ , jₕ , iₕ≢jₕ) ∷ xs) xs[i]≡j {k} 1+∣xs∣≡1+k | yes (there (here iₕ≡j)) with jₕ ≟ i
    ... | no jₕ≢i = {!!}
    ... | yes jₕ≡i = xs , prop , ℕ.suc-injective 1+∣xs∣≡1+k
      where
        prop : transpose i j ∘ₚ transpose iₕ jₕ ∘ₚ eval xs ≈ eval xs
        prop k rewrite iₕ≡j rewrite jₕ≡i = cong (eval xs ⟨$⟩ʳ_) (PC.transpose-inverse j i)
  
{-

p₃ : ∀ (xs : TranspositionList n) → eval xs ≈ id → parity (L.length xs) ≡ 0ℙ
p₃ [] p = refl
p₃ xs@(_ ∷ []) p = contradiction refl (eval[xs]≈id⇒length[xs]≢1 xs p)
p₃ xs@(_ ∷ _ ∷ _) p with p₂ xs p refl
... | ys , p′ , ys-shorter = {!parity (L.length ys)!}

p₄ : ∀ (xs ys : TranspositionList n) → eval xs ≈ eval ys → parity (L.length xs) ≡ parity (L.length ys)
p₄ = {!!}
-}
