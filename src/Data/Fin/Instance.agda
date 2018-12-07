module Data.Fin.Instance where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Instance
open import Function.Inverse
open import Relation.Binary.PropositionalEquality
open import Instance
open import Data.Fin hiding (_≤_)
open import Data.Fin.Properties hiding (≤-refl ; ≤-irrelevance ; ≤-trans ; ≤-reflexive)
open import Data.Fin.Permutation

data _InverseOfᵢ_ {k} (f g : Fin (suc k) → Fin (suc k)) : (m : ℕ) → {{m≤k : m ≤ᵢ k}} → Set where
  instance
    inv-zero : {{eq : f (g zero) ≡ zero }} → (f InverseOfᵢ g) zero
    inv-suc  : ∀{a} → {{sa≤k : suc a ≤ᵢ k}} → let fn = fromℕ≤ (s≤s (≤ᵢ-to-≤ {{sa≤k}}))
                                              in {{eq : f (g fn) ≡ fn }}
               → let e = ≤-to-≤ᵢ (≤⇒pred≤ ≤ᵢ-to-≤)
                 in {{ind : _InverseOfᵢ_ f g a {{e}}}} → (f InverseOfᵢ g) (suc a)



_InverseOfᵢ′_ : ∀{k} (f g : Fin (suc k) → Fin (suc k)) → (m : ℕ) → m ≤ k → Set
_InverseOfᵢ′_ f g m x = _InverseOfᵢ_ f g m {{≤-to-≤ᵢ x}}


_invOf_at′_ : ∀{k} → (f g : Fin (suc k) → Fin (suc k)) → (m : ℕ) → (m≤k : m ≤ k)
              → (inv : (f InverseOfᵢ′ g) k ≤-refl) → f (g (fromℕ≤ (s≤s m≤k) )) ≡ fromℕ≤ (s≤s m≤k)
_invOf_at′_ {k} f g m m≤k x = hfun k (k ∸ m) (m∸[m∸n]≡n m≤k) ≤-refl x m≤k where
  hfun : ∀ nk l → nk ∸ l ≡ m → (nk≤k : nk ≤ k) → (f InverseOfᵢ′ g) nk nk≤k
      → (m≤k : m ≤ k) → f (g (fromℕ≤ (s≤s m≤k) )) ≡ fromℕ≤ (s≤s m≤k)
  hfun zero zero refl z≤n inv-zero z≤n = it
  hfun zero (suc l) refl z≤n inv-zero z≤n = it
  hfun (suc nk) zero refl nklk inv-suc mlk
    = subst (λ z → f (g (fromℕ≤ (s≤s z))) ≡ fromℕ≤ (s≤s z)) (≤-irrelevance ((≤ᵢ-to-≤ {{≤-to-≤ᵢ nklk}})) mlk) it
  hfun (suc nk) (suc l) neq (s≤s nklk) (inv-suc {{sa≤k}} {{ind = ind}}) mlk
    = hfun nk l neq (≤-step nklk) w mlk where
      w = subst (λ z → (f InverseOfᵢ′ g) nk z) (≤-irrelevance (≤-trans (≤-step (≤-reflexive refl))
                                                              (s≤s (≤ᵢ-to-≤ {{≤-to-≤ᵢ nklk}}))) (≤-step nklk)) ind



_invOf_at_ : ∀{k} → (f g : Fin (suc k) → Fin (suc k)) → (m : ℕ) → {{m≤k : m ≤ᵢ k}}
             → {{inv : (f InverseOfᵢ′ g) k ≤-refl}}
             → f (g (fromℕ≤ (s≤s (≤ᵢ-to-≤ {{m≤k}})) )) ≡ fromℕ≤ (s≤s (≤ᵢ-to-≤ {{m≤k}}))
f invOf g at m = (f invOf g at′ m) ≤ᵢ-to-≤ it



open _InverseOf_

invOfᵢ-to-invOf : ∀{k} → (f g : Fin (suc k) → Fin (suc k))
               → {{inv : (f InverseOfᵢ′ g) k ≤-refl}} → {{inv′ : (g InverseOfᵢ′ f) k ≤-refl}}
               → (→-to-⟶ f) InverseOf (→-to-⟶ g)
left-inverse-of (invOfᵢ-to-invOf f g) x
  = subst (λ z → f (g z) ≡ z) (fromℕ≤-toℕ x _) ((f invOf g at′ toℕ x) (toℕ≤pred[n] x) it)  
right-inverse-of (invOfᵢ-to-invOf f g) x
  = subst (λ z → g (f z) ≡ z) (fromℕ≤-toℕ x _) ((g invOf f at′ toℕ x) (toℕ≤pred[n] x) it)



permutationᵢ : ∀ {k} (f g : Fin (suc k) → Fin (suc k))
               → {{inv : (f InverseOfᵢ′ g) k ≤-refl}} → {{inv′ : (g InverseOfᵢ′ f) k ≤-refl}}
               → Permutation′ (suc k)
permutationᵢ f g = record
  { to         = →-to-⟶ f
  ; from       = →-to-⟶ g
  ; inverse-of = invOfᵢ-to-invOf g f
  }


-- Example
--
-- g : Fin 3 → Fin 3
-- g zero = suc zero
-- g (suc zero) = suc (suc zero)
-- g (suc (suc zero)) = zero
-- g (suc (suc (suc ())))

-- f : Fin 3 → Fin 3
-- f zero = suc (suc zero)
-- f (suc zero) = zero
-- f (suc (suc zero)) = suc zero
-- f (suc (suc (suc ())))


-- perm : Permutation′ 3
-- perm = permutationᵢ f g
