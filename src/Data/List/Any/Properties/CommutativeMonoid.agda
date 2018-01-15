open import Algebra using (CommutativeMonoid)

module Data.List.Any.Properties.CommutativeMonoid {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

open import Data.Nat using (ℕ)
open import Data.Fin as F using (Fin)
import Data.Fin.Properties as FP
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Data.List hiding (sum)
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.Fin.Vec
open import Data.Maybe using (Maybe; just; nothing; maybe)

open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
import Relation.Binary.Sigma.Propositional as OverΣ
open OverΣ using (OverΣ)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
import Relation.Binary.Indexed as I
import Function.Related as FR
open import Function.Inverse renaming (_∘_ to _∘ⁱ_; sym to symⁱ; id to idⁱ)
import Function.Equality as FunEq
open FunEq using (_⟶_; _⟨$⟩_)

open CommutativeMonoid commutativeMonoid renaming (_∙_ to _+_)
open import Algebra.Operations.CommutativeMonoid commutativeMonoid
open import Algebra.Properties.CommutativeMonoid commutativeMonoid

module B = Setoid ([ bag ]-Equality Carrier)

private
  sum-fromList : ∀ xs → sumFin _ (fromList xs) ≡ sum xs
  sum-fromList [] = P.refl
  sum-fromList (x ∷ xs) = P.cong₂ _+_ P.refl (sum-fromList xs)

  sum-toList : ∀ n {f} → sumFin n f ≡ sum (toList f)
  sum-toList ℕ.zero = P.refl
  sum-toList (ℕ.suc n) = P.cong₂ _+_ P.refl (sum-toList n)

  lookup′ : (xs : List Carrier) (i : Fin (length xs)) → Carrier
  lookup′ = fromList

  getLookup : ∀ {xs : List Carrier} (i : Fin (length xs)) → lookup′ xs i ∈ xs
  getLookup {[]} ()
  getLookup {x ∷ xs} Fin.zero = here P.refl
  getLookup {x ∷ xs} (Fin.suc i) = there (getLookup i)

  lookup : ∀ {xs : List Carrier} (i : Fin (length xs)) → ∃ λ x → x ∈ xs
  lookup i = _ , getLookup i

  index-getLookup : ∀ {xs i} → index (getLookup {xs} i) ≡ i
  index-getLookup {[]} {()}
  index-getLookup {x ∷ xs} {Fin.zero} = P.refl
  index-getLookup {x ∷ xs} {Fin.suc i} = P.cong Fin.suc index-getLookup

  lookup′-index : ∀ {xs x} (x∈xs : x ∈ xs) → lookup′ xs (index x∈xs) ≡ x
  lookup′-index (here px) = P.sym px
  lookup′-index (there x∈xs) = lookup′-index x∈xs

  lookup-index′ : ∀ {xs x} (x∈xs : x ∈ xs) → OverΣ _≡_ (lookup (index x∈xs)) (x , x∈xs)
  lookup-index′ (here P.refl) = P.refl , P.refl
  lookup-index′ (there x∈xs) = OverΣ.hom (P.cong there) (lookup-index′ x∈xs)

  lookup-index : ∀ {xs x} (x∈xs : x ∈ xs) → lookup (index x∈xs) ≡ (x , x∈xs)
  lookup-index x∈xs = OverΣ.to-≡ (lookup-index′ x∈xs)

-- If two lists are bag-equal, then there is a bijection between distinct
-- elements of each list.

bag-∈-↔ : ∀ {xs ys : List Carrier} → xs ∼[ bag ] ys → (∃ λ x → x ∈ xs) ↔ (∃ λ y → y ∈ ys)
bag-∈-↔ {xs}{ys} p = record
  { to = P.→-to-⟶ λ {(x , x∈xs) → x , Inverse.to p ⟨$⟩ x∈xs}
  ; from = P.→-to-⟶ λ {(y , y∈ys) → y , Inverse.from p ⟨$⟩ y∈ys}
  ; inverse-of = record
    { left-inverse-of = λ _ → OverΣ.to-≡ (P.refl , Inverse.left-inverse-of p _)
    ; right-inverse-of = λ _ → OverΣ.to-≡ (P.refl , Inverse.right-inverse-of p _)
    }
  }

-- There is a bijection between distinct elements of a list and a set the size
-- of the list's length.

∈-↔-length : (xs : List Carrier) → (∃ λ x → x ∈ xs) ↔ (Fin (length xs))
∈-↔-length xs = record
  { to = P.→-to-⟶ (index ∘ proj₂)
  ; from = P.→-to-⟶ lookup
  ; inverse-of = record
    { left-inverse-of = lookup-index ∘ proj₂
    ; right-inverse-of = λ _ → index-getLookup
    }
  }

-- A bag-equality between two lists induces a permutation between the indices of
-- their elements.

bag-permutation : ∀ {xs ys : List Carrier} → xs ∼[ bag ] ys → Fin (length xs) ↔ Fin (length ys)
bag-permutation {xs} {ys} p =
  Fin (length xs)    ↔⟨ FR.EquationalReasoning.sym (∈-↔-length xs) ⟩
  (∃ λ x → x ∈ xs)   ↔⟨ bag-∈-↔ p ⟩
  (∃ λ y → y ∈ ys)   ↔⟨ ∈-↔-length ys ⟩
  Fin (length ys)    ∎
  where open FR.EquationalReasoning

-- If two lists are bag-equal, then they have the same length.

bag-length-≡ : ∀ {xs ys : List Carrier} → xs ∼[ bag ] ys → length xs ≡ length ys
bag-length-≡ p = FP.↔-≡ (bag-permutation p)

-- The permutation between list element indices given by 'bag-permutation'
-- correctly maps elements of each list to each other.

bag-permutation-correct : ∀ {xs ys : List Carrier} (p : xs ∼[ bag ] ys) → fromList xs ≗ (fromList ys ∘ (Inverse.to (bag-permutation p) ⟨$⟩_))
bag-permutation-correct {xs} {ys} p i =
  begin
    fromList xs i                                        ≡⟨⟩
    lookup′ xs i                                         ≡⟨ P.sym (lookup′-index (Inverse.to p ⟨$⟩ getLookup i)) ⟩
    lookup′ ys (index (Inverse.to p ⟨$⟩ getLookup i))    ≡⟨⟩
    fromList ys (Inverse.to (bag-permutation p) ⟨$⟩ i)   ∎
  where
    open P.≡-Reasoning

-- In a commutative monoid, if you add up everything in two lists that contain
-- the same elements, you get the same result.

sum-bag : ∀ {xs ys} → xs ∼[ bag ] ys → sum xs ≈ sum ys
sum-bag {xs} {ys} p =
  begin
    sum xs                                                          ≡⟨ P.sym (sum-fromList xs) ⟩
    sumFin _ (fromList xs)                                          ≡⟨ sumFin-cong≡ (bag-permutation-correct p) ⟩
    sumFin _ (fromList ys ∘ (Inverse.to (bag-permutation p) ⟨$⟩_))  ≈⟨ sym (sumFin-permute′ (fromList ys) (bag-permutation p)) ⟩
    sumFin _ (fromList ys)                                          ≡⟨ sum-fromList ys ⟩
    sum ys                                                          ∎
  where
    open EqReasoning setoid
