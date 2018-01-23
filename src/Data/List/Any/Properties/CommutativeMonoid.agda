open import Algebra using (CommutativeMonoid)

module Data.List.Any.Properties.CommutativeMonoid {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

open import Data.Nat using (ℕ)
open import Data.Fin as F using (Fin)
import Data.Fin.Properties as FP
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Data.List hiding (sum; lookup)
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.List.Any.BagAndSetEquality using (bag-permutation; bag-permutation-correct)
open import Data.Table hiding (setoid)
open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Product.Relation.SigmaPropositional as OverΣ
open OverΣ using (OverΣ)

open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
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

-- In a commutative monoid, if you add up everything in two lists that contain
-- the same elements, you get the same result.

sum-bag : ∀ {xs ys} → xs ∼[ bag ] ys → sum xs ≈ sum ys
sum-bag {xs} {ys} p =
  begin
    sum xs                                                          ≡⟨ P.sym (sumTable-fromList xs) ⟩
    sumTable (fromList xs)                                          ≡⟨ sumTable-cong≡ (bag-permutation-correct p) ⟩
    sumTable (permute (bag-permutation p) (fromList ys))            ≈⟨ sym (sumTable-permute′ (fromList ys) (bag-permutation p)) ⟩
    sumTable (fromList ys)                                          ≡⟨ sumTable-fromList ys ⟩
    sum ys                                                          ∎
  where
    open EqReasoning setoid
