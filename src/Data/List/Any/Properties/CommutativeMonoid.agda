------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list membership applicable only in a commutative monoid
------------------------------------------------------------------------

open import Algebra using (CommutativeMonoid)

module Data.List.Any.Properties.CommutativeMonoid {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

open import Data.List.Any.Membership.Propositional using (bag; [_]-Equality; _∼[_]_)
open import Data.List.Any.BagAndSetEquality using (bag-permutation; bag-permutation-correct)
import Data.Table as Tbl using (fromList; permute)

open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
import Relation.Binary.PropositionalEquality as P

open CommutativeMonoid commutativeMonoid renaming (_∙_ to _+_)
open import Algebra.Operations.CommutativeMonoid commutativeMonoid
open import Algebra.Properties.CommutativeMonoid commutativeMonoid

module B = Setoid ([ bag ]-Equality Carrier)

-- In a commutative monoid, if you add up everything in two lists that contain
-- the same elements, you get the same result.

sum-bag : ∀ {xs ys} → xs ∼[ bag ] ys → sumₗ xs ≈ sumₗ ys
sum-bag {xs} {ys} p =
  begin
    sumₗ xs                                                    ≡⟨ P.sym (sumₜ-fromList xs) ⟩
    sumₜ (Tbl.fromList xs)                                     ≡⟨ sumₜ-cong≡ (bag-permutation-correct p) ⟩
    sumₜ (Tbl.permute (bag-permutation p) (Tbl.fromList ys))   ≈⟨ sym (sumₜ-permute′ (Tbl.fromList ys) (bag-permutation p)) ⟩
    sumₜ (Tbl.fromList ys)                                     ≡⟨ sumₜ-fromList ys ⟩
    sumₗ ys                                                    ∎
  where
    open EqReasoning setoid
