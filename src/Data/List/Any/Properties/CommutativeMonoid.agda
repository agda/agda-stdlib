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

sum-bag : ∀ {xs ys} → xs ∼[ bag ] ys → sum xs ≈ sum ys
sum-bag {xs} {ys} p =
  begin
    sum xs                                                         ≡⟨ P.sym (sumTable-fromList xs) ⟩
    sumTable (Tbl.fromList xs)                                     ≡⟨ sumTable-cong≡ (bag-permutation-correct p) ⟩
    sumTable (Tbl.permute (bag-permutation p) (Tbl.fromList ys))   ≈⟨ sym (sumTable-permute′ (Tbl.fromList ys) (bag-permutation p)) ⟩
    sumTable (Tbl.fromList ys)                                     ≡⟨ sumTable-fromList ys ⟩
    sum ys                                                         ∎
  where
    open EqReasoning setoid
