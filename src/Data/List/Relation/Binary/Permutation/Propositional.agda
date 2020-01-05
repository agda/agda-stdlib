------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Algebra
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- An inductive definition of permutation

-- Note that one would expect that this would be defined in terms of
-- `Permutation.Setoid`. This is not currently the case as it involves
-- adding in a bunch of trivial `_≡_` proofs to the constructors which
-- a) adds noise and b) prevents easy access to the variables `x`, `y`.
-- This may be changed in future when a better solution is found.

infix 3 _↭_

data _↭_ : Rel (List A) a where
  refl  : ∀ {xs}        → xs ↭ xs
  prep  : ∀ {xs ys} x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ {xs ys} x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : ∀ {xs ys zs}  → xs ↭ ys → ys ↭ zs → xs ↭ zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = refl

↭-refl : Reflexive _↭_
↭-refl = refl

↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
↭-sym refl                = refl
↭-sym (prep x xs↭ys)      = prep x (↭-sym xs↭ys)
↭-sym (swap x y xs↭ys)    = swap y x (↭-sym xs↭ys)
↭-sym (trans xs↭ys ys↭zs) = trans (↭-sym ys↭zs) (↭-sym xs↭ys)

↭-trans : Transitive _↭_
↭-trans = trans

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
  { refl  = refl
  ; sym   = ↭-sym
  ; trans = trans
  }

↭-setoid : Setoid _ _
↭-setoid = record
  { isEquivalence = ↭-isEquivalence
  }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs and allow "zooming in"
-- to localised reasoning.

module PermutationReasoning where

  private
    module Base = EqReasoning ↭-setoid

  open EqReasoning ↭-setoid public
    hiding (step-≈; step-≈˘)

  infixr 2 step-↭  step-↭˘ step-swap step-prep

  step-↭  = Base.step-≈
  step-↭˘ = Base.step-≈˘

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = relTo (trans (prep x xs↭ys) (begin rel))

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = relTo (trans (swap x y xs↭ys) (begin rel))

  syntax step-↭  x y↭z x↭y = x ↭⟨  x↭y ⟩ y↭z
  syntax step-↭˘ x y↭z y↭x = x ↭˘⟨  y↭x ⟩ y↭z
  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z

------------------------------------------------------------------------
-- _↭_ properties
open PermutationReasoning

x∷xs++ys↭xs++x∷ys : ∀ x xs ys → x ∷ xs ++ ys ↭ xs ++ x ∷ ys
x∷xs++ys↭xs++x∷ys x [] ys = refl
x∷xs++ys↭xs++x∷ys x₁ (x₂ ∷ xs) ys = begin
  x₁ ∷ x₂ ∷ xs ++ ys ↭⟨ swap x₁ x₂ refl ⟩
  x₂ ∷ x₁ ∷ xs ++ ys ↭⟨ prep x₂ (x∷xs++ys↭xs++x∷ys x₁ xs ys) ⟩
  x₂ ∷ xs ++ x₁ ∷ ys ∎

xs++ys↭ys++xs : ∀ xs ys → xs ++ ys ↭ ys ++ xs
xs++ys↭ys++xs [] [] = refl
xs++ys↭ys++xs [] (y ∷ ys) = prep y (xs++ys↭ys++xs [] ys)
xs++ys↭ys++xs (x ∷ xs) [] = prep x (xs++ys↭ys++xs xs [])
xs++ys↭ys++xs (x ∷ xs) (y ∷ ys) = begin
  x ∷ xs ++ y ∷ ys ↭˘⟨ x∷xs++ys↭xs++x∷ys y (x ∷ xs) ys ⟩
  y ∷ x ∷ xs ++ ys ↭⟨ prep y (prep x (xs++ys↭ys++xs xs ys)) ⟩
  y ∷ x ∷ ys ++ xs ↭⟨ swap y x ↭-refl ⟩
  x ∷ y ∷ ys ++ xs ↭⟨ x∷xs++ys↭xs++x∷ys x (y ∷ ys) xs ⟩
  y ∷ ys ++ x ∷ xs ∎

++-congˡ-↭ : LeftCongruent _↭_ _++_
++-congˡ-↭ {[]}     ys↭zs = ys↭zs
++-congˡ-↭ {x ∷ xs} ys↭zs = prep x (++-congˡ-↭ ys↭zs)

++-congʳ-↭ : RightCongruent _↭_ _++_
++-congʳ-↭ {xs} {ys} {zs} ys↭zs = begin
  ys ++ xs ↭⟨ xs++ys↭ys++xs ys xs ⟩
  xs ++ ys ↭⟨ ++-congˡ-↭ ys↭zs ⟩
  xs ++ zs ↭⟨ xs++ys↭ys++xs xs zs ⟩
  zs ++ xs ∎

↭-resp-all : ∀ {xs ys} → xs ↭ ys → ∀ {p} {P : Pred A p} → All P xs → All P ys
↭-resp-all refl all[xs] = all[xs]
↭-resp-all (prep x xs↭ys) (px ∷ all[xs]) = px ∷ ↭-resp-all xs↭ys all[xs]
↭-resp-all (swap x y xs↭ys) (px ∷ py ∷ all[xs]) = py ∷ px ∷ ↭-resp-all xs↭ys all[xs]
↭-resp-all (trans xs↭ys ys↭zs) all[xs] = ↭-resp-all ys↭zs (↭-resp-all xs↭ys all[xs])

↭-resp-any : ∀ {xs ys} → xs ↭ ys → ∀ {p} {P : Pred A p} → Any P xs → Any P ys
↭-resp-any refl any[xs] = any[xs]
↭-resp-any (prep x xs↭ys) (here px) = here px
↭-resp-any (prep x xs↭ys) (there any[xs]) = there (↭-resp-any xs↭ys any[xs])
↭-resp-any (swap x y xs↭ys) (here px) = there (here px)
↭-resp-any (swap x y xs↭ys) (there (here py)) = here py
↭-resp-any (swap x y xs↭ys) (there (there any[xs])) = there (there (↭-resp-any xs↭ys any[xs]))
↭-resp-any (trans xs↭ys ys↭zs) any[xs] = ↭-resp-any ys↭zs (↭-resp-any xs↭ys any[xs])
