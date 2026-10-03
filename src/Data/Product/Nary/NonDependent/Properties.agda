------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of nondependent heterogeneous N-ary products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Nary.NonDependent.Properties where

open import Data.Nat.Base using (zero; suc; 2+; _+_)
open import Data.Product.Base as Prod
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡; ≡⇒≡×≡)
open import Data.Product.Nary.NonDependent
open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)
open import Function.Definitions
open import Function.Nary.NonDependent.Base
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Tactic.Cong using (cong!)
open ≡-Reasoning

Product⊤↔Product : ∀ n {ls} {as : Sets n ls} → Product⊤ n as ↔ Product n as
Product⊤↔Product n = mk↔ₛ′ (toProduct n) (toProduct⊤ n) (invˡ n) (invʳ n)
  where
    invˡ : ∀ n {ls} {as : Sets n ls} → StrictlyInverseˡ _≡_ (toProduct n {as = as}) (toProduct⊤ n)
    invˡ 0 _ = refl
    invˡ 1 _ = refl
    invˡ (2+ n) (a , as) = ≡×≡⇒≡ (refl , invˡ (suc n) as)

    invʳ : ∀ n {ls} {as : Sets n ls} → StrictlyInverseʳ _≡_ (toProduct n {as = as}) (toProduct⊤ n)
    invʳ 0 _ = refl
    invʳ 1 _ = refl
    invʳ (2+ n) (a , as) = ≡×≡⇒≡ (refl , invʳ (suc n) as)

splitAt⊤-append⊤-identity :
  ∀ m n {lsa lsb} {as : Sets m lsa} {bs : Sets n lsb} →
  (pa : Product⊤ m as) → (pb : Product⊤ n bs) →
  splitAt⊤ m n (append⊤ m n pa pb) ≡ (pa , pb)
splitAt⊤-append⊤-identity zero    _ _        _ = ≡×≡⇒≡ (refl , refl)
splitAt⊤-append⊤-identity (suc m) n (a , as) bs =
  let eq , eqs = ≡⇒≡×≡ (splitAt⊤-append⊤-identity m n as bs)
  in ≡×≡⇒≡ (≡×≡⇒≡ (refl , eq) , eqs)

append⊤-splitAt⊤-identity :
  ∀ m n {lsa lsb} {as : Sets m lsa} {bs : Sets n lsb} →
  (p : Product⊤ (m + n) (sappend m n as bs)) →
  uncurry (append⊤ m n) (splitAt⊤ m n p) ≡ p
append⊤-splitAt⊤-identity zero    n p        = refl
append⊤-splitAt⊤-identity (suc m) n (a , as) = ≡×≡⇒≡ (refl , append⊤-splitAt⊤-identity m n as)

splitAt-append-identity :
  ∀ m n {lsa lsb} {as : Sets m lsa} {bs : Sets n lsb} →
  (pa : Product m as) → (pb : Product n bs) →
  splitAt m n (append m n pa pb) ≡ (pa , pb)
splitAt-append-identity m n {as = as} {bs} pa pb = begin
    splitAt m n (append m n pa pb)
  ≡⟨⟩
    map (toProduct m) (toProduct n)
      (splitAt⊤ m n (toProduct⊤ (m + n) (toProduct (m + n)
        (append⊤ m n (toProduct⊤ m pa) (toProduct⊤ n pb)))))
  ≡⟨ cong! (strictlyInverseʳ (Product⊤↔Product (m + n)) _) ⟩
    map (toProduct m) (toProduct n)
      (splitAt⊤ m n
        (append⊤ m n (toProduct⊤ m pa) (toProduct⊤ n pb)))
  ≡⟨ cong (map (toProduct m) (toProduct n)) eq ⟩
    map (toProduct m) (toProduct n) (toProduct⊤ m pa , toProduct⊤ n pb)
  ≡⟨ ≡×≡⇒≡ (strictlyInverseˡ (Product⊤↔Product m) pa , strictlyInverseˡ (Product⊤↔Product n) pb) ⟩
    pa , pb
  ∎ where eq = splitAt⊤-append⊤-identity m n (toProduct⊤ m pa) (toProduct⊤ n pb)
          open Inverse
