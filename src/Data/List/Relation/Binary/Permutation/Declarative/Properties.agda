-------------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of declarative definition of permutation
-------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Declarative.Properties
  {s ℓ} (S : Setoid s ℓ) where

open import Data.List.Base using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (length-++)
open import Data.Nat.Base using (suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties as ≡
  using (module ≡-Reasoning)

open import Data.List.Relation.Binary.Permutation.Algorithmic S
  using ([]; _∷_; _⋎_)
  renaming (_↭_ to _↭ₐ_; ↭-trans to ↭ₐ-trans)
open import Data.List.Relation.Binary.Permutation.Algorithmic.Properties S
  using ()
  renaming (↭-swap-++ to ↭ₐ-swap-++)
open import Data.List.Relation.Binary.Permutation.Declarative S

open Setoid S
  using ()
  renaming (Carrier to A)

private
  variable
    as bs : List A


-------------------------------------------------------------------------------
-- Properties

↭-length : as ↭ bs → length as ≡ length bs
↭-length []                  = ≡.refl
↭-length (a≈b ∷ as↭bs)       = ≡.cong suc (↭-length as↭bs)
↭-length (trans as↭cs cs↭bs) = ≡.trans (↭-length as↭cs) (↭-length cs↭bs)
↭-length (as ++ᵒ bs)         = begin
  length (as ++ bs)     ≡⟨ length-++ as ⟩
  length as + length bs ≡⟨ +-comm (length as) (length bs) ⟩
  length bs + length as ≡⟨ length-++ bs ⟨
  length (bs ++ as)     ∎
  where open ≡-Reasoning

-------------------------------------------------------------------------------
-- Equivalence with `Algorithmic` definition of _↭_

↭ₐ⇒↭ : as ↭ₐ bs → as ↭ bs
↭ₐ⇒↭ []                  = []
↭ₐ⇒↭ (a≈b ∷ as↭bs)       = a≈b ∷ ↭ₐ⇒↭ as↭bs
↭ₐ⇒↭ (as↭b∷cs ⋎ a∷cs↭bs) = ↭ₐ⇒↭ as↭b∷cs ↭-⋎ ↭ₐ⇒↭ a∷cs↭bs

↭⇒↭ₐ : as ↭ bs → as ↭ₐ bs
↭⇒↭ₐ []                  = []
↭⇒↭ₐ (a≈b ∷ as↭bs)       = a≈b ∷ ↭⇒↭ₐ as↭bs
↭⇒↭ₐ (trans as↭cs cs↭bs) = ↭ₐ-trans (↭⇒↭ₐ as↭cs) (↭⇒↭ₐ cs↭bs)
↭⇒↭ₐ (as ++ᵒ bs)         = ↭ₐ-swap-++ as bs
