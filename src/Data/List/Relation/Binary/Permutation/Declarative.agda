-------------------------------------------------------------------------------
-- The Agda standard library
--
-- A declarative definition of the permutation relation,
-- as the least congruence making `_++_` commutative
-------------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Declarative
  {s ℓ} (S : Setoid s ℓ) where

open import Data.List.Base
open import Data.List.Properties using (++-identityʳ; length-++)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (suc-injective; +-comm)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties as ≡
  using (module ≡-Reasoning)

open import Data.List.Relation.Binary.Equality.Setoid S as ≋
  using (_≋_; []; _∷_; ≋-refl; ≋-reflexive)
open import Data.List.Relation.Binary.Permutation.Algorithmic S
  using ([]; _∷_; _⋎_)
  renaming (_∼_ to _∼ₐ_; ∼-trans to ∼ₐ-trans; ∼-swap-++ to ∼ₐ-swap-++)

open Setoid S
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

private
  variable
    a b c d : A
    as bs cs ds : List A
    n : ℕ


-------------------------------------------------------------------------------
-- Definition

infix  4  _∼_

data _∼_ : List A → List A → Set (s ⊔ ℓ) where
  []     : [] ∼ []
  _∷_    : a ≈ b → as ∼ bs → a ∷ as ∼ b ∷ bs
  trans  : as ∼ bs → bs ∼ cs → as ∼ cs
  _++ᵒ_  : ∀ as bs → as ++ bs ∼ bs ++ as

-- smart constructor for prefix congruence

_≡∷_  : ∀ c → as ∼ bs → c ∷ as ∼ c ∷ bs
_≡∷_ c = ≈-refl ∷_


-------------------------------------------------------------------------------
-- Properties

∼-reflexive : as ≋ bs → as ∼ bs
∼-reflexive []            = []
∼-reflexive (a≈b ∷ as∼bs) = a≈b ∷ ∼-reflexive as∼bs

∼-refl : ∀ as → as ∼ as
∼-refl _ = ∼-reflexive ≋-refl

∼-sym : as ∼ bs → bs ∼ as
∼-sym []                  = []
∼-sym (a≈b ∷ as∼bs)       = ≈-sym a≈b ∷ ∼-sym as∼bs
∼-sym (trans as∼cs cs∼bs) = trans (∼-sym cs∼bs) (∼-sym as∼cs)
∼-sym (as ++ᵒ bs)         = bs ++ᵒ as

∼-length : as ∼ bs → length as ≡ length bs
∼-length []                  = ≡.refl
∼-length (a≈b ∷ as∼bs)       = ≡.cong suc (∼-length as∼bs)
∼-length (trans as∼cs cs∼bs) = ≡.trans (∼-length as∼cs) (∼-length cs∼bs)
∼-length (as ++ᵒ bs)         = begin
  length (as ++ bs)     ≡⟨ length-++ as ⟩
  length as + length bs ≡⟨ +-comm (length as) _ ⟩
  length bs + length as ≡⟨ length-++ bs ⟨
  length (bs ++ as)     ∎
  where open ≡-Reasoning

∼-congʳ : ∀ cs → as ∼ bs → cs ++ as ∼ cs ++ bs
∼-congʳ {as = as} {bs = bs} cs as∼bs = lemma cs
  where
  lemma : ∀ cs → cs ++ as ∼ cs ++ bs
  lemma []       = as∼bs
  lemma (c ∷ cs) = c ≡∷ lemma cs

∼-congˡ : as ∼ bs → ∀ cs → as ++ cs ∼ bs ++ cs
∼-congˡ {as = as} {bs = bs} as∼bs cs =
  trans (as ++ᵒ cs) (trans (∼-congʳ _ as∼bs) (cs ++ᵒ bs))

∼-cong : as ∼ bs → cs ∼ ds → as ++ cs ∼ bs ++ ds
∼-cong as∼bs cs∼ds = trans (∼-congˡ as∼bs _) (∼-congʳ _ cs∼ds)

-- smart constructor for generalised swap

infix  5 _∼-⋎_

_∼-⋎_ : as ∼ b ∷ cs → a ∷ cs ∼ bs → a ∷ as ∼ b ∷ bs
_∼-⋎_ {b = b} {cs = cs} {a = a} as∼b∷cs a∷cs∼bs =
  trans (a ≡∷ as∼b∷cs) (trans (∼-congˡ ([ a ] ++ᵒ [ b ]) cs) (b ≡∷ a∷cs∼bs))

⋎-syntax : ∀ cs → as ∼ b ∷ cs → a ∷ cs ∼ bs → a ∷ as ∼ b ∷ bs
⋎-syntax cs = _∼-⋎_ {cs = cs}

syntax ⋎-syntax cs as∼b∷cs a∷cs∼bs = as∼b∷cs ∼-⋎[ cs ] a∷cs∼bs


-------------------------------------------------------------------------------
-- Equivalence with `Algorithmic` definition of _∼_

∼ₐ⇒∼ : as ∼ₐ bs → as ∼ bs
∼ₐ⇒∼ []                  = []
∼ₐ⇒∼ (a≈b ∷ as∼bs)       = a≈b ∷ ∼ₐ⇒∼ as∼bs
∼ₐ⇒∼ (as∼b∷cs ⋎ a∷cs∼bs) = ∼ₐ⇒∼ as∼b∷cs ∼-⋎ ∼ₐ⇒∼ a∷cs∼bs

∼⇒∼ₐ : as ∼ bs → as ∼ₐ bs
∼⇒∼ₐ []                  = []
∼⇒∼ₐ (a≈b ∷ as∼bs)       = a≈b ∷ ∼⇒∼ₐ as∼bs
∼⇒∼ₐ (trans as∼cs cs∼bs) = ∼ₐ-trans (∼⇒∼ₐ as∼cs) (∼⇒∼ₐ cs∼bs)
∼⇒∼ₐ (as ++ᵒ bs)         = ∼ₐ-swap-++ as bs
