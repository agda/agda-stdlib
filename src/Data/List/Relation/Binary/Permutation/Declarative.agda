-------------------------------------------------------------------------------
-- The Agda standard library
--
-- A declarative definition of the permutation relation, inductively defined
-- as the least congruence on `List` which makes `_++_` commutative. Thus, for
-- `(A, _≈_)` a setoid, `List A` with equality given by `_↭_` is a constructive
-- presentation of the free commutative monoid on `A`.
--
-- NB. we do not need to specify symmetry as a constructor; the rules defining
-- `_↭_` are themselves symmetric, by inspection, whence `↭-sym` below.
--
-- `_↭_` is somehow the 'maximally non-deterministic' (permissive) presentation
-- of the permutation relation on lists, so is 'easiest' to establish for any
-- given pair of lists, while nevertheless provably equivalent to more
-- operationally defined versions, in particular
-- `Declarative` ⊆ `Data.List.Relation.Binary.Permutation.Algorithmic`
-------------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Declarative
  {s ℓ} (S : Setoid s ℓ) where

open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Function.Base using (id; _∘_)
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as ≡ using (sym)

open import Data.List.Relation.Binary.Equality.Setoid S as ≋
  using (_≋_; []; _∷_; ≋-refl; ≋-reflexive)

open Setoid S
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

private
  variable
    a b c d : A
    as bs cs ds : List A


-------------------------------------------------------------------------------
-- Definition

infix  4  _↭_

data _↭_ : List A → List A → Set (s ⊔ ℓ) where
  []     : [] ↭ []
  _∷_    : a ≈ b → as ↭ bs → a ∷ as ↭ b ∷ bs
  trans  : as ↭ bs → bs ↭ cs → as ↭ cs
  _++ᵒ_  : ∀ as bs → as ++ bs ↭ bs ++ as

-- smart constructor for prefix congruence

_≡∷_  : ∀ c → as ↭ bs → c ∷ as ↭ c ∷ bs
_≡∷_ c = ≈-refl ∷_

-------------------------------------------------------------------------------
-- Basic properties and smart constructors

↭-reflexive : as ≋ bs → as ↭ bs
↭-reflexive []            = []
↭-reflexive (a≈b ∷ as↭bs) = a≈b ∷ ↭-reflexive as↭bs

↭-refl : ∀ as → as ↭ as
↭-refl _ = ↭-reflexive ≋-refl

↭-sym : as ↭ bs → bs ↭ as
↭-sym []                  = []
↭-sym (a≈b ∷ as↭bs)       = ≈-sym a≈b ∷ ↭-sym as↭bs
↭-sym (trans as↭cs cs↭bs) = trans (↭-sym cs↭bs) (↭-sym as↭cs)
↭-sym (as ++ᵒ bs)         = bs ++ᵒ as

-- smart constructor for trans

↭-trans  : as ↭ bs → bs ↭ cs → as ↭ cs
↭-trans []                  = id
↭-trans (trans as↭bs bs↭cs) = ↭-trans as↭bs ∘ ↭-trans bs↭cs
↭-trans as↭bs               = trans as↭bs

-- smart constructor for swap

↭-swap-++ : (as bs : List A) → as ++ bs ↭ bs ++ as
↭-swap-++ []         bs         = ↭-reflexive (≋-reflexive (≡.sym (++-identityʳ bs)))
↭-swap-++ as@(_ ∷ _) []         = ↭-reflexive (≋-reflexive (++-identityʳ as))
↭-swap-++ as@(_ ∷ _) bs@(_ ∷ _) = as ++ᵒ bs

↭-congʳ : as ↭ bs → cs ++ as ↭ cs ++ bs
↭-congʳ {as = as} {bs = bs} {cs = cs} as↭bs = lemma cs
  where
  lemma : ∀ cs → cs ++ as ↭ cs ++ bs
  lemma []       = as↭bs
  lemma (c ∷ cs) = c ≡∷ lemma cs

↭-congˡ : as ↭ bs → as ++ cs ↭ bs ++ cs
↭-congˡ {as = as} {bs = bs} {cs = cs} as↭bs =
  ↭-trans (↭-swap-++ as cs) (↭-trans (↭-congʳ as↭bs) (↭-swap-++ cs bs))

↭-cong : as ↭ bs → cs ↭ ds → as ++ cs ↭ bs ++ ds
↭-cong as↭bs cs↭ds = ↭-trans (↭-congˡ as↭bs) (↭-congʳ cs↭ds)

-- smart constructor for generalised swap

infix  5 _↭-⋎_

_↭-⋎_ : as ↭ b ∷ cs → a ∷ cs ↭ bs → a ∷ as ↭ b ∷ bs
_↭-⋎_ {b = b} {a = a} as↭b∷cs a∷cs↭bs =
  trans (a ≡∷ as↭b∷cs) (↭-trans (↭-congˡ ([ a ] ++ᵒ [ b ])) (b ≡∷ a∷cs↭bs))

⋎-syntax : ∀ cs → as ↭ b ∷ cs → a ∷ cs ↭ bs → a ∷ as ↭ b ∷ bs
⋎-syntax cs = _↭-⋎_ {cs = cs}

syntax ⋎-syntax cs as↭b∷cs a∷cs↭bs = as↭b∷cs ↭-⋎[ cs ] a∷cs↭bs
