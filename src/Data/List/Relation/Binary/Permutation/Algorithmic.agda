-------------------------------------------------------------------------------
-- The Agda standard library
--
-- A alternative definition for the permutation relation using setoid equality
-- Based on Choudhury and Fiore, "Free Commutative Monoids in HoTT" (MFPS, 2022)
-- Constructor `_⋎_` below is rule (3), directly after the proof of Theorem 6.3,
-- and appears as rule `commrel` of their earlier presentation at (HoTT, 2019),
-- "The finite-multiset construction in HoTT".
--
-- `Algorithmic` ⊆ `Data.List.Relation.Binary.Permutation.Declarative`
-- but enjoys a much smaller space of derivations, without being so (over-)
-- deterministic as to being inductively defined as the relation generated
-- by swapping the top two elements (the relational analogue of bubble-sort).

-- In particular, transitivity, `↭-trans` below, is an admissible property.
--
-- So this relation is 'better' for proving properties of `_↭_`, while at the
-- same time also being a better fit, via `_⋎_`, for the operational features
-- of e.g. sorting algorithms which transpose at arbitary positions.
-------------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Algorithmic
  {s ℓ} (S : Setoid s ℓ) where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (suc-injective)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Data.List.Relation.Binary.Equality.Setoid S as ≋
  using (_≋_; []; _∷_; ≋-refl)

open Setoid S
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

private
  variable
    a b c d : A
    as bs cs ds : List A
    n : ℕ


-------------------------------------------------------------------------------
-- Definition

infix  4  _↭_
infix  5 _⋎_ _⋎[_]_

data _↭_ : List A → List A → Set (s ⊔ ℓ) where
  []   : [] ↭ []
  _∷_  : a ≈ b → as ↭ bs → a ∷ as ↭ b ∷ bs
  _⋎_  : as ↭ b ∷ cs → a ∷ cs ↭ bs → a ∷ as ↭ b ∷ bs

-- smart constructor for prefix congruence

_≡∷_  : ∀ c → as ↭ bs → c ∷ as ↭ c ∷ bs
_≡∷_ c = ≈-refl ∷_

-- pattern synonym to allow naming the 'middle' term
pattern _⋎[_]_ {as} {b} {a} {bs} as↭b∷cs cs a∷cs↭bs
  = _⋎_ {as} {b} {cs = cs} {a} {bs} as↭b∷cs a∷cs↭bs

-------------------------------------------------------------------------------
-- Properties

↭-reflexive : as ≋ bs → as ↭ bs
↭-reflexive []            = []
↭-reflexive (a≈b ∷ as↭bs) = a≈b ∷ ↭-reflexive as↭bs

↭-refl : ∀ as → as ↭ as
↭-refl _ = ↭-reflexive ≋-refl

↭-sym : as ↭ bs → bs ↭ as
↭-sym []                  = []
↭-sym (a≈b     ∷ as↭bs)   = ≈-sym a≈b ∷ ↭-sym as↭bs
↭-sym (as↭b∷cs ⋎ a∷cs↭bs) = ↭-sym a∷cs↭bs ⋎ ↭-sym as↭b∷cs

≋∘↭⇒↭ : as ≋ bs → bs ↭ cs → as ↭ cs
≋∘↭⇒↭ []            []                  = []
≋∘↭⇒↭ (a≈b ∷ as≋bs) (b≈c ∷ bs↭cs)       = ≈-trans a≈b b≈c ∷ ≋∘↭⇒↭ as≋bs bs↭cs
≋∘↭⇒↭ (a≈b ∷ as≋bs) (bs↭c∷ds ⋎ b∷ds↭cs) =
  ≋∘↭⇒↭ as≋bs bs↭c∷ds ⋎ ≋∘↭⇒↭ (a≈b ∷ ≋-refl) b∷ds↭cs

↭∘≋⇒↭ : as ↭ bs → bs ≋ cs → as ↭ cs
↭∘≋⇒↭ []                  []            = []
↭∘≋⇒↭ (a≈b ∷ as↭bs)       (b≈c ∷ bs≋cs) = ≈-trans a≈b b≈c ∷ ↭∘≋⇒↭ as↭bs bs≋cs
↭∘≋⇒↭ (as↭b∷cs ⋎ a∷cs↭bs) (b≈d ∷ bs≋ds) =
  ↭∘≋⇒↭ as↭b∷cs (b≈d ∷ ≋-refl) ⋎ ↭∘≋⇒↭ a∷cs↭bs bs≋ds

↭-length : as ↭ bs → length as ≡ length bs
↭-length []                  = ≡.refl
↭-length (a≈b ∷ as↭bs)       = ≡.cong suc (↭-length as↭bs)
↭-length (as↭b∷cs ⋎ a∷cs↭bs) = ≡.cong suc (≡.trans (↭-length as↭b∷cs) (↭-length a∷cs↭bs))

↭-trans  : as ↭ bs → bs ↭ cs → as ↭ cs
↭-trans = lemma ≡.refl
  where
  lemma : n ≡ length bs → as ↭ bs → bs ↭ cs → as ↭ cs

-- easy base case for bs = [], eq: 0 ≡ 0
  lemma _ [] [] = []

-- fiddly step case for bs = b ∷ bs, where eq : suc n ≡ suc (length bs)
-- hence suc-injective eq : n ≡ length bs

  lemma {n = suc n} eq (a≈b ∷ as↭bs) (b≈c ∷ bs↭cs)
    = ≈-trans a≈b b≈c ∷ lemma (suc-injective eq) as↭bs bs↭cs

  lemma {n = suc n} eq (a≈b ∷ as↭bs) (bs↭c∷ys ⋎ b∷ys↭cs)
    = ≋∘↭⇒↭ (a≈b ∷ ≋-refl) (lemma (suc-injective eq) as↭bs bs↭c∷ys ⋎ b∷ys↭cs)

  lemma {n = suc n} eq (as↭b∷xs ⋎ a∷xs↭bs) (a≈b ∷ bs↭cs)
    = ↭∘≋⇒↭ (as↭b∷xs ⋎ lemma (suc-injective eq) a∷xs↭bs bs↭cs) (a≈b ∷ ≋-refl)

  lemma {n = suc n} {bs = b ∷ bs} {as = a ∷ as} {cs = c ∷ cs} eq
    (as↭b∷xs ⋎[ xs ] a∷xs↭bs) (bs↭c∷ys ⋎[ ys ] b∷ys↭cs) = a∷as↭c∷cs
    where
    n≡∣bs∣ : n ≡ length bs
    n≡∣bs∣ = suc-injective eq

    n≡∣b∷xs∣ : n ≡ length (b ∷ xs)
    n≡∣b∷xs∣ = ≡.trans n≡∣bs∣ (≡.sym (↭-length a∷xs↭bs))

    n≡∣b∷ys∣ : n ≡ length (b ∷ ys)
    n≡∣b∷ys∣ = ≡.trans n≡∣bs∣ (↭-length bs↭c∷ys)

    a∷as↭c∷cs : a ∷ as ↭ c ∷ cs
    a∷as↭c∷cs with lemma n≡∣bs∣ a∷xs↭bs bs↭c∷ys
    ... | a≈c ∷ xs↭ys = a≈c ∷ as↭cs
      where
      as↭cs : as ↭ cs
      as↭cs = lemma n≡∣b∷xs∣ as↭b∷xs
               (lemma n≡∣b∷ys∣ (b ≡∷ xs↭ys) b∷ys↭cs)
    ... | xs↭c∷zs ⋎[ zs ] a∷zs↭ys
      = lemma n≡∣b∷xs∣ as↭b∷xs b∷xs↭c∷b∷zs
        ⋎[ b ∷ zs ]
        lemma n≡∣b∷ys∣ a∷b∷zs↭b∷ys b∷ys↭cs
      where
      b∷zs↭b∷zs : b ∷ zs ↭ b ∷ zs
      b∷zs↭b∷zs = ↭-refl (b ∷ zs)
      b∷xs↭c∷b∷zs : b ∷ xs ↭ c ∷ (b ∷ zs)
      b∷xs↭c∷b∷zs = xs↭c∷zs ⋎[ zs ] b∷zs↭b∷zs
      a∷b∷zs↭b∷ys : a ∷ (b ∷ zs) ↭ b ∷ ys
      a∷b∷zs↭b∷ys = b∷zs↭b∷zs ⋎[ zs ] a∷zs↭ys
