------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between orders
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
open import Relation.Binary.Morphism

module Relation.Binary.Morphism.OrderMonomorphism
  {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set a} {B : Set b}
  {_≈₁_ : Rel A ℓ₁} {_≈₂_ : Rel B ℓ₃}
  {_∼₁_ : Rel A ℓ₂} {_∼₂_ : Rel B ℓ₄}
  {⟦_⟧ : A → B}
  (isOrderMonomorphism : IsOrderMonomorphism _≈₁_ _≈₂_ _∼₁_ _∼₂_ ⟦_⟧)
  where

open import Data.Product using (map)
import Relation.Binary.Morphism.RelMonomorphism as RawRelation

open IsOrderMonomorphism isOrderMonomorphism

------------------------------------------------------------------------
-- Re-export equivalence proofs

module EqM = RawRelation Eq.isRelMonomorphism

open RawRelation isRelMonomorphism public

------------------------------------------------------------------------
-- Properties

reflexive : _≈₂_ ⇒ _∼₂_ → _≈₁_ ⇒ _∼₁_
reflexive refl x≈y = cancel (refl (cong x≈y))

irrefl : Irreflexive _≈₂_ _∼₂_ → Irreflexive _≈₁_ _∼₁_
irrefl irrefl x≈y x∼y = irrefl (cong x≈y) (mono x∼y)

antisym : Antisymmetric _≈₂_ _∼₂_ → Antisymmetric _≈₁_ _∼₁_
antisym antisym x∼y y∼x = injective (antisym (mono x∼y) (mono y∼x))

compare : Trichotomous _≈₂_ _∼₂_ → Trichotomous _≈₁_ _∼₁_
compare compare x y with compare ⟦ x ⟧ ⟦ y ⟧
... | tri< a ¬b ¬c = tri< (cancel a) (¬b ∘ cong) (¬c ∘ mono)
... | tri≈ ¬a b ¬c = tri≈ (¬a ∘ mono) (injective b) (¬c ∘ mono)
... | tri> ¬a ¬b c = tri> (¬a ∘ mono) (¬b ∘ cong) (cancel c)

respˡ : _∼₂_ Respectsˡ _≈₂_ → _∼₁_ Respectsˡ _≈₁_
respˡ resp x≈y x∼z = cancel (resp (cong x≈y) (mono x∼z))

respʳ : _∼₂_ Respectsʳ _≈₂_ → _∼₁_ Respectsʳ _≈₁_
respʳ resp x≈y y∼z = cancel (resp (cong x≈y) (mono y∼z))

resp : _∼₂_ Respects₂ _≈₂_ → _∼₁_ Respects₂ _≈₁_
resp = map respʳ respˡ

------------------------------------------------------------------------
-- Structures

isPreorder : IsPreorder _≈₂_ _∼₂_ → IsPreorder _≈₁_ _∼₁_
isPreorder O = record
  { isEquivalence = EqM.isEquivalence O.isEquivalence
  ; reflexive     = reflexive O.reflexive
  ; trans         = trans O.trans
  } where module O = IsPreorder O

isPartialOrder : IsPartialOrder _≈₂_ _∼₂_ → IsPartialOrder _≈₁_ _∼₁_
isPartialOrder O = record
  { isPreorder = isPreorder O.isPreorder
  ; antisym    = antisym O.antisym
  } where module O = IsPartialOrder O

isTotalOrder : IsTotalOrder _≈₂_ _∼₂_ → IsTotalOrder _≈₁_ _∼₁_
isTotalOrder O = record
  { isPartialOrder = isPartialOrder O.isPartialOrder
  ; total          = total O.total
  } where module O = IsTotalOrder O

isDecTotalOrder : IsDecTotalOrder _≈₂_ _∼₂_ → IsDecTotalOrder _≈₁_ _∼₁_
isDecTotalOrder O = record
  { isTotalOrder = isTotalOrder O.isTotalOrder
  ; _≟_          = EqM.dec O._≟_
  ; _≤?_         = dec O._≤?_
  } where module O = IsDecTotalOrder O

isStrictPartialOrder : IsStrictPartialOrder _≈₂_ _∼₂_ →
                       IsStrictPartialOrder _≈₁_ _∼₁_
isStrictPartialOrder O = record
  { isEquivalence = EqM.isEquivalence O.isEquivalence
  ; irrefl        = irrefl O.irrefl
  ; trans         = trans O.trans
  ; <-resp-≈      = resp O.<-resp-≈
  } where module O = IsStrictPartialOrder O

isStrictTotalOrder : IsStrictTotalOrder _≈₂_ _∼₂_ →
                     IsStrictTotalOrder _≈₁_ _∼₁_
isStrictTotalOrder O = record
  { isEquivalence = EqM.isEquivalence O.isEquivalence
  ; trans         = trans O.trans
  ; compare       = compare O.compare
  } where module O = IsStrictTotalOrder O
