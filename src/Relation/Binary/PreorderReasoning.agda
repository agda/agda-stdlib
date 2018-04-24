------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a preorder
------------------------------------------------------------------------

-- I think that the idea behind this library is originally Ulf
-- Norell's. I have adapted it to my tastes and mixfix operators,
-- though.

-- If you need to use several instances of this module in a given
-- file, then you can use the following approach:
--
--   import Relation.Binary.PreorderReasoning as Pre
--
--   f x y z = begin
--     ...
--       ∎
--     where open Pre preorder₁
--
--   g i j = begin
--     ...
--       ∎
--     where open Pre preorder₂

open import Relation.Binary

module Relation.Binary.PreorderReasoning
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Relation.Binary.PropositionalEquality as P using (_≡_)
open Preorder P

infix  4 _IsRelatedTo_
infix  3 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_ _≡⟨_⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : Carrier) : Set p₃ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

_≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive x≈y) y∼z)

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≡⟨ P.refl ⟩ x∼z = x∼z

_≈⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≈⟨⟩ x∼y = x∼y

_∎ : ∀ x → x IsRelatedTo x
_∎ _ = relTo refl
