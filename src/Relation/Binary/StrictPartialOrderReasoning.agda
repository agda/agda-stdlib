------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a strict partial order
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.StrictPartialOrderReasoning
         {p₁ p₂ p₃} (P : StrictPartialOrder p₁ p₂ p₃) where

open import Level
open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open StrictPartialOrder P

infix  4 _⊢_IsRelatedTo_
infix  3 _∎
infixr 2 _<⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _⊢_IsRelatedTo_ : (b : Bool) (x y : Carrier) → Set (p₁ ⊔ p₃) where
  eqTo  : ∀ {x y} → x ≡ y → false ⊢ x IsRelatedTo y
  relTo : ∀ {x y} → (x<y : x < y) → true ⊢ x IsRelatedTo y

begin_ : ∀ {x y} → true ⊢ x IsRelatedTo y → x < y
begin relTo x<y = x<y

_<⟨_⟩_ : ∀ {b} x {y z} → x < y → b ⊢ y IsRelatedTo z → true ⊢ x IsRelatedTo z
_ <⟨ x<y ⟩ eqTo  y≡z = relTo (P.subst (_ <_) y≡z x<y)
_ <⟨ x<y ⟩ relTo y<z = relTo (trans x<y y<z)


_≡⟨_⟩_ : ∀ {b} x {y z} → x ≡ y → b ⊢ y IsRelatedTo z → b ⊢ x IsRelatedTo z
_ ≡⟨ P.refl ⟩ x<z = x<z

_≡⟨⟩_ : ∀ {b} x {y} → b ⊢ x IsRelatedTo y → b ⊢ x IsRelatedTo y
_ ≡⟨⟩ x<y = x<y

_∎ : ∀ x → false ⊢ x IsRelatedTo x
_∎ _ = eqTo P.refl
