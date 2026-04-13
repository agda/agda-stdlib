------------------------------------------------------------------------
-- The Agda standard library
--
-- A data structure which keeps track of an upper bound on the number
-- of elements /not/ in a given list
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Countdown (D : DecSetoid 0ℓ 0ℓ) where

open import Data.Fin.Base using (Fin; zero; suc; punchOut)
open import Data.Fin.Properties using (suc-injective; punchOut-injective)
open import Data.Bool.Base using (true; false)
open import Data.List.Base hiding (lookup)
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (∃; _,_; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Function.Base using (const; _$_; _∘_)
open import Function.Bundles using (Injection; module Injection)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; cong)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; _because_)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Nullary.Negation.Core using (contradiction)

import Relation.Binary.PropositionalEquality.Properties as ≡

open ≡.≡-Reasoning

private
  open module D = DecSetoid D
    hiding (refl) renaming (Carrier to Elem)
  open import Data.List.Membership.Setoid D.setoid

------------------------------------------------------------------------
-- Helper functions

private

  -- The /first/ occurrence of x in xs.

  first-occurrence : ∀ {xs} x → x ∈ xs → x ∈ xs
  first-occurrence x (here x≈y)           = here x≈y
  first-occurrence x (there {x = y} x∈xs) with x ≟ y
  ... | true  because [x≈y] = here (invert [x≈y])
  ... | false because   _   = there $ first-occurrence x x∈xs

  -- The index of the first occurrence of x in xs.

  first-index : ∀ {xs} x → x ∈ xs → Fin (length xs)
  first-index x x∈xs = Any.index $ first-occurrence x x∈xs

  -- first-index preserves equality of its first argument.

  first-index-cong : ∀ {x₁ x₂ xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
                     x₁ ≈ x₂ → first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs
  first-index-cong {x₁} {x₂} x₁∈xs x₂∈xs x₁≈x₂ = helper x₁∈xs x₂∈xs
    where
    helper : ∀ {xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
             first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs
    helper (here x₁≈x) (here x₂≈x)           = refl
    helper (here x₁≈x) (there {x = x} x₂∈xs)
      with x₂ ≟ x | dec-true (x₂ ≟ x) (trans (sym x₁≈x₂) x₁≈x)
    ... | _ | refl = refl
    helper (there {x = x} x₁∈xs) (here x₂≈x)
      with x₁ ≟ x | dec-true (x₁ ≟ x) (trans x₁≈x₂ x₂≈x)
    ... | _ | refl = refl
    helper (there {x = x} x₁∈xs) (there x₂∈xs) with x₁ ≟ x | x₂ ≟ x
    ... | true  because _ | true  because _ = refl
    ... | false because _ | false because _ = cong suc $ helper x₁∈xs x₂∈xs
    ... | yes x₁≈x | no  x₂≉x = contradiction (trans (sym x₁≈x₂) x₁≈x) x₂≉x
    ... | no  x₁≉x | yes x₂≈x = contradiction (trans x₁≈x₂ x₂≈x) x₁≉x

  -- first-index is injective in its first argument.

  first-index-injective
    : ∀ {x₁ x₂ xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
      first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs → x₁ ≈ x₂
  first-index-injective {x₁} {x₂} = helper
    where
    helper : ∀ {xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
             first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs → x₁ ≈ x₂
    helper (here x₁≈x) (here x₂≈x)             _  = trans x₁≈x (sym x₂≈x)
    helper (here x₁≈x) (there {x = x} x₂∈xs)   _  with x₂ ≟ x
    helper (here x₁≈x) (there {x = x} x₂∈xs)   _  | yes x₂≈x = trans x₁≈x (sym x₂≈x)
    helper (here x₁≈x) (there {x = x} x₂∈xs)   () | no  x₂≉x
    helper (there {x = x} x₁∈xs) (here x₂≈x)   _  with x₁ ≟ x
    helper (there {x = x} x₁∈xs) (here x₂≈x)   _  | yes x₁≈x = trans x₁≈x (sym x₂≈x)
    helper (there {x = x} x₁∈xs) (here x₂≈x)   () | no  x₁≉x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) _  with x₁ ≟ x | x₂ ≟ x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) _  | yes x₁≈x | yes x₂≈x = trans x₁≈x (sym x₂≈x)
    helper (there {x = x} x₁∈xs) (there x₂∈xs) () | yes x₁≈x | no  x₂≉x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) () | no  x₁≉x | yes x₂≈x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) eq | no  x₁≉x | no  x₂≉x =
      helper x₁∈xs x₂∈xs (suc-injective eq)

------------------------------------------------------------------------
-- The countdown data structure

-- If counted ⊕ n is inhabited then there are at most n values of type
-- Elem which are not members of counted (up to _≈_). You can read the
-- symbol _⊕_ as partitioning Elem into two parts: counted and
-- uncounted.

infix 4 _⊕_

record _⊕_ (counted : List Elem) (n : ℕ) : Set where
  field
    -- An element can be of two kinds:
    -- ⑴ It is provably in counted.
    -- ⑵ It is one of at most n elements which may or may not be in
    --   counted. The "at most n" part is guaranteed by the field
    --   "injective".

    kind      : ∀ x → x ∈ counted ⊎ Fin n
    injective : ∀ {x y i} → kind x ≡ inj₂ i → kind y ≡ inj₂ i → x ≈ y

-- A countdown can be initialised by proving that Elem is finite.

empty : ∀ {n} → Injection D.setoid (≡.setoid (Fin n)) → [] ⊕ n
empty inj =
  record { kind      = inj₂ ∘ to
         ; injective = λ {x} {y} {i} eq₁ eq₂ → injective (begin
             to x ≡⟨ inj₂-injective eq₁ ⟩
             i    ≡⟨ ≡.sym $ inj₂-injective eq₂ ⟩
             to y ∎)
         }
  where open Injection inj

-- A countdown can also be initialised by proving that Elem is finite.

emptyFromList : (counted : List Elem) → (∀ x → x ∈ counted) →
                [] ⊕ length counted
emptyFromList counted complete = empty record
  { to        = λ x → first-index x (complete x)
  ; cong      = first-index-cong (complete _) (complete _)
  ; injective = first-index-injective (complete _) (complete _)
  }

-- Finds out if an element has been counted yet.

lookup : ∀ {counted n} → counted ⊕ n → ∀ x → Dec (x ∈ counted)
lookup {counted} _ x = Any.any? (_≟_ x) counted

-- When no element remains to be counted all elements have been
-- counted.

lookup! : ∀ {counted} → counted ⊕ zero → ∀ x → x ∈ counted
lookup! counted⊕0 x with _⊕_.kind counted⊕0 x
... | inj₁ x∈counted = x∈counted
... | inj₂ ()

private

  -- A variant of lookup!.

  lookup‼ : ∀ {m counted} →
            counted ⊕ m → ∀ x → x ∉ counted → ∃ λ n → m ≡ suc n
  lookup‼ {suc m} counted⊕n x x∉counted = (m , refl)
  lookup‼ {zero}  counted⊕n x x∉counted =
    contradiction (lookup! counted⊕n x) x∉counted

-- Counts a previously uncounted element.

insert : ∀ {counted n} →
         counted ⊕ suc n → ∀ x → x ∉ counted → x ∷ counted ⊕ n
insert {counted} {n} counted⊕1+n x x∉counted =
  record { kind = kind′; injective = inj }
  where
  open _⊕_ counted⊕1+n

  helper : ∀ x y i {j} →
           kind x ≡ inj₂ i → kind y ≡ inj₂ j → i ≡ j → x ≈ y
  helper _ _ _ eq₁ eq₂ refl = injective eq₁ eq₂

  kind′ : ∀ y → y ∈ x ∷ counted ⊎ Fin n
  kind′  y with y ≟ x | kind x | kind y | helper x y
  kind′  y | yes y≈x | _              | _              | _   = inj₁ (here y≈x)
  kind′  y | _       | inj₁ x∈counted | _              | _   = contradiction x∈counted x∉counted
  kind′  y | _       | _              | inj₁ y∈counted | _   = inj₁ (there y∈counted)
  kind′  y | no  y≉x | inj₂ i         | inj₂ j         | hlp =
    inj₂ (punchOut (y≉x ∘ sym ∘ hlp _ refl refl))

  inj : ∀ {y z i} → kind′ y ≡ inj₂ i → kind′ z ≡ inj₂ i → y ≈ z
  inj {y} {z} eq₁ eq₂ with y ≟ x | z ≟ x | kind x | kind y | kind z
                         | helper x y | helper x z | helper y z
  inj ()  _   | yes _ | _     | _              | _      | _      | _ | _ | _
  inj _   ()  | _     | yes _ | _              | _      | _      | _ | _ | _
  inj _   _   | no  _ | no  _ | inj₁ x∈counted | _      | _      | _ | _ | _ = contradiction x∈counted x∉counted
  inj ()  _   | no  _ | no  _ | inj₂ _         | inj₁ _ | _      | _ | _ | _
  inj _   ()  | no  _ | no  _ | inj₂ _         | _      | inj₁ _ | _ | _ | _
  inj eq₁ eq₂ | no  _ | no  _ | inj₂ i         | inj₂ _ | inj₂ _ | _ | _ | hlp =
    hlp _ refl refl $
      punchOut-injective {i = i} _ _ $
        (≡.trans (inj₂-injective eq₁) (≡.sym (inj₂-injective eq₂)))

-- Counts an element if it has not already been counted.

lookupOrInsert : ∀ {counted m} →
                 counted ⊕ m →
                 ∀ x → x ∈ counted ⊎
                       ∃ λ n → m ≡ suc n × x ∷ counted ⊕ n
lookupOrInsert counted⊕n x with lookup counted⊕n x
... | yes x∈counted = inj₁ x∈counted
... | no  x∉counted with lookup‼ counted⊕n x x∉counted
...   | (n , refl) = inj₂ (n , refl , insert counted⊕n x x∉counted)
