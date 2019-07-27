------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Properties {a} {A : Set a} where

open import Data.List using (List; []; _∷_;  map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (here-injective; there-injective)
open import Data.List.Relation.Binary.Sublist.Propositional
  hiding (map)
import Data.List.Relation.Binary.Sublist.Setoid.Properties
  as SetoidProperties
open import Function
open import Level
open import Relation.Binary using (_Respects_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary as U using (Pred)

------------------------------------------------------------------------
-- Re-exporting setoid properties

open SetoidProperties (P.setoid A) public
  hiding (map⁺)

module _ {b} {B : Set b} where

  map⁺ : ∀ {as bs} (f : A → B) → as ⊆ bs → map f as ⊆ map f bs
  map⁺ f = SetoidProperties.map⁺ (setoid A) (setoid B) (cong f)

------------------------------------------------------------------------
-- Category laws for _⊆_

private
  variable
    xs ys zs : List A
    τ τ′ τ₁ τ₂ τ₃ : xs ⊆ ys

⊆-trans-idˡ : ⊆-trans (⊆-refl {x = xs}) τ ≡ τ
⊆-trans-idˡ              {τ = []    } = refl
⊆-trans-idˡ              {τ = _ ∷  _} = cong (_ ∷_ ) ⊆-trans-idˡ
⊆-trans-idˡ {xs = []   } {τ = _ ∷ʳ _} = cong (_ ∷ʳ_) ⊆-trans-idˡ
⊆-trans-idˡ {xs = _ ∷ _} {τ = _ ∷ʳ _} = cong (_ ∷ʳ_) ⊆-trans-idˡ

⊆-trans-idʳ : ⊆-trans τ ⊆-refl ≡ τ
⊆-trans-idʳ {τ = []      } = refl
⊆-trans-idʳ {τ = _ ∷ʳ _  } = cong (_  ∷ʳ_ ) ⊆-trans-idʳ
⊆-trans-idʳ {τ = refl ∷ _} = cong (refl ∷_) ⊆-trans-idʳ

-- Note: The associativity law is oriented such that rewriting with it
-- may trigger reductions of ⊆-trans, which matches first on its
-- second argument and then on its first argument.

⊆-trans-assoc : ⊆-trans τ₁ (⊆-trans τ₂ τ₃) ≡ ⊆-trans (⊆-trans τ₁ τ₂) τ₃
⊆-trans-assoc                               {τ₃ = _ ∷ʳ _} = cong (_ ∷ʳ_) ⊆-trans-assoc
⊆-trans-assoc                 {τ₂ = _ ∷ʳ _} {τ₃ = _ ∷  _} = cong (_ ∷ʳ_) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = _ ∷ʳ _  } {τ₂ = _ ∷  _} {τ₃ = _ ∷  _} = cong (_ ∷ʳ_) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = refl ∷ _} {τ₂ = _ ∷  _} {τ₃ = _ ∷  _} = cong (_ ∷_ ) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = []      } {τ₂ = []    } {τ₃ = []    } = refl

------------------------------------------------------------------------
-- Relationships to other predicates

private
  variable
    ℓ : Level
    P : Pred A ℓ

-- All P is a contravariant functor from _⊆_ to Set.

All-resp-⊆ : (All P) Respects (flip _⊆_)
All-resp-⊆ []          []       = []
All-resp-⊆ (_    ∷ʳ p) (_ ∷ xs) = All-resp-⊆ p xs
All-resp-⊆ (refl ∷  p) (x ∷ xs) = x ∷ All-resp-⊆ p xs

-- Any P is a covariant functor from _⊆_ to Set.

Any-resp-⊆ : (Any P) Respects _⊆_
Any-resp-⊆ = lookup

------------------------------------------------------------------------
-- Functor laws for All-resp-⊆

-- First functor law: identity.

All-resp-⊆-refl : All-resp-⊆ ⊆-refl ≗ id {A = All P xs}
All-resp-⊆-refl []       = refl
All-resp-⊆-refl (p ∷ ps) = cong (p ∷_) (All-resp-⊆-refl ps)

-- Second functor law: composition.

All-resp-⊆-trans : ∀ (τ′ : ys ⊆ zs) →
  All-resp-⊆ {P = P} (⊆-trans τ τ′) ≗ All-resp-⊆ τ ∘ All-resp-⊆ τ′
All-resp-⊆-trans                (_    ∷ʳ τ′) (p ∷ ps) = All-resp-⊆-trans τ′ ps
All-resp-⊆-trans {τ = _ ∷ʳ _  } (refl ∷  τ′) (p ∷ ps) = All-resp-⊆-trans τ′ ps
All-resp-⊆-trans {τ = refl ∷ _} (refl ∷  τ′) (p ∷ ps) = cong (p ∷_) (All-resp-⊆-trans τ′ ps)
All-resp-⊆-trans {τ = []      } ([]        ) []       = refl

------------------------------------------------------------------------
-- Functor laws for Any-resp-⊆ / lookup

-- First functor law: identity.

Any-resp-⊆-refl : Any-resp-⊆ ⊆-refl ≗ id {A = Any P xs}
Any-resp-⊆-refl (here p)  = refl
Any-resp-⊆-refl (there i) = cong there (Any-resp-⊆-refl i)

lookup-⊆-refl = Any-resp-⊆-refl

-- Second functor law: composition.

Any-resp-⊆-trans : ∀ (τ′ : ys ⊆ zs) →
  Any-resp-⊆ {P = P} (⊆-trans τ τ′) ≗ Any-resp-⊆ τ′ ∘ Any-resp-⊆ τ
Any-resp-⊆-trans                (_ ∷ʳ τ′) i         = cong there (Any-resp-⊆-trans τ′ i)
Any-resp-⊆-trans {τ = _   ∷ʳ _} (_ ∷  τ′) i         = cong there (Any-resp-⊆-trans τ′ i)
Any-resp-⊆-trans {τ = _    ∷ _} (_ ∷  τ′) (there i) = cong there (Any-resp-⊆-trans τ′ i)
Any-resp-⊆-trans {τ = refl ∷ _} (_ ∷  τ′) (here _)  = refl
Any-resp-⊆-trans {τ = []      } []        ()

lookup-⊆-trans = Any-resp-⊆-trans

------------------------------------------------------------------------
-- The `lookup` function for `xs ⊆ ys` is injective.
--
-- Note: `lookup` can be seen as a strictly increasing reindexing function
-- for indices into `xs`, producing indices into `ys`.

private variable i j : Any P xs

lookup-injective : lookup τ i ≡ lookup τ j → i ≡ j
lookup-injective {τ = []}      {i = ()}
lookup-injective {τ = _  ∷ʳ _}                             = lookup-injective ∘′ there-injective
lookup-injective {τ = x≡y ∷ _} {i = here  _} {j = here  _} = cong here ∘′ subst-injective x≡y ∘′ here-injective
lookup-injective {τ = _   ∷ _} {i = there _} {j = there _} = cong there ∘′ lookup-injective ∘′ there-injective
