------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Properties
  {a} {A : Set a} where

open import Data.List using (List; []; _∷_;  map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties
  using (here-injective; there-injective)
open import Data.List.Relation.Binary.Sublist.Propositional
  hiding (map)
import Data.List.Relation.Binary.Sublist.Setoid.Properties
  as SetoidProperties
open import Function.Core
open import Level using (Level)
open import Relation.Binary using (_Respects_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

private
  variable
    b ℓ : Level
    B : Set b

------------------------------------------------------------------------
-- Re-exporting setoid properties

open SetoidProperties (setoid A) public
  hiding (map⁺)

map⁺ : ∀ {as bs} (f : A → B) → as ⊆ bs → map f as ⊆ map f bs
map⁺ {B = B} f = SetoidProperties.map⁺ (setoid A) (setoid B) (cong f)

------------------------------------------------------------------------
-- Category laws for _⊆_

⊆-trans-idˡ : ∀ {xs ys : List A} {τ : xs ⊆ ys} →
              ⊆-trans ⊆-refl τ ≡ τ
⊆-trans-idˡ {_}     {τ = []    } = refl
⊆-trans-idˡ {_}     {τ = _ ∷  _} = cong (_ ∷_ ) ⊆-trans-idˡ
⊆-trans-idˡ {[]}    {τ = _ ∷ʳ _} = cong (_ ∷ʳ_) ⊆-trans-idˡ
⊆-trans-idˡ {_ ∷ _} {τ = _ ∷ʳ _} = cong (_ ∷ʳ_) ⊆-trans-idˡ

⊆-trans-idʳ : ∀ {xs ys : List A} {τ : xs ⊆ ys} →
              ⊆-trans τ ⊆-refl ≡ τ
⊆-trans-idʳ {τ = []      } = refl
⊆-trans-idʳ {τ = _ ∷ʳ _  } = cong (_  ∷ʳ_ ) ⊆-trans-idʳ
⊆-trans-idʳ {τ = refl ∷ _} = cong (refl ∷_) ⊆-trans-idʳ

-- Note: The associativity law is oriented such that rewriting with it
-- may trigger reductions of ⊆-trans, which matches first on its
-- second argument and then on its first argument.

⊆-trans-assoc : ∀ {ws xs ys zs : List A}
                {τ₁ : ws ⊆ xs} {τ₂ : xs ⊆ ys} {τ₃ : ys ⊆ zs} →
                ⊆-trans τ₁ (⊆-trans τ₂ τ₃) ≡ ⊆-trans (⊆-trans τ₁ τ₂) τ₃
⊆-trans-assoc {τ₁ = _}        {_}      {_ ∷ʳ _} = cong (_ ∷ʳ_) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = _}        {_ ∷ʳ _} {_ ∷  _} = cong (_ ∷ʳ_) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = _ ∷ʳ _  } {_ ∷  _} {_ ∷  _} = cong (_ ∷ʳ_) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = refl ∷ _} {_ ∷  _} {_ ∷  _} = cong (_ ∷_ ) ⊆-trans-assoc
⊆-trans-assoc {τ₁ = []}       {[]}     {[]}     = refl

------------------------------------------------------------------------
-- Relationships to other predicates

-- All P is a contravariant functor from _⊆_ to Set.

All-resp-⊆ : {P : Pred A ℓ} → (All P) Respects _⊇_
All-resp-⊆ []          []       = []
All-resp-⊆ (_    ∷ʳ p) (_ ∷ xs) = All-resp-⊆ p xs
All-resp-⊆ (refl ∷  p) (x ∷ xs) = x ∷ All-resp-⊆ p xs

-- Any P is a covariant functor from _⊆_ to Set.

Any-resp-⊆ : {P : Pred A ℓ} → (Any P) Respects _⊆_
Any-resp-⊆ = lookup

------------------------------------------------------------------------
-- Functor laws for All-resp-⊆

-- First functor law: identity.

All-resp-⊆-refl : ∀ {P : Pred A ℓ} {xs : List A} →
                  All-resp-⊆ ⊆-refl ≗ id {A = All P xs}
All-resp-⊆-refl []       = refl
All-resp-⊆-refl (p ∷ ps) = cong (p ∷_) (All-resp-⊆-refl ps)

-- Second functor law: composition.

All-resp-⊆-trans : ∀ {P : Pred A ℓ} {xs ys zs} {τ : xs ⊆ ys} (τ′ : ys ⊆ zs) →
                   All-resp-⊆ {P = P} (⊆-trans τ τ′) ≗ All-resp-⊆ τ ∘ All-resp-⊆ τ′
All-resp-⊆-trans                (_    ∷ʳ τ′) (p ∷ ps) = All-resp-⊆-trans τ′ ps
All-resp-⊆-trans {τ = _ ∷ʳ _  } (refl ∷  τ′) (p ∷ ps) = All-resp-⊆-trans τ′ ps
All-resp-⊆-trans {τ = refl ∷ _} (refl ∷  τ′) (p ∷ ps) = cong (p ∷_) (All-resp-⊆-trans τ′ ps)
All-resp-⊆-trans {τ = []      } ([]        ) []       = refl

------------------------------------------------------------------------
-- Functor laws for Any-resp-⊆ / lookup

-- First functor law: identity.

Any-resp-⊆-refl : ∀ {P : Pred A ℓ} {xs} →
                  Any-resp-⊆ ⊆-refl ≗ id {A = Any P xs}
Any-resp-⊆-refl (here p)  = refl
Any-resp-⊆-refl (there i) = cong there (Any-resp-⊆-refl i)

lookup-⊆-refl = Any-resp-⊆-refl

-- Second functor law: composition.

Any-resp-⊆-trans : ∀ {P : Pred A ℓ} {xs ys zs} {τ : xs ⊆ ys} (τ′ : ys ⊆ zs) →
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

lookup-injective : ∀ {P : Pred A ℓ} {xs ys} {τ : xs ⊆ ys} {i j : Any P xs} →
                   lookup τ i ≡ lookup τ j → i ≡ j
lookup-injective {τ = _   ∷ʳ _}                     = lookup-injective ∘′ there-injective
lookup-injective {τ = refl ∷ _} {here  _} {here  _} = cong here ∘′ here-injective
lookup-injective {τ = _    ∷ _} {there _} {there _} = cong there ∘′ lookup-injective ∘′ there-injective

------------------------------------------------------------------------
-- Weak pushout (wpo)

-- A raw pushout is a weak pushout if the pushout square commutes.

IsWeakPushout : ∀{xs ys zs : List A} {τ : xs ⊆ ys} {σ : xs ⊆ zs} →
                RawPushout τ σ → Set a
IsWeakPushout {τ = τ} {σ = σ} rpo =
  ⊆-trans τ (RawPushout.leg₁ rpo) ≡
  ⊆-trans σ (RawPushout.leg₂ rpo)

-- Joining two list extensions with ⊆-join produces a weak pushout.

⊆-joinˡ-is-wpo : ∀{xs ys zs : List A} {τ : xs ⊆ ys} {σ : xs ⊆ zs} →
                 IsWeakPushout (⊆-joinˡ τ σ)
⊆-joinˡ-is-wpo {τ = []} {σ = σ}
  rewrite ⊆-trans-idʳ {τ = σ}
        = ⊆-trans-idˡ {xs = []}
⊆-joinˡ-is-wpo {τ = y   ∷ʳ _}                = cong (y   ∷ʳ_) ⊆-joinˡ-is-wpo
⊆-joinˡ-is-wpo {τ = _   ∷  _} {σ = z   ∷ʳ _} = cong (z   ∷ʳ_) ⊆-joinˡ-is-wpo
⊆-joinˡ-is-wpo {τ = refl ∷ _} {σ = refl ∷ _} = cong (refl ∷_) ⊆-joinˡ-is-wpo
