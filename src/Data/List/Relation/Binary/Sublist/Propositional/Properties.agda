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
open import Data.Product using (∃; _,_; proj₂)
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
-- Laws concerning ⊆-trans and ∷ˡ⁻

⊆-trans-∷ˡ⁻ᵣ : ∀ {y} {xs ys zs : List A} {τ : xs ⊆ ys} {σ : (y ∷ ys) ⊆ zs} →
               ⊆-trans τ (∷ˡ⁻ σ) ≡ ⊆-trans (y ∷ʳ τ) σ
⊆-trans-∷ˡ⁻ᵣ {σ = x ∷ σ} = refl
⊆-trans-∷ˡ⁻ᵣ {σ = y ∷ʳ σ} = cong (y ∷ʳ_) ⊆-trans-∷ˡ⁻ᵣ

⊆-trans-∷ˡ⁻ₗ : ∀ {x} {xs ys zs : List A} {τ : (x ∷ xs) ⊆ ys} {σ : ys ⊆ zs} →
              ⊆-trans (∷ˡ⁻ τ) σ ≡ ∷ˡ⁻ (⊆-trans τ σ)
⊆-trans-∷ˡ⁻ₗ                {σ = y   ∷ʳ σ} = cong (y ∷ʳ_) ⊆-trans-∷ˡ⁻ₗ
⊆-trans-∷ˡ⁻ₗ {τ = y   ∷ʳ τ} {σ = refl ∷ σ} = cong (y ∷ʳ_) ⊆-trans-∷ˡ⁻ₗ
⊆-trans-∷ˡ⁻ₗ {τ = refl ∷ τ} {σ = refl ∷ σ} = refl

⊆-∷ˡ⁻trans-∷ : ∀ {y} {xs ys zs : List A} {τ : xs ⊆ ys} {σ : (y ∷ ys) ⊆ zs} →
               ∷ˡ⁻ (⊆-trans (refl ∷ τ) σ) ≡ ⊆-trans (y ∷ʳ τ) σ
⊆-∷ˡ⁻trans-∷ {σ = y   ∷ʳ σ} = cong (y ∷ʳ_) ⊆-∷ˡ⁻trans-∷
⊆-∷ˡ⁻trans-∷ {σ = refl ∷ σ} = refl

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
lookup-injective {τ = _  ∷ʳ _}                     = lookup-injective ∘′ there-injective
lookup-injective {τ = x≡y ∷ _} {here  _} {here  _} = cong here ∘′ subst-injective x≡y ∘′ here-injective
  -- Note: instead of using subst-injective, we could match x≡y against refl on the lhs.
  -- However, this turns the following clause into a non-strict match.
lookup-injective {τ = _   ∷ _} {there _} {there _} = cong there ∘′ lookup-injective ∘′ there-injective

-------------------------------------------------------------------------
-- from∈ ∘ to∈ turns a sublist morphism τ : x∷xs ⊆ ys into a morphism
-- [x] ⊆ ys.  The same morphism is obtained by pre-composing τ with
-- the canonial morphism [x] ⊆ x∷xs.
--
-- Note: This lemma does not hold for Sublist.Setoid, but could hold for
-- a hypothetical Sublist.Groupoid where trans refl = id.

from∈∘to∈ : ∀ {x : A} {xs ys} (τ : x ∷ xs ⊆ ys) →
            from∈ (to∈ τ) ≡ ⊆-trans (refl ∷ minimum xs) τ
from∈∘to∈ (x≡y ∷ τ) = cong (x≡y ∷_) ([]⊆-irrelevant _ _)
from∈∘to∈ (y  ∷ʳ τ) = cong (y  ∷ʳ_) (from∈∘to∈ τ)

------------------------------------------------------------------------
-- Weak pushout (wpo)

-- A raw pushout is a weak pushout if the pushout square commutes.

IsWeakPushout : ∀{xs ys zs : List A} {τ : xs ⊆ ys} {σ : xs ⊆ zs} →
                RawPushout τ σ → Set a
IsWeakPushout {τ = τ} {σ = σ} rpo =
  ⊆-trans τ (RawPushout.leg₁ rpo) ≡
  ⊆-trans σ (RawPushout.leg₂ rpo)

-- Joining two list extensions with ⊆-pushout produces a weak pushout.

⊆-pushoutˡ-is-wpo : ∀{xs ys zs : List A} {τ : xs ⊆ ys} {σ : xs ⊆ zs} →
                 IsWeakPushout (⊆-pushoutˡ τ σ)
⊆-pushoutˡ-is-wpo {τ = []} {σ = σ}
  rewrite ⊆-trans-idʳ {τ = σ}
        = ⊆-trans-idˡ {xs = []}
⊆-pushoutˡ-is-wpo {τ = y   ∷ʳ _}                = cong (y   ∷ʳ_) ⊆-pushoutˡ-is-wpo
⊆-pushoutˡ-is-wpo {τ = _   ∷  _} {σ = z   ∷ʳ _} = cong (z   ∷ʳ_) ⊆-pushoutˡ-is-wpo
⊆-pushoutˡ-is-wpo {τ = refl ∷ _} {σ = refl ∷ _} = cong (refl ∷_) ⊆-pushoutˡ-is-wpo

------------------------------------------------------------------------
-- Properties of disjointness

-- From τ ⊎ σ = ρ, compute the difference τ′ such that τ = ⊆-trans τ′ ρ.

DisjointUnion-diffˡ : ∀ {xs ys zs us : List A} {τ : xs ⊆ zs} {σ : ys ⊆ zs} {ρ : us ⊆ zs} →
                      DisjointUnion τ σ ρ → ∃ λ (τ′ : xs ⊆ us) → ⊆-trans τ′ ρ ≡ τ
DisjointUnion-diffˡ []         = []       , refl
DisjointUnion-diffˡ (y   ∷ₙ d) = _        , cong (y  ∷ʳ_) (proj₂ (DisjointUnion-diffˡ d))
DisjointUnion-diffˡ (x≈y ∷ₗ d) = refl ∷ _ , cong (x≈y ∷_) (proj₂ (DisjointUnion-diffˡ d))
DisjointUnion-diffˡ (x≈y ∷ᵣ d) = _ ∷ʳ _   , cong (_  ∷ʳ_) (proj₂ (DisjointUnion-diffˡ d))

-- From τ ⊎ σ = ρ, compute the difference σ′ such that σ = ⊆-trans σ′ ρ.

DisjointUnion-diffʳ : ∀ {xs ys zs us : List A} {τ : xs ⊆ zs} {σ : ys ⊆ zs} {ρ : us ⊆ zs} →
                      DisjointUnion τ σ ρ → ∃ λ (σ′ : ys ⊆ us) → ⊆-trans σ′ ρ ≡ σ
DisjointUnion-diffʳ []         = []       , refl
DisjointUnion-diffʳ (y   ∷ₙ d) = _        , cong (y  ∷ʳ_) (proj₂ (DisjointUnion-diffʳ d))
DisjointUnion-diffʳ (x≈y ∷ᵣ d) = refl ∷ _ , cong (x≈y ∷_) (proj₂ (DisjointUnion-diffʳ d))
DisjointUnion-diffʳ (x≈y ∷ₗ d) = _ ∷ʳ _   , cong (_  ∷ʳ_) (proj₂ (DisjointUnion-diffʳ d))

------------------------------------------------------------------------
-- A Union where the triangles commute is a
-- Cospan in the slice category (_ ⊆ zs).

record IsCospan {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} (u : UpperBound τ₁ τ₂) : Set a where
  field
    tri₁ : ⊆-trans (UpperBound.inj₁ u) (UpperBound.sub u) ≡ τ₁
    tri₂ : ⊆-trans (UpperBound.inj₂ u) (UpperBound.sub u) ≡ τ₂

record Cospan {xs ys zs : List A} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) : Set a where
  field
    upperBound : UpperBound τ₁ τ₂
    isCospan   : IsCospan upperBound

  open UpperBound upperBound public
  open IsCospan isCospan public

open IsCospan
open Cospan

module _
  {x : A} {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs}
  (d : Disjoint τ₁ τ₂) (c : IsCospan (⊆-disjoint-union d)) where

  ∷ₙ-cospan : IsCospan (⊆-disjoint-union (x ∷ₙ d))
  ∷ₙ-cospan = record
    { tri₁ = cong (x ∷ʳ_) (c .tri₁)
    ; tri₂ = cong (x ∷ʳ_) (c .tri₂)
    }

  ∷ₗ-cospan : IsCospan (⊆-disjoint-union (refl {x = x} ∷ₗ d))
  ∷ₗ-cospan = record
    { tri₁ = cong (refl ∷_) (c .tri₁)
    ; tri₂ = cong (x   ∷ʳ_) (c .tri₂)
    }

  ∷ᵣ-cospan : IsCospan (⊆-disjoint-union (refl {x = x} ∷ᵣ d))
  ∷ᵣ-cospan = record
    { tri₁ = cong (x   ∷ʳ_) (c .tri₁)
    ; tri₂ = cong (refl ∷_) (c .tri₂)
    }

⊆-disjoint-union-is-cospan : ∀ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  (d : Disjoint τ₁ τ₂) → IsCospan (⊆-disjoint-union d)
⊆-disjoint-union-is-cospan [] = record { tri₁ = refl ; tri₂ = refl }
⊆-disjoint-union-is-cospan (x    ∷ₙ d) = ∷ₙ-cospan d (⊆-disjoint-union-is-cospan d)
⊆-disjoint-union-is-cospan (refl ∷ₗ d) = ∷ₗ-cospan d (⊆-disjoint-union-is-cospan d)
⊆-disjoint-union-is-cospan (refl ∷ᵣ d) = ∷ᵣ-cospan d (⊆-disjoint-union-is-cospan d)

⊆-disjoint-union-cospan : ∀ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  Disjoint τ₁ τ₂ → Cospan τ₁ τ₂
⊆-disjoint-union-cospan d = record
  { upperBound = ⊆-disjoint-union d
  ; isCospan   = ⊆-disjoint-union-is-cospan d
  }
