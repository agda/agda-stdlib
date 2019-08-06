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
-- A Union where the triangles commute is a
-- cospan in the slice category (_ ⊆ zs)

private
  variable
    xs ys zs : List A
    τ₁ : xs ⊆ zs
    τ₂ : ys ⊆ zs
    σ τ : ys ⊆ zs
    x y z : A

-- module _ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} where

record IsCospan (u : UpperBound τ₁ τ₂) : Set a where
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

variable
  c c' : Cospan τ₁ τ₂

record CospanMorphism (c c' : Cospan τ₁ τ₂) : Set a where
  field
    morphism : theUpperBound c ⊆ theUpperBound c'
    tri      : ⊆-trans morphism (sub c') ≡ sub c


module _ {x : A} (d : Disjoint τ₁ τ₂) (c : IsCospan (⊆-disjoint-union d)) where

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

⊆-disjoint-union-is-cospan : (d : Disjoint τ₁ τ₂) → IsCospan (⊆-disjoint-union d)
⊆-disjoint-union-is-cospan [] = record { tri₁ = refl ; tri₂ = refl }
⊆-disjoint-union-is-cospan (x    ∷ₙ d) = ∷ₙ-cospan d (⊆-disjoint-union-is-cospan d)
⊆-disjoint-union-is-cospan (refl ∷ₗ d) = ∷ₗ-cospan d (⊆-disjoint-union-is-cospan d)
⊆-disjoint-union-is-cospan (refl ∷ᵣ d) = ∷ᵣ-cospan d (⊆-disjoint-union-is-cospan d)

⊆-disjoint-union-cospan : Disjoint τ₁ τ₂ → Cospan τ₁ τ₂
⊆-disjoint-union-cospan d = record
  { upperBound = ⊆-disjoint-union d
  ; isCospan   = ⊆-disjoint-union-is-cospan d
  }

record CospanMorphism' {xs ys zs}
      {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} (c : Cospan τ₁ τ₂)
      {zs'} (σ : zs ⊆ zs')
      {τ₁' : xs ⊆ zs'} {τ₂' : ys ⊆ zs'} (c' : Cospan τ₁' τ₂')
      : Set a where
  field
    morphism : theUpperBound c ⊆ theUpperBound c'
    square   : ⊆-trans morphism (sub c') ≡ ⊆-trans (sub c) σ

-- aux : ∀
--       CospanMorphism' (⊆-disjoint-union-cospan d) (∷ˡ⁻ σ) c →
--       CospanMorphism' (⊆-disjoint-union-cospan (y ∷ₙ d)) σ c

⊆-trans-∷ˡ⁻ᵣ : ⊆-trans τ (∷ˡ⁻ σ) ≡ ⊆-trans (y ∷ʳ τ) σ
⊆-trans-∷ˡ⁻ᵣ {σ = x ∷ σ} = refl
⊆-trans-∷ˡ⁻ᵣ {σ = y ∷ʳ σ} = cong (y ∷ʳ_) ⊆-trans-∷ˡ⁻ᵣ

⊆-trans-∷ˡ⁻ₗ : ⊆-trans (∷ˡ⁻ τ) σ ≡ ∷ˡ⁻ (⊆-trans τ σ)
⊆-trans-∷ˡ⁻ₗ {σ = y ∷ʳ σ}                  = cong (y ∷ʳ_) ⊆-trans-∷ˡ⁻ₗ
⊆-trans-∷ˡ⁻ₗ {σ = refl ∷ σ} {τ = y   ∷ʳ τ} = cong (y ∷ʳ_) ⊆-trans-∷ˡ⁻ₗ
⊆-trans-∷ˡ⁻ₗ {σ = refl ∷ σ} {τ = refl ∷ τ} = refl

{-
_∷ᵣ-ub′_ : ∀ {x} {xs ys zs} {τ : x ∷ xs ⊆ zs} {σ : ys ⊆ zs} {y} →
         (x≡y : x ≡ y) → UpperBound (∷ˡ⁻ τ) σ → UpperBound τ {!!} -- (x≡y ∷ σ)
x≈y ∷ᵣ-ub′ u = {!!}
-- record
--   { sub  = {! refl ∷ u .sub !}
--   ; inj₁ = _   ∷ʳ u .inj₁
--   ; inj₂ = x≈y  ∷ u .inj₂
--   }
{-
ub1 : ∀ {x} {xs ys zs} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs} → UpperBound τ σ → UpperBound (∷ˡ⁻ τ) σ
ub1 {x} {xs} {ys} {zs} {τ} {σ} record{ theUpperBound = us ; sub = ρ ; inj₁ = τ' ; inj₂ = σ' } =
  ub us ρ τ' σ'
  where
  ub : ∀ {ys zs} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs} us (ρ : us ⊆ zs) (τ' : x ∷ xs ⊆ us) (σ' : ys ⊆ us) → UpperBound (∷ˡ⁻ τ) σ
  -- ub us ρ τ' σ' = {!!}
  ub (y ∷ us) ρ (y ∷ʳ τ') (y ∷ʳ σ') = ub us (∷ˡ⁻ ρ) τ' σ'
  ub {τ = z ∷ʳ τ} {σ = z ∷ʳ σ} (y ∷ us) (.z ∷ʳ ρ) (y ∷ʳ τ') (refl ∷ σ') =
    ∷ₙ-ub (ub (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ'))
  ub {τ = z ∷ʳ τ} {σ = z ∷ʳ σ} (z ∷ us) (refl ∷ ρ) (z ∷ʳ τ') (refl ∷ σ') = {! refl ∷ᵣ-ub (ub ? ? ? ?)!}
    -- ub {τ = {!τ!} }{σ = z ∷ʳ σ}(z ∷ us) (refl ∷ ρ) (y ∷ʳ τ') (refl ∷ σ')
  -- ∷ₙ-ub (ub (y ∷ us) {!!} (y ∷ʳ τ') (refl ∷ σ'))
  ub {τ = z   ∷ʳ τ} {σ = refl ∷ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') = {!!}
  ub {τ = refl ∷ τ} {σ = z   ∷ʳ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') = {!!}
  ub {τ = refl ∷ τ} {σ = refl ∷ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') = {!!}
  ub {τ = τ} {σ = σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') = {! aux τ σ !}
    -- where
    -- aux : ∀(τ
    --      : Data.List.Relation.Binary.Sublist.Heterogeneous.Core.Sublist _≡_
    --        (x ∷ xs) zs)
    --     (σ
    --      : Data.List.Relation.Binary.Sublist.Heterogeneous.Core.Sublist _≡_
    --        (y ∷ xs) zs) →
    --   Data.List.Relation.Binary.Sublist.Setoid.UpperBound (setoid A)
    --   (Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.∷ˡ⁻ τ)
    --   σ

  --   = {! _∷ᵣ-ub_ !} -- ub {!!} {!!} {!!} (refl ∷ σ')
  ub (x ∷ us) ρ (refl ∷ τ') (x ∷ʳ σ') = record
    { theUpperBound = us
    ; sub =  ∷ˡ⁻ ρ
    ; inj₁ = τ'
    ; inj₂ = σ'
    }
  ub (x ∷ us) ρ (refl ∷ τ') (refl ∷ σ') = record
    { theUpperBound = x ∷ us
    ; sub  = ρ
    ; inj₁ = x ∷ʳ τ'
    ; inj₂ = refl ∷ σ'
    }
  ub (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ')  =  record
    { theUpperBound = us
    ; sub  = {! ρ !}
    ; inj₁ = {! y ∷ʳ τ' !}
    ; inj₂ = {! refl ∷ σ' !}
    }
{-
ub1 {τ = τ} {σ = σ} record { theUpperBound = (y ∷ us) ; sub = ρ ; inj₁ = (y ∷ʳ τ') ; inj₂ = (.y ∷ʳ σ') } =
  ub1 {τ = τ} {σ = σ} record { sub = ∷ˡ⁻ ρ ; inj₁ = τ' ; inj₂ = σ' }
ub1 record { theUpperBound = .(y ∷ _) ; sub = ρ ; inj₁ = (y ∷ʳ τ') ; inj₂ = (x ∷ σ') } = {!!}
ub1 record { theUpperBound = (x ∷ us) ; sub = ρ ; inj₁ = (refl ∷ τ') ; inj₂ = (x ∷ʳ σ') } = record
  { theUpperBound = us
  ; sub =  ∷ˡ⁻ ρ
  ; inj₁ = τ'
  ; inj₂ = σ'
  }
ub1 record { theUpperBound = x ∷ us ; sub = ρ ; inj₁ = refl ∷ τ' ; inj₂ = refl ∷ σ' } = record
  { theUpperBound = x ∷ us
  ; sub  = ρ
  ; inj₁ = x ∷ʳ τ'
  ; inj₂ = refl ∷ σ'
  }

-- ub1 :  UpperBound τ σ → UpperBound (∷ˡ⁻ τ) σ
-- ub1 {σ = []} {τ = ()}
-- ub1 {σ = y ∷ʳ σ} {τ = .y ∷ʳ τ} u = {!!}
-- ub1 {σ = y ∷ʳ σ} {τ = refl ∷ τ} u = {!!}
-- ub1 {σ = refl ∷ σ} {τ = y ∷ʳ τ} u = {!!}
-- ub1 {σ = refl ∷ σ} {τ = refl ∷ τ} u = record
--   { theUpperBound = {!UpperBound.theUpperBound u!}
--   ; sub = {! UpperBound.sub u!}
--   ; inj₁ = {!UpperBound.inj₁ u!}
--   ; inj₂ = {!UpperBound.inj₂ u!}
--   }

-- ub1 {τ₁ = y ∷ʳ τ₁} u = {!u!}
-- ub1 {τ₁ = refl ∷ τ₁} u = record { sub = UpperBound.sub u ; inj₁ = {!!} ; inj₂ = {!UpperBound.inj₂ u!} }

∷ˡ⁻-ubₗ : UpperBound τ₁ τ₂ → UpperBound (∷ˡ⁻ τ₁) τ₂
∷ˡ⁻-ubₗ u = record
  { sub = UpperBound.sub u
  ; inj₁ = ∷ˡ⁻ (UpperBound.inj₁ u)
  ; inj₂ = UpperBound.inj₂ u
  }

cs1 : Cospan τ₁ τ₂ → Cospan (∷ˡ⁻ τ₁) τ₂
cs1 c = record
  { upperBound = ∷ˡ⁻-ubₗ (upperBound c)
  ; isCospan = record
    { tri₁ = trans ⊆-trans-∷ˡ⁻ₗ (cong ∷ˡ⁻ (tri₁ c))
    ; tri₂ = tri₂ c
    }
  }

-- -}
-- -}
-- -}
-- -}

{-
cs1 : ∀ {x} {xs ys zs} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs} →
      Cospan τ σ → Cospan (∷ˡ⁻ τ) σ
cs1 {x} {xs} {ys} {z} {τ} {σ}
  record
    { upperBound = record
      { theUpperBound = us
      ; sub = ρ
      ; inj₁ = τ'
      ; inj₂ = σ'
      }
    ; isCospan = record
      { tri₁ = refl
      ; tri₂ = refl
      }
    }
  =  cs us ρ τ' σ'
  where
  cs : ∀ us (ρ : us ⊆ zs) (τ' : x ∷ xs ⊆ us) (σ' : ys ⊆ us) →
       Cospan (∷ˡ⁻ (⊆-trans τ' ρ)) (⊆-trans σ' ρ)
  cs .(y ∷ _) ρ (y ∷ʳ τ') (.y ∷ʳ σ') = {! cs _ (∷ˡ⁻ ρ) τ' σ' !}
  cs .(y ∷ _) ρ (y ∷ʳ τ') (refl ∷ σ') = {!!}
  cs .(y ∷ _) ρ (refl ∷ τ') (y ∷ʳ σ') = {!!}
  cs .(_ ∷ _) ρ (refl ∷ τ') (refl ∷ σ') = {!!}
-}

cs1 : ∀ {x} {xs ys zs} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs} →
      Cospan τ σ → Cospan (∷ˡ⁻ τ) σ
cs1 {x} {xs} {ys} {z} {τ} {σ}
  record
    { upperBound = record
      { theUpperBound = us
      ; sub = ρ
      ; inj₁ = τ'
      ; inj₂ = σ'
      }
    ; isCospan = record
      { tri₁ = τ'∘ρ≡τ
      ; tri₂ = σ'∘ρ≡σ
      }
    }
  = cs {τ = τ} {σ} us ρ τ' σ' τ'∘ρ≡τ σ'∘ρ≡σ
  where
  cs : ∀ {ys zs} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs}
       us (ρ : us ⊆ zs) (τ' : x ∷ xs ⊆ us) (σ' : ys ⊆ us)
       (τ'∘ρ≡τ : ⊆-trans τ' ρ ≡ τ)
       (σ'∘ρ≡σ : ⊆-trans σ' ρ ≡ σ) →
       Cospan (∷ˡ⁻ τ) σ
  cs (y ∷ us) ρ (y ∷ʳ τ') (y ∷ʳ σ') refl refl = cs us (∷ˡ⁻ ρ) τ' σ' ⊆-trans-∷ˡ⁻ᵣ ⊆-trans-∷ˡ⁻ᵣ

  cs {τ = z ∷ʳ τ} {σ = z ∷ʳ σ} (y ∷ us) (.z ∷ʳ ρ) (y ∷ʳ τ') (refl ∷ σ') τ'∘ρ≡τ refl = {!!}
    -- σ'∘ρ≡σ = {! ∷ₙ-ub (cs (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ')) !}
  cs {σ = z ∷ʳ σ} _ (refl ∷ ρ) _ (refl ∷ σ') _ ()
  cs {τ = z   ∷ʳ τ} {σ = refl ∷ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') τ'∘ρ≡τ σ'∘ρ≡σ = {!!}
  cs {τ = refl ∷ τ} {σ = z   ∷ʳ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') τ'∘ρ≡τ σ'∘ρ≡σ = {!!}
  cs {τ = refl ∷ τ} {σ = refl ∷ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') τ'∘ρ≡τ σ'∘ρ≡σ = {!!}

  -- cs {τ = τ} {σ = σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') τ'∘ρ≡τ σ'∘ρ≡σ = {! aux τ σ !}

  cs (x ∷ us) ρ (refl ∷ τ') (x ∷ʳ σ') refl refl = record
    { upperBound = record
      { theUpperBound = us
      ; sub =  ∷ˡ⁻ ρ
      ; inj₁ = τ'
      ; inj₂ = σ'
      }
    ; isCospan = record
      { tri₁ = {! τ'∘ρ≡τ !}
      ; tri₂ = {! σ'∘ρ≡σ !}
      }
    }
  cs (x ∷ us) ρ (refl ∷ τ') (x ∷ʳ σ') τ'∘ρ≡τ σ'∘ρ≡σ = record
    { upperBound = record
      { theUpperBound = us
      ; sub =  ∷ˡ⁻ ρ
      ; inj₁ = τ'
      ; inj₂ = σ'
      }
    ; isCospan = record
      { tri₁ = {! τ'∘ρ≡τ !}
      ; tri₂ = {! σ'∘ρ≡σ !}
      }
    }
  cs (x ∷ us) ρ (refl ∷ τ') (refl ∷ σ') τ'∘ρ≡τ σ'∘ρ≡σ = record
    { upperBound = record
      { theUpperBound = x ∷ us
      ; sub  = ρ
      ; inj₁ = x ∷ʳ τ'
      ; inj₂ = refl ∷ σ'
      }
    ; isCospan = record
      { tri₁ = {! τ'∘ρ≡τ !}
      ; tri₂ = {! σ'∘ρ≡σ !}
      }
    }
  cs (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') τ'∘ρ≡τ σ'∘ρ≡σ =  record
    { upperBound = record
      { theUpperBound = us
      ; sub  = {! ρ !}
      ; inj₁ = {! y ∷ʳ τ' !}
      ; inj₂ = {! refl ∷ σ' !}
      }
    ; isCospan = record
      { tri₁ = {! τ'∘ρ≡τ !}
      ; tri₂ = {! σ'∘ρ≡σ !}
      }
    }

{-
foo : ∀{xs ys zs}
      {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} (d : Disjoint τ₁ τ₂)
      {zs'} (σ : zs ⊆ zs')
      {τ₁' : xs ⊆ zs'} {τ₂' : ys ⊆ zs'} (c : Cospan τ₁' τ₂') →
      CospanMorphism'  (⊆-disjoint-union-cospan d) σ c
foo [] σ c = record { morphism = minimum _ ; square = []⊆-irrelevant _ _ }
foo (y ∷ₙ d) σ c = let bar = foo d (∷ˡ⁻ σ) c in record
  { morphism = CospanMorphism'.morphism bar
  ; square = trans (CospanMorphism'.square bar) ⊆-trans-∷ˡ⁻ᵣ
  }
  where
  aux : ⊆-trans (UpperBound.sub (⊆-disjoint-union d)) (∷ˡ⁻ σ)
      ≡ ⊆-trans (UpperBound.sub (⊆-disjoint-union (y ∷ₙ d))) σ
  aux = {!!}
foo (x≈y ∷ₗ d) σ c = let bar = foo d (∷ˡ⁻ σ) (cs1 c) in record
  { morphism = ⊆-trans {!!} (CospanMorphism'.morphism bar)
  ; square = {!!}
  }
foo (x≈y ∷ᵣ d) σ c = record { morphism = {!!} ; square = {!!} }

⊆-disjoint-union-minimal : (d : Disjoint τ₁ τ₂) (c : Cospan τ₁ τ₂) →
  CospanMorphism (⊆-disjoint-union-cospan d) c
⊆-disjoint-union-minimal [] c = record
  { morphism = minimum _
  ; tri      = []⊆-irrelevant _ _
  }
⊆-disjoint-union-minimal (y ∷ₙ d) c = {!!}
⊆-disjoint-union-minimal (x≈y ∷ₗ d) c = {!!}
⊆-disjoint-union-minimal (x≈y ∷ᵣ d) c = {!!}


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
