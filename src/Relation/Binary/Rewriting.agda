------------------------------------------------------------------------
-- The Agda standard library
--
-- Concepts from rewriting theory
-- Definitions are based on "Term Rewriting Systems" by J.W. Klop
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.Rewriting where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Product using (_×_ ; ∃ ; _,_ ; proj₂)
open import Data.Empty
open import Data.Sum as Sum using (_⊎_)
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Nullary

-- The following definitions are taken from Klop [5]
IsNormalForm : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → A → Set _
IsNormalForm _⟶_ a = ¬ ∃ λ b → (a ⟶ b)

HasNormalForm : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → A → Set _
HasNormalForm _⟶_ b = ∃ λ a → ( IsNormalForm _⟶_ a × (b —↠ a))
  where
    _—↠_ = Star _⟶_

NormalForm : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → Set _
NormalForm _⟶_ = ∀ {a b}
  → IsNormalForm _⟶_ a
  → b ↔ a
  → b —↠ a
  where
    _—↠_ = Star _⟶_
    _↔_  = Star (SymClosure _⟶_)

WeaklyNormalizing : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → Set _
WeaklyNormalizing _⟶_ = ∀ a → HasNormalForm _⟶_ a

UniqueNormalForm : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → Set _
UniqueNormalForm _⟶_ = ∀ {a b}
  → IsNormalForm _⟶_ a
  → IsNormalForm _⟶_ b
  → a ↔ b
  → a ≡ b
  where
    _↔_ = Star (SymClosure _⟶_)

Deterministic : ∀ {a b ℓ₁ ℓ₂} → {A : Set a} → {B : Set b} → Rel B ℓ₁ → REL A B ℓ₂ → Set _
Deterministic _≈_ _—→_ = ∀ {x y z} → x —→ y → x —→ z → y ≈ z

Confluent : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → Set _
Confluent _⟶_ = ∀ {A B C} → (A —↠ B × A —↠ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
     _—↠_ = Star _⟶_

Diamond : ∀ {a ℓ} → {A : Set a} → Rel A ℓ → Set _
Diamond _⟶_ = ∀ {A B C} → (A ⟶ B × A ⟶ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
    _—↠_ = Star _⟶_

det⟶conf : ∀ {a ℓ} → {A : Set a}
  → {_⟶_ : Rel A ℓ}
  → Deterministic _≡_ _⟶_
  → Confluent _⟶_
det⟶conf f (ε , snd)                         = _ , snd , ε
det⟶conf f (a ◅ fst , ε)                     = _ , ε , a ◅ fst
det⟶conf f (a ◅ fst , b ◅ snd) rewrite f a b = det⟶conf f ( fst , snd )

conf⟶diamond : ∀ {a ℓ} → {A : Set a} → {_⟶_ : Rel A ℓ} → Confluent _⟶_ → Diamond _⟶_
conf⟶diamond c (fst , snd) = c (fst ◅ ε , snd ◅ ε)

conf⟶nf : ∀ {a ℓ} → {A : Set a} → {_⟶_ : Rel A ℓ} → Confluent _⟶_ → NormalForm _⟶_
conf⟶nf c aIsNF ε = ε
conf⟶nf c aIsNF (fwd x ◅ rest) = x ◅ conf⟶nf c aIsNF rest
conf⟶nf c aIsNF (bwd y ◅ rest) with c (y ◅ ε , (conf⟶nf c aIsNF rest))
conf⟶nf _ aIsNF _ | _ , _    , x ◅ _ = ⊥-elim (aIsNF (_ , x))
...               | _ , left , ε     = left

conf⟶unf : ∀ {a ℓ} {A : Set a} → {_⟶_ : Rel A ℓ} → Confluent _⟶_ → UniqueNormalForm _⟶_
conf⟶unf _ _     _     ε           = refl
conf⟶unf _ aIsNF _     (fwd x ◅ _) = ⊥-elim (aIsNF (_ , x))
conf⟶unf c _     bIsNF (bwd y ◅ r) with c (y ◅ ε , (conf⟶nf c bIsNF r))
conf⟶unf _ _     bIsNF _ | _ , ε     , x ◅ _ = ⊥-elim (bIsNF (_ , x))
conf⟶unf _ aIsNF _     _ | _ , x ◅ _ , _     = ⊥-elim (aIsNF (_ , x))
...                      | _ , ε     , ε     = refl

un&wn⟶cr : ∀ {a ℓ} → (A : Set a) → (_⟶_ : Rel A ℓ) → UniqueNormalForm _⟶_ → WeaklyNormalizing _⟶_ → Confluent _⟶_
un&wn⟶cr A _⟶_ un wn = helper
  where
    _—↠_ = Star _⟶_
    _↔_  = Star (SymClosure _⟶_)

    helper : ∀ {a b c : A} → (a —↠ b × a —↠ c) → ∃ λ d → (b —↠ d) × (c —↠ d)
    helper {a} {b} {c} _ with (wn b , wn c)
    helper (aToB , aToC) | (_ , (e , x)) , (_ , (f , y)) with bNF≡cNF
      where
        forwards : ∀ {a b : A} → a —↠ b → a ↔ b
        forwards ε = ε
        forwards (x ◅ y) = fwd x ◅ forwards y

        back : ∀ {a b : A} → a —↠ b → b ↔ a
        back ε = ε
        back (x ◅ y) = back y ◅◅ bwd x ◅ ε

        lemma : ∀ {a b c : A} → a —↠ b → a —↠ c → b ↔ c
        lemma t b = back t ◅◅ forwards b

        bNF≡cNF = un e f (lemma (aToB ◅◅ x) (aToC ◅◅ y))

    helper _ | (bNF , x) , (_ , y) | refl = bNF , proj₂ x , proj₂ y
