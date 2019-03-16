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
IsNormalForm : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → (a : A) → Set _
IsNormalForm {A} {ℓ} {_⟶_} a = ¬ ∃ λ b → (a ⟶ b)

HasNormalForm : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → (b : A) → Set _
HasNormalForm {A} {ℓ} {_⟶_} b = ∃ λ a → ( IsNormalForm {A} {ℓ} {_⟶_} a × (b —↠ a))
  where
    _—↠_ = Star _⟶_

NormalForm : ∀ {A : Set} → {ℓ : Level} → (r : Rel A ℓ) → Set _
NormalForm {A} {ℓ} r = ∀ {a b}
  → IsNormalForm {A} {ℓ} {r} a
  → b ↔ a
  → b —↠ a
  where
    _—↠_ = Star r
    _↔_  = Star (SymClosure r)

WeaklyNormalizing : ∀ {A : Set} → {ℓ : Level} → (r : Rel A ℓ) → Set _
WeaklyNormalizing {A} {ℓ} r = ∀ a → HasNormalForm {A} {ℓ} {r} a

UniqueNormalForm : ∀ {A : Set} → {ℓ : Level} → (r : Rel A ℓ) → Set _
UniqueNormalForm {A} {ℓ} r = ∀ {a b}
  → IsNormalForm {A} {ℓ} {r} a
  → IsNormalForm {A} {ℓ} {r} b
  → a ↔ b
  → a ≡ b
  where
    _↔_ = Star (SymClosure r)

Det : ∀ {a b ℓ₁ ℓ₂} → {A : Set a} → {B : Set b} → Rel B ℓ₁ → REL A B ℓ₂ → Set _
Det _≈_ _—→_ = ∀ {x y z} → x —→ y → x —→ z → y ≈ z

Deterministic : ∀ {a b ℓ} → {A : Set a} → {B : Set b} → REL A B ℓ → Set _
Deterministic = Det _≡_

Confluent : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
Confluent _—→_ = ∀ {A B C} → (A —↠ B × A —↠ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
     _—↠_ = Star _—→_

Diamond : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
Diamond _—→_ = ∀ {A B C} → (A —→ B × A —→ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
    _—↠_ = Star _—→_

det⟶conf : ∀ {A : Set}
  → {ℓ : Level}
  → {r : Rel A ℓ}
  → Deterministic r
  → Confluent r
det⟶conf f (ε , snd)                         = _ , snd , ε
det⟶conf f (a ◅ fst , ε)                     = _ , ε , a ◅ fst
det⟶conf f (a ◅ fst , b ◅ snd) rewrite f a b = det⟶conf f ( fst , snd )

conf⟶diamond : ∀ {A : Set}
  → {ℓ : Level}
  → {r : Rel A ℓ}
  → Confluent r
  → Diamond r
conf⟶diamond c (fst , snd) = c (fst ◅ ε , snd ◅ ε)

conf⟶nf : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ}
  → Confluent r
  → NormalForm r
conf⟶nf c aIsNF ε = ε
conf⟶nf c aIsNF (fwd x ◅ r) = x ◅ conf⟶nf c aIsNF r
conf⟶nf c aIsNF (bwd y ◅ rest) with c (y ◅ ε , (conf⟶nf c aIsNF rest))
conf⟶nf c aIsNF (bwd y ◅ rest) | dest , _    , x ◅ _ = ⊥-elim (aIsNF (_ , x))
conf⟶nf c aIsNF (bwd y ◅ rest) | dest , left , ε     = left

conf⟶unf : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ}
  → Confluent r
  → UniqueNormalForm r
conf⟶unf c aIsNF bIsNF ε = refl
conf⟶unf c aIsNF bIsNF (fwd x ◅ _) = ⊥-elim (aIsNF (_ , x))
conf⟶unf c aIsNF bIsNF (bwd y ◅ r) with c (y ◅ ε , (conf⟶nf c bIsNF r))
conf⟶unf c aIsNF bIsNF (bwd y ◅ r) | dest , ε , ε = refl
conf⟶unf c aIsNF bIsNF (bwd y ◅ r) | dest , ε , x ◅ _ = ⊥-elim (bIsNF (_ , x))
conf⟶unf c aIsNF bIsNF (bwd y ◅ r) | dest , x ◅ _ , _ = ⊥-elim (aIsNF (_ , x))

un&wn⟶cr : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ}
  → UniqueNormalForm r
  → WeaklyNormalizing r
  → Confluent r
un&wn⟶cr {A} {ℓ} {r} un wn = helper
  where
    helper : ∀ {a b c : A}
      → (Star r a b × Star r a c) → ∃ λ d → (Star r b d) × (Star r c d)
    helper {a} {b} {c} _ with (wn b , wn c)
    helper (aToB , aToC) | (_ , (e , x)) , (_ , (f , y)) with bNF≡cNF
      where
        forwards : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → {a b : A}
          → Star r a b
          → Star (SymClosure r) a b
        forwards ε = ε
        forwards (x ◅ y) = fwd x ◅ forwards y

        back : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → {a b : A}
          → Star r a b
          → Star (SymClosure r) b a
        back ε = ε
        back (x ◅ y) = back y ◅◅ bwd x ◅ ε

        lemma : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → {a b c : A}
          → Star r a b
          → Star r a c
          → Star (SymClosure r) b c
        lemma t b = back t ◅◅ forwards b

        bNF≡cNF = un e f (lemma (aToB ◅◅ x) (aToC ◅◅ y))

    helper _ | (bNF , (_ , x)) , (_ , (_ , y)) | refl = bNF , x , y
