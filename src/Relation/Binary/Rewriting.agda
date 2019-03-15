------------------------------------------------------------------------
-- The Agda standard library
--
-- Concepts from rewriting theory
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.Rewriting where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; ∃ ; _,_)
open import Data.Empty
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Nullary

IsNormalForm : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → (a : A) → Set _
IsNormalForm {A} {ℓ} {_⟶_} a = ¬ ∃ λ b → (a ⟶ b)

NormalForm : ∀ {A : Set} → {ℓ : Level} → (r : Rel A ℓ) → Set _
NormalForm {A} {ℓ} r = ∀ {a b}
  → IsNormalForm {A} {ℓ} {r} a
  → b ↔ a
  → b —↠ a
  where
    _—↠_ = Star r
    _↔_  = Star (SymClosure r)

Det : ∀ {a b ℓ₁ ℓ₂} → {A : Set a} → {B : Set b} → Rel B ℓ₁ → REL A B ℓ₂ → Set _
Det _≈_ _—→_ = ∀ {x y z} → x —→ y → x —→ z → y ≈ z

Deterministic : ∀ {a b ℓ} → {A : Set a} → {B : Set b} → REL A B ℓ → Set _
Deterministic = Det _≡_

EqConfluent : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
EqConfluent _—→_ = ∀ {A B C} → (A ↔ B × A ↔ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
    _—↠_ = Star _—→_
    _↔_ = Star (SymClosure _—→_)

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
