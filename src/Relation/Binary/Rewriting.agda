------------------------------------------------------------------------
-- The Agda standard library
--
-- Concepts from rewriting theory
-- Definitions are based on "Term Rewriting Systems" by J.W. Klop
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Rewriting where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Product using (_×_ ; ∃ ; -,_; _,_ ; proj₁ ; proj₂)
open import Data.Empty
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (flip; _∘′_)
open import Induction.WellFounded
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Construct.Closure.Reflexive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as RTrans
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary

-- The following definitions are taken from Klop [5]
module _ {a ℓ} {A : Set a} (_⟶_ : Rel A ℓ) where

  private
    _⟵_  = flip _⟶_
    _—↠_ = Star _⟶_
    _↔_  = Star (SymClosure _⟶_)

  IsNormalForm : A → Set _
  IsNormalForm a = ¬ ∃ λ b → (a ⟶ b)

  HasNormalForm : A → Set _
  HasNormalForm b = ∃ λ a → IsNormalForm a × (b —↠ a)

  NormalForm : Set _
  NormalForm = ∀ {a b} → IsNormalForm a → b ↔ a → b —↠ a

  WeaklyNormalizing : Set _
  WeaklyNormalizing = ∀ a → HasNormalForm a

  StronglyNormalizing : Set _
  StronglyNormalizing = WellFounded _⟵_

  UniqueNormalForm : Set _
  UniqueNormalForm = ∀ {a b} → IsNormalForm a → IsNormalForm b → a ↔ b → a ≡ b

  Confluent : Set _
  Confluent = ∀ {A B C} → A —↠ B → A —↠ C → ∃ λ D → (B —↠ D) × (C —↠ D)

  WeaklyConfluent : Set _
  WeaklyConfluent = ∀ {A B C} → A ⟶ B → A ⟶ C → ∃ λ D → (B —↠ D) × (C —↠ D)


Deterministic : ∀ {a b ℓ₁ ℓ₂} → {A : Set a} → {B : Set b} → Rel B ℓ₁ → REL A B ℓ₂ → Set _
Deterministic _≈_ _—→_ = ∀ {x y z} → x —→ y → x —→ z → y ≈ z

module _ {a ℓ} {A : Set a} {_⟶_ : Rel A ℓ} where

  private
    _—↠_ = Star _⟶_
    _↔_  = Star (SymClosure _⟶_)
    _⟶₊_ = Plus _⟶_

  det⟶conf : Deterministic _≡_ _⟶_ → Confluent _⟶_
  det⟶conf det ε          rs₂        = -, rs₂ , ε
  det⟶conf det rs₁        ε          = -, ε , rs₁
  det⟶conf det (r₁ ◅ rs₁) (r₂ ◅ rs₂)
    rewrite det r₁ r₂ = det⟶conf det rs₁ rs₂

  conf⟶wcr : Confluent _⟶_ → WeaklyConfluent _⟶_
  conf⟶wcr c fst snd = c (fst ◅ ε) (snd ◅ ε)

  conf⟶nf : Confluent _⟶_ → NormalForm _⟶_
  conf⟶nf c aIsNF ε = ε
  conf⟶nf c aIsNF (fwd x ◅ rest) = x ◅ conf⟶nf c aIsNF rest
  conf⟶nf c aIsNF (bwd y ◅ rest) with c (y ◅ ε) (conf⟶nf c aIsNF rest)
  ... | _ , _    , x ◅ _ = ⊥-elim (aIsNF (_ , x))
  ... | _ , left , ε     = left

  conf⟶unf : Confluent _⟶_ → UniqueNormalForm _⟶_
  conf⟶unf _ _     _     ε           = refl
  conf⟶unf _ aIsNF _     (fwd x ◅ _) = ⊥-elim (aIsNF (_ , x))
  conf⟶unf c aIsNF bIsNF (bwd y ◅ r) with c (y ◅ ε) (conf⟶nf c bIsNF r)
  ... | _ , ε     , x ◅ _ = ⊥-elim (bIsNF (_ , x))
  ... | _ , x ◅ _ , _     = ⊥-elim (aIsNF (_ , x))
  ... | _ , ε     , ε     = refl

  un&wn⟶cr : UniqueNormalForm _⟶_ → WeaklyNormalizing _⟶_ → Confluent _⟶_
  un&wn⟶cr un wn = helper where

    helper : ∀ {a b c} → a —↠ b → a —↠ c → ∃ λ d → (b —↠ d) × (c —↠ d)
    helper {_} {b} {c} aToB aToC with (wn b , wn c)
    ... | (bNF , (e , x)) , (_ , (f , y)) with bNF≡cNF

     where

        forwards : ∀ {a b} → a —↠ b → a ↔ b
        forwards = RTrans.map inj₁

        backwards : ∀ {a b} → a —↠ b → b ↔ a
        backwards = RTrans.reverse (symmetric _⟶_) ∘′ forwards

        lemma : ∀ {a b c} → a —↠ b → a —↠ c → b ↔ c
        lemma t b = backwards t ◅◅ forwards b

        bNF≡cNF = un e f (lemma (aToB ◅◅ x) (aToC ◅◅ y))

    ... | refl = bNF , x , y


-- Newman's lemma
  sn⟶wcr⟶cr : StronglyNormalizing (Plus _⟶_) → WeaklyConfluent _⟶_ → Confluent _⟶_
  sn⟶wcr⟶cr sn wcr = helper (sn _) where

    starToPlus : ∀ {a b c} → (a ⟶ b) → b —↠ c → a ⟶₊ c
    starToPlus aToB ε = [ aToB ]
    starToPlus {a} aToB (e ◅ bToC) = a ∼⁺⟨ [ aToB ] ⟩ (starToPlus e bToC)

    helper : ∀ {a b c} → (acc : Acc (flip _⟶₊_) a) →
             a —↠ b → a —↠ c → ∃ λ d → (b —↠ d) × (c —↠ d)
    helper _       ε           snd         = -, snd , ε
    helper _       fst         ε           = -, ε   , fst
    helper (acc g) (toJ ◅ fst) (toK ◅ snd) = result where

        wcrProof = wcr toJ toK
        innerPoint = proj₁ wcrProof
        jToInner = proj₁ (proj₂ wcrProof)
        kToInner = proj₂ (proj₂ wcrProof)

        lhs = helper (g _ [ toJ ]) fst jToInner
        rhs = helper (g _ [ toK ]) snd kToInner

        fromAB = proj₁ (proj₂ lhs)
        fromInnerB = proj₂ (proj₂ lhs)

        fromAC = proj₁ (proj₂ rhs)
        fromInnerC = proj₂ (proj₂ rhs)

        aToInner : _ ⟶₊ innerPoint
        aToInner = starToPlus toJ jToInner

        finalRecursion = helper (g innerPoint aToInner) fromInnerB fromInnerC

        bMidToDest = proj₁ (proj₂ finalRecursion)
        cMidToDest = proj₂ (proj₂ finalRecursion)

        result : ∃ λ d → (_ —↠ d) × (_ —↠ d)
        result = _ , fromAB ◅◅ bMidToDest , fromAC ◅◅ cMidToDest
