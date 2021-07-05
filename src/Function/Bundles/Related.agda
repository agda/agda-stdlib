------------------------------------------------------------------------

-- The Agda standard library
--
-- Relatedness for the function hierarchy
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Bundles.Related where

open import Level
open import Relation.Binary using (Sym; Reflexive; Trans; IsEquivalence; Setoid; IsPreorder; Preorder)
open import Function.Bundles
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as Eq
import Function.Injection   as Inj
import Function.Inverse     as Inv
import Function.LeftInverse as LeftInv
import Function.Surjection  as Surj
import Relation.Binary.PropositionalEquality as P
open import Function.Properties.Bijection
open import Function.Properties.Surjection
open import Function.Properties.Inverse
open import Function.Properties.RightInverse

import Function.Construct.Symmetry as Symmetry
import Function.Construct.Identity as Identity
import Function.Construct.Composition as Composition

open import Data.Product

------------------------------------------------------------------------
-- Relatedness

-- There are several kinds of "relatedness".

-- The idea to include kinds other than equivalence and bijection came
-- from Simon Thompson and Bengt Nordström. /NAD

data Kind : Set where
  implication         : Kind
  reverse-implication : Kind
  equivalence         : Kind
  injection           : Kind
  reverse-injection   : Kind
  left-inverse        : Kind
  surjection          : Kind
  bijection           : Kind

-- Interpretation of the codes above. The code "bijection" is
-- interpreted as Inverse rather than Bijection; the two types are
-- equivalent.

infix 4 _∼[_]_

_∼[_]_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Kind → Set ℓ₂ → Set _
A ∼[ implication         ] B = A ⟶ B
A ∼[ reverse-implication ] B = B ⟶ A
A ∼[ equivalence         ] B = A ⇔ B
A ∼[ injection           ] B = A ↣ B
A ∼[ reverse-injection   ] B = B ↣ A
A ∼[ left-inverse        ] B = A ↪ B
A ∼[ surjection          ] B = A ↠ B
A ∼[ bijection           ] B = A ⤖ B

-- A non-infix synonym.

Related : Kind → ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
Related k A B = A ∼[ k ] B

-- The bijective equality implies any kind of relatedness.

⤖⇒ : ∀ {k x y} {X : Set x} {Y : Set y} →
     X ∼[ bijection ] Y → X ∼[ k ] Y
⤖⇒ {implication}         = mk⟶ ∘ Bijection.f
⤖⇒ {reverse-implication} = mk⟶ ∘ Inverse.f⁻¹ ∘ ⤖⇒↔
⤖⇒ {equivalence}         = ⤖⇒⇔
⤖⇒ {injection}           = Bijection.injection
⤖⇒ {reverse-injection}   = Bijection.injection ∘ ↔⇒⤖ ∘ Symmetry.inverse ∘ ⤖⇒↔
⤖⇒ {left-inverse}        = Inverse.rightInverse ∘ ⤖⇒↔
⤖⇒ {surjection}          = Bijection.surjection
⤖⇒ {bijection}           = id

-- Actual equality also implies any kind of relatedness.

≡⇒ : ∀ {k ℓ} {X Y : Set ℓ} → X P.≡ Y → X ∼[ k ] Y
≡⇒ P.refl = ⤖⇒ (Identity.id-⤖ _)

------------------------------------------------------------------------
-- Special kinds of kinds

-- Kinds whose interpretation is symmetric.

data Symmetric-kind : Set where
  equivalence : Symmetric-kind
  bijection   : Symmetric-kind

-- Forgetful map.

⌊_⌋ : Symmetric-kind → Kind
⌊ equivalence ⌋ = equivalence
⌊ bijection   ⌋ = bijection

-- The proof of symmetry can be found below.

-- Kinds whose interpretation include a function which "goes in the
-- forward direction".

data Forward-kind : Set where
  implication  : Forward-kind
  equivalence  : Forward-kind
  injection    : Forward-kind
  left-inverse : Forward-kind
  surjection   : Forward-kind
  bijection    : Forward-kind

-- Forgetful map.

⌊_⌋→ : Forward-kind → Kind
⌊ implication  ⌋→ = implication
⌊ equivalence  ⌋→ = equivalence
⌊ injection    ⌋→ = injection
⌊ left-inverse ⌋→ = left-inverse
⌊ surjection   ⌋→ = surjection
⌊ bijection    ⌋→ = bijection

-- The function.

⇒→ : ∀ {k x y} {X : Set x} {Y : Set y} → X ∼[ ⌊ k ⌋→ ] Y → X → Y
⇒→ {implication}  = Func.f
⇒→ {equivalence}  = Equivalence.f
⇒→ {injection}    = Injection.f
⇒→ {left-inverse} = RightInverse.f
⇒→ {surjection}   = Surjection.f
⇒→ {bijection}    = Bijection.f

-- Kinds whose interpretation include a function which "goes backwards".

data Backward-kind : Set where
  reverse-implication : Backward-kind
  equivalence         : Backward-kind
  reverse-injection   : Backward-kind
  left-inverse        : Backward-kind
  surjection          : Backward-kind
  bijection           : Backward-kind

-- Forgetful map.

⌊_⌋← : Backward-kind → Kind
⌊ reverse-implication ⌋← = reverse-implication
⌊ equivalence         ⌋← = equivalence
⌊ reverse-injection   ⌋← = reverse-injection
⌊ left-inverse        ⌋← = left-inverse
⌊ surjection          ⌋← = surjection
⌊ bijection           ⌋← = bijection

-- The function.

⇒← : ∀ {k x y} {X : Set x} {Y : Set y} → X ∼[ ⌊ k ⌋← ] Y → Y → X
⇒← {reverse-implication} = Func.f
⇒← {equivalence}         = Equivalence.g
⇒← {reverse-injection}   = Injection.f
⇒← {left-inverse}        = RightInverse.g
⇒← {surjection}          = RightInverse.f ∘ ↠⇒↪
⇒← {bijection}           = Inverse.f⁻¹ ∘ ⤖⇒↔

-- Kinds whose interpretation include functions going in both
-- directions.

data Equivalence-kind : Set where
    equivalence  : Equivalence-kind
    left-inverse : Equivalence-kind
    surjection   : Equivalence-kind
    bijection    : Equivalence-kind

-- Forgetful map.

⌊_⌋⇔ : Equivalence-kind → Kind
⌊ equivalence  ⌋⇔ = equivalence
⌊ left-inverse ⌋⇔ = left-inverse
⌊ surjection   ⌋⇔ = surjection
⌊ bijection    ⌋⇔ = bijection

-- The functions.

⇒⇔ : ∀ {k x y} {X : Set x} {Y : Set y} →
     X ∼[ ⌊ k ⌋⇔ ] Y → X ∼[ equivalence ] Y
⇒⇔ {equivalence}  = id
⇒⇔ {left-inverse} = RightInverse.equivalence
⇒⇔ {surjection}   = ↠⇒⇔
⇒⇔ {bijection}    = ⤖⇒⇔

-- Conversions between special kinds.

⇔⌊_⌋ : Symmetric-kind → Equivalence-kind
⇔⌊ equivalence ⌋ = equivalence
⇔⌊ bijection   ⌋ = bijection

→⌊_⌋ : Equivalence-kind → Forward-kind
→⌊ equivalence  ⌋ = equivalence
→⌊ left-inverse ⌋ = left-inverse
→⌊ surjection   ⌋ = surjection
→⌊ bijection    ⌋ = bijection

←⌊_⌋ : Equivalence-kind → Backward-kind
←⌊ equivalence  ⌋ = equivalence
←⌊ left-inverse ⌋ = left-inverse
←⌊ surjection   ⌋ = surjection
←⌊ bijection    ⌋ = bijection

------------------------------------------------------------------------
-- Opposites

-- For every kind there is an opposite kind.

_op : Kind → Kind
implication         op = reverse-implication
reverse-implication op = implication
equivalence         op = equivalence
injection           op = reverse-injection
reverse-injection   op = injection
left-inverse        op = surjection
surjection          op = left-inverse
bijection           op = bijection

-- For every morphism there is a corresponding reverse morphism of the
-- opposite kind.

reverse : ∀ {k a b} {A : Set a} {B : Set b} →
          A ∼[ k ] B → B ∼[ k op ] A
reverse {implication}         = id
reverse {reverse-implication} = id
reverse {equivalence}         = Symmetry.sym-⇔
reverse {injection}           = id
reverse {reverse-injection}   = id
reverse {left-inverse}        = ↪⇒↠
reverse {surjection}          = ↠⇒↪
reverse {bijection}           = ↔⇒⤖ ∘ Symmetry.sym-↔ ∘ ⤖⇒↔

------------------------------------------------------------------------
-- For a fixed universe level every kind is a preorder and each
-- symmetric kind is an equivalence

K-refl : ∀ {k ℓ} → Reflexive (Related k {ℓ})
K-refl {implication}         = Identity.id-⟶ _
K-refl {reverse-implication} = Identity.id-⟶ _
K-refl {equivalence}         = Identity.id-⇔ _
K-refl {injection}           = Identity.id-↣ _
K-refl {reverse-injection}   = Identity.id-↣ _
K-refl {left-inverse}        = Identity.id-↪ _
K-refl {surjection}          = Identity.id-↠ _
K-refl {bijection}           = Identity.id-⤖ _

K-reflexive : ∀ {k ℓ} → P._≡_ Relation.Binary.⇒ Related k {ℓ}
K-reflexive P.refl = K-refl

K-trans : ∀ {k ℓ₁ ℓ₂ ℓ₃} → Trans (Related k {ℓ₁} {ℓ₂})
                                 (Related k {ℓ₂} {ℓ₃})
                                 (Related k {ℓ₁} {ℓ₃})
K-trans {implication}         = Composition._∘-⟶_
K-trans {reverse-implication} = flip Composition._∘-⟶_
K-trans {equivalence}         = Composition._∘-⇔_
K-trans {injection}           = Composition._∘-↣_
K-trans {reverse-injection}   = flip Composition._∘-↣_
K-trans {left-inverse}        = Composition._∘-↪_
K-trans {surjection}          = Composition._∘-↠_
K-trans {bijection}           = Composition._∘-⤖_

SK-sym : ∀ {k ℓ₁ ℓ₂} → Sym (Related ⌊ k ⌋ {ℓ₁} {ℓ₂})
                          (Related ⌊ k ⌋ {ℓ₂} {ℓ₁})
SK-sym {equivalence} = reverse
SK-sym {bijection}   = reverse

SK-isEquivalence : ∀ k ℓ → IsEquivalence {ℓ = ℓ} (Related ⌊ k ⌋)
SK-isEquivalence k ℓ = record
  { refl  = K-refl
  ; sym   = SK-sym
  ; trans = K-trans
  }

SK-setoid : Symmetric-kind → (ℓ : Level) → Setoid _ _
SK-setoid k ℓ = record { isEquivalence = SK-isEquivalence k ℓ }

K-isPreorder : ∀ k ℓ → IsPreorder _⤖_ (Related k)
K-isPreorder k ℓ = record
    { isEquivalence = SK-isEquivalence bijection ℓ
    ; reflexive     = ⤖⇒
    ; trans         = K-trans
    }

K-preorder : Kind → (ℓ : Level) → Preorder _ _ _
K-preorder k ℓ = record { isPreorder = K-isPreorder k ℓ }

------------------------------------------------------------------------
-- Equational reasoning

-- Equational reasoning for related things.

module EquationalReasoning where

  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _⤖⟨_⟩_ _↔⟨_⟩_ _↔⟨⟩_ _≡⟨_⟩_

  _∼⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ∼[ k ] Y → Y ∼[ k ] Z → X ∼[ k ] Z
  _ ∼⟨ X↝Y ⟩ Y↝Z = K-trans X↝Y Y↝Z

  -- Isomorphisms and bijections can be combined with any other kind of relatedness.

  _⤖⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ⤖ Y → Y ∼[ k ] Z → X ∼[ k ] Z
  X ⤖⟨ X⤖Y ⟩ Y⇔Z = X ∼⟨ ⤖⇒ X⤖Y ⟩ Y⇔Z

  _↔⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ↔ Y → Y ∼[ k ] Z → X ∼[ k ] Z
  X ↔⟨ X↔Y ⟩ Y⇔Z = X ∼⟨ ⤖⇒ (↔⇒⤖ X↔Y) ⟩ Y⇔Z

  _↔⟨⟩_ : ∀ {k x y} (X : Set x) {Y : Set y} →
          X ∼[ k ] Y → X ∼[ k ] Y
  X ↔⟨⟩ X⇔Y = X⇔Y

  _≡⟨_⟩_ : ∀ {k ℓ z} (X : Set ℓ) {Y : Set ℓ} {Z : Set z} →
           X P.≡ Y → Y ∼[ k ] Z → X ∼[ k ] Z
  X ≡⟨ X≡Y ⟩ Y⇔Z = X ∼⟨ ≡⇒ X≡Y ⟩ Y⇔Z

  _∎ : ∀ {k x} (X : Set x) → X ∼[ k ] X
  X ∎ = K-refl


------------------------------------------------------------------------
-- Every unary relation induces a preorder and, for symmetric kinds,
-- an equivalence. (No claim is made that these relations are unique.)

InducedRelation₁ : Kind → ∀ {a s} {A : Set a} →
                   (A → Set s) → A → A → Set _
InducedRelation₁ k S = λ x y → S x ∼[ k ] S y

InducedPreorder₁ : Kind → ∀ {a s} {A : Set a} →
                   (A → Set s) → Preorder _ _ _
InducedPreorder₁ k S = record
  { _≈_        = P._≡_
  ; _∼_        = InducedRelation₁ k S
  ; isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = reflexive ∘
                      K-reflexive ∘
                      P.cong S
    ; trans         = K-trans
    }
  } where open Preorder (K-preorder _ _)

InducedEquivalence₁ : Symmetric-kind → ∀ {a s} {A : Set a} →
                      (A → Set s) → Setoid _ _
InducedEquivalence₁ k S = record
  { _≈_           = InducedRelation₁ ⌊ k ⌋ S
  ; isEquivalence = record
    { refl  = K-refl
    ; sym   = SK-sym
    ; trans = K-trans
    }
  }

------------------------------------------------------------------------
-- Every binary relation induces a preorder and, for symmetric kinds,
-- an equivalence. (No claim is made that these relations are unique.)

InducedRelation₂ : Kind → ∀ {a b s} {A : Set a} {B : Set b} →
                   (A → B → Set s) → B → B → Set _
InducedRelation₂ k _S_ = λ x y → ∀ {z} → (z S x) ∼[ k ] (z S y)

InducedPreorder₂ : Kind → ∀ {a b s} {A : Set a} {B : Set b} →
                   (A → B → Set s) → Preorder _ _ _
InducedPreorder₂ k _S_ = record
  { _≈_        = P._≡_
  ; _∼_        = InducedRelation₂ k _S_
  ; isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = λ x≡y {z} →
                        reflexive $
                        K-reflexive $
                        P.cong (_S_ z) x≡y

    ; trans         = λ i↝j j↝k → K-trans i↝j j↝k
    }
  } where open Preorder (K-preorder _ _)

InducedEquivalence₂ : Symmetric-kind →
                      ∀ {a b s} {A : Set a} {B : Set b} →
                      (A → B → Set s) → Setoid _ _
InducedEquivalence₂ k _S_ = record
  { _≈_           = InducedRelation₂ ⌊ k ⌋ _S_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ i↝j → sym i↝j
    ; trans = λ i↝j j↝k → trans i↝j j↝k
    }
  } where open Setoid (SK-setoid _ _)
