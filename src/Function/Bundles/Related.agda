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

------------------------------------------------------------------------
-- Relatedness

-- There are several kinds of "relatedness".

-- The idea to include kinds other than equivalence and bijection came
-- from Simon Thompson and Bengt Nordström. /NAD

data Kind : Set where
  implication        : Kind
  reverseImplication : Kind
  equivalence        : Kind
  injection          : Kind
  reverseInjection   : Kind
  leftInverse        : Kind
  surjection         : Kind
  bijection          : Kind

private
  variable
    k : Kind
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

-- Interpretation of the codes above. The code "bijection" is
-- interpreted as Inverse rather than Bijection; the two types are
-- equivalent.

infix 4 _∼[_]_

_∼[_]_ : Set a → Kind → Set b → Set _
A ∼[ implication        ] B = A ⟶ B
A ∼[ reverseImplication ] B = B ⟶ A
A ∼[ equivalence        ] B = A ⇔ B
A ∼[ injection          ] B = A ↣ B
A ∼[ reverseInjection   ] B = B ↣ A
A ∼[ leftInverse        ] B = A ↪ B
A ∼[ surjection         ] B = A ↠ B
A ∼[ bijection          ] B = A ⤖ B

-- A non-infix synonym.

Related : Kind → Set a → Set b → Set _
Related k A B = A ∼[ k ] B

-- The bijective equality implies any kind of relatedness.

⤖⇒ : A ∼[ bijection ] B → A ∼[ k ] B
⤖⇒ {k = implication}        = mk⟶ ∘ Bijection.f
⤖⇒ {k = reverseImplication} = mk⟶ ∘ Inverse.f⁻¹ ∘ ⤖⇒↔
⤖⇒ {k = equivalence}        = ⤖⇒⇔
⤖⇒ {k = injection}          = Bijection.injection
⤖⇒ {k = reverseInjection}   = Bijection.injection ∘ ↔⇒⤖ ∘ Symmetry.inverse ∘ ⤖⇒↔
⤖⇒ {k = leftInverse}        = Inverse.rightInverse ∘ ⤖⇒↔
⤖⇒ {k = surjection}         = Bijection.surjection
⤖⇒ {k = bijection}          = id

-- Actual equality also implies any kind of relatedness.

≡⇒ : A P.≡ B → A ∼[ k ] B
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
  implication : Forward-kind
  equivalence : Forward-kind
  injection   : Forward-kind
  leftInverse : Forward-kind
  surjection  : Forward-kind
  bijection   : Forward-kind

-- Forgetful map.

⌊_⌋→ : Forward-kind → Kind
⌊ implication  ⌋→ = implication
⌊ equivalence  ⌋→ = equivalence
⌊ injection    ⌋→ = injection
⌊ leftInverse  ⌋→ = leftInverse
⌊ surjection   ⌋→ = surjection
⌊ bijection    ⌋→ = bijection

-- The function.

⇒→ : ∀ {k} → A ∼[ ⌊ k ⌋→ ] B → A → B
⇒→ {k = implication} = Func.f
⇒→ {k = equivalence} = Equivalence.f
⇒→ {k = injection}   = Injection.f
⇒→ {k = leftInverse} = RightInverse.f
⇒→ {k = surjection}  = Surjection.f
⇒→ {k = bijection}   = Bijection.f

-- Kinds whose interpretation include a function which "goes backwards".

data Backward-kind : Set where
  reverseImplication : Backward-kind
  equivalence        : Backward-kind
  reverseInjection   : Backward-kind
  leftInverse        : Backward-kind
  surjection         : Backward-kind
  bijection          : Backward-kind

-- Forgetful map.

⌊_⌋← : Backward-kind → Kind
⌊ reverseImplication ⌋← = reverseImplication
⌊ equivalence        ⌋← = equivalence
⌊ reverseInjection   ⌋← = reverseInjection
⌊ leftInverse        ⌋← = leftInverse
⌊ surjection         ⌋← = surjection
⌊ bijection          ⌋← = bijection

-- The function.

⇒← : ∀ {k} → A ∼[ ⌊ k ⌋← ] B → B → A
⇒← {k = reverseImplication} = Func.f
⇒← {k = equivalence}        = Equivalence.g
⇒← {k = reverseInjection}   = Injection.f
⇒← {k = leftInverse}        = RightInverse.g
⇒← {k = surjection}         = RightInverse.f ∘ ↠⇒↪
⇒← {k = bijection}          = Inverse.f⁻¹ ∘ ⤖⇒↔

-- Kinds whose interpretation include functions going in both
-- directions.

data Equivalence-kind : Set where
  equivalence : Equivalence-kind
  leftInverse : Equivalence-kind
  surjection  : Equivalence-kind
  bijection   : Equivalence-kind

-- Forgetful map.

⌊_⌋⇔ : Equivalence-kind → Kind
⌊ equivalence ⌋⇔ = equivalence
⌊ leftInverse ⌋⇔ = leftInverse
⌊ surjection  ⌋⇔ = surjection
⌊ bijection   ⌋⇔ = bijection

-- The functions.

⇒⇔ : ∀ {k} → A ∼[ ⌊ k ⌋⇔ ] B → A ∼[ equivalence ] B
⇒⇔ {k = equivalence} = id
⇒⇔ {k = leftInverse} = RightInverse.equivalence
⇒⇔ {k = surjection}  = ↠⇒⇔
⇒⇔ {k = bijection}   = ⤖⇒⇔

-- Conversions between special kinds.

⇔⌊_⌋ : Symmetric-kind → Equivalence-kind
⇔⌊ equivalence ⌋ = equivalence
⇔⌊ bijection   ⌋ = bijection

→⌊_⌋ : Equivalence-kind → Forward-kind
→⌊ equivalence ⌋ = equivalence
→⌊ leftInverse ⌋ = leftInverse
→⌊ surjection  ⌋ = surjection
→⌊ bijection   ⌋ = bijection

←⌊_⌋ : Equivalence-kind → Backward-kind
←⌊ equivalence ⌋ = equivalence
←⌊ leftInverse ⌋ = leftInverse
←⌊ surjection  ⌋ = surjection
←⌊ bijection   ⌋ = bijection

------------------------------------------------------------------------
-- Opposites

-- For every kind there is an opposite kind.

_op : Kind → Kind
implication        op = reverseImplication
reverseImplication op = implication
equivalence        op = equivalence
injection          op = reverseInjection
reverseInjection   op = injection
leftInverse        op = surjection
surjection         op = leftInverse
bijection          op = bijection

-- For every morphism there is a corresponding reverse morphism of the
-- opposite kind.

reverse : A ∼[ k ] B → B ∼[ k op ] A
reverse {k = implication}        = id
reverse {k = reverseImplication} = id
reverse {k = equivalence}        = Symmetry.sym-⇔
reverse {k = injection}          = id
reverse {k = reverseInjection}   = id
reverse {k = leftInverse}        = ↪⇒↠
reverse {k = surjection}         = ↠⇒↪
reverse {k = bijection}          = ↔⇒⤖ ∘ Symmetry.sym-↔ ∘ ⤖⇒↔

------------------------------------------------------------------------
-- For a fixed universe level every kind is a preorder and each
-- symmetric kind is an equivalence

K-refl : Reflexive (Related {a} k)
K-refl {k = implication}        = Identity.id-⟶ _
K-refl {k = reverseImplication} = Identity.id-⟶ _
K-refl {k = equivalence}        = Identity.id-⇔ _
K-refl {k = injection}          = Identity.id-↣ _
K-refl {k = reverseInjection}   = Identity.id-↣ _
K-refl {k = leftInverse}        = Identity.id-↪ _
K-refl {k = surjection}         = Identity.id-↠ _
K-refl {k = bijection}          = Identity.id-⤖ _

K-reflexive : P._≡_ Relation.Binary.⇒ Related {a} k
K-reflexive P.refl = K-refl

K-trans : Trans (Related {a} {b} k)
                (Related {b} {c} k)
                (Related {a} {c} k)
K-trans {k = implication}        = Composition._∘-⟶_
K-trans {k = reverseImplication} = flip Composition._∘-⟶_
K-trans {k = equivalence}        = Composition._∘-⇔_
K-trans {k = injection}          = Composition._∘-↣_
K-trans {k = reverseInjection}   = flip Composition._∘-↣_
K-trans {k = leftInverse}        = Composition._∘-↪_
K-trans {k = surjection}         = Composition._∘-↠_
K-trans {k = bijection}          = Composition._∘-⤖_

SK-sym : ∀ {k} → Sym (Related {a} {b} ⌊ k ⌋)
                     (Related {b} {a} ⌊ k ⌋)
SK-sym {k = equivalence} = reverse
SK-sym {k = bijection}   = reverse

SK-isEquivalence : ∀ k → IsEquivalence {ℓ = a} (Related ⌊ k ⌋)
SK-isEquivalence k = record
  { refl  = K-refl
  ; sym   = SK-sym
  ; trans = K-trans
  }

SK-setoid : Symmetric-kind → (ℓ : Level) → Setoid _ _
SK-setoid k ℓ = record { isEquivalence = SK-isEquivalence {ℓ} k }

K-isPreorder : ∀ k → IsPreorder {ℓ = a} _⤖_ (Related k)
K-isPreorder k = record
  { isEquivalence = SK-isEquivalence bijection
  ; reflexive     = ⤖⇒
  ; trans         = K-trans
  }

K-preorder : Kind → (ℓ : Level) → Preorder _ ℓ _
K-preorder k ℓ = record { isPreorder = K-isPreorder k }

------------------------------------------------------------------------
-- Equational reasoning

-- Equational reasoning for related things.

module EquationalReasoning where

  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _⤖⟨_⟩_ _↔⟨_⟩_ _↔⟨⟩_ _≡⟨_⟩_

  _∼⟨_⟩_ : (A : Set a) → A ∼[ k ] B → B ∼[ k ] C → A ∼[ k ] C
  _ ∼⟨ A↝B ⟩ B↝C = K-trans A↝B B↝C

  -- Isomorphisms and bijections can be combined with any other kind of relatedness.

  _⤖⟨_⟩_ : (A : Set a) → A ⤖ B → B ∼[ k ] C → A ∼[ k ] C
  A ⤖⟨ A⤖B ⟩ B⇔C = A ∼⟨ ⤖⇒ A⤖B ⟩ B⇔C

  _↔⟨_⟩_ : (A : Set a) → A ↔ B → B ∼[ k ] C → A ∼[ k ] C
  A ↔⟨ A↔B ⟩ B⇔C = A ∼⟨ ⤖⇒ (↔⇒⤖ A↔B) ⟩ B⇔C

  _↔⟨⟩_ : (A : Set a) → A ∼[ k ] B → A ∼[ k ] B
  A ↔⟨⟩ A⇔B = A⇔B

  _≡⟨_⟩_ : (A : Set a) → A P.≡ B → B ∼[ k ] C → A ∼[ k ] C
  A ≡⟨ A≡B ⟩ B⇔C = A ∼⟨ ≡⇒ A≡B ⟩ B⇔C

  _∎ : (A : Set a) → A ∼[ k ] A
  A ∎ = K-refl


------------------------------------------------------------------------
-- Every unary relation induces a preorder and, for symmetric kinds,
-- an equivalence. (No claim is made that these relations are unique.)

InducedRelation₁ : Kind → ∀ {s} → (A → Set s) → A → A → Set _
InducedRelation₁ k S = λ x y → S x ∼[ k ] S y

InducedPreorder₁ : Kind → ∀ {s} → (A → Set s) → Preorder _ _ _
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

InducedEquivalence₁ : Symmetric-kind → ∀ {s} → (A → Set s) → Setoid _ _
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

InducedRelation₂ : Kind → ∀ {s} → (A → B → Set s) → B → B → Set _
InducedRelation₂ k _S_ = λ x y → ∀ {z} → (z S x) ∼[ k ] (z S y)

InducedPreorder₂ : Kind → ∀ {s} → (A → B → Set s) → Preorder _ _ _
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

InducedEquivalence₂ : Symmetric-kind → ∀ {s} → (A → B → Set s) → Setoid _ _
InducedEquivalence₂ k _S_ = record
  { _≈_           = InducedRelation₂ ⌊ k ⌋ _S_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ i↝j → sym i↝j
    ; trans = λ i↝j j↝k → trans i↝j j↝k
    }
  } where open Setoid (SK-setoid _ _)
