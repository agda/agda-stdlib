------------------------------------------------------------------------
-- The Agda standard library
--
-- Relatedness for the function hierarchy
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Related.Propositional where

open import Level
open import Relation.Binary
  using (Sym; Reflexive; Trans; IsEquivalence; Setoid; IsPreorder; Preorder)
open import Function.Bundles
open import Function.Base
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P

open import Function.Properties.Surjection   using (↠⇒↪; ↠⇒⇔)
open import Function.Properties.RightInverse using (↪⇒↠)
open import Function.Properties.Bijection    using (⤖⇒↔; ⤖⇒⇔)
open import Function.Properties.Inverse      using (↔⇒⤖)

import Function.Construct.Symmetry    as Symmetry
import Function.Construct.Identity    as Identity
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
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c
    k : Kind

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
⤖⇒ {k = implication}        = mk⟶ ∘ Bijection.to
⤖⇒ {k = reverseImplication} = mk⟶ ∘ Inverse.from ∘ ⤖⇒↔
⤖⇒ {k = equivalence}        = ⤖⇒⇔
⤖⇒ {k = injection}          = Bijection.injection
⤖⇒ {k = reverseInjection}   = Bijection.injection ∘ ↔⇒⤖ ∘ Symmetry.inverse ∘ ⤖⇒↔
⤖⇒ {k = leftInverse}        = Inverse.rightInverse ∘ ⤖⇒↔
⤖⇒ {k = surjection}         = Bijection.surjection
⤖⇒ {k = bijection}          = id

-- Propositional equality also implies any kind of relatedness.

≡⇒ : A ≡ B → A ∼[ k ] B
≡⇒ P.refl = ⤖⇒ (Identity.⤖-id _)

------------------------------------------------------------------------
-- Special kinds of kinds

-- Kinds whose interpretation is symmetric.

data SymmetricKind : Set where
  equivalence : SymmetricKind
  bijection   : SymmetricKind

-- Forgetful map.

⌊_⌋ : SymmetricKind → Kind
⌊ equivalence ⌋ = equivalence
⌊ bijection   ⌋ = bijection

-- The proof of symmetry can be found below.

-- Kinds whose interpretation include a function which "goes in the
-- forward direction".

data ForwardKind : Set where
  implication : ForwardKind
  equivalence : ForwardKind
  injection   : ForwardKind
  leftInverse : ForwardKind
  surjection  : ForwardKind
  bijection   : ForwardKind

-- Forgetful map.

⌊_⌋→ : ForwardKind → Kind
⌊ implication  ⌋→ = implication
⌊ equivalence  ⌋→ = equivalence
⌊ injection    ⌋→ = injection
⌊ leftInverse  ⌋→ = leftInverse
⌊ surjection   ⌋→ = surjection
⌊ bijection    ⌋→ = bijection

-- The function.

⇒→ : ∀ {k} → A ∼[ ⌊ k ⌋→ ] B → A → B
⇒→ {k = implication} = Func.to
⇒→ {k = equivalence} = Equivalence.to
⇒→ {k = injection}   = Injection.to
⇒→ {k = leftInverse} = RightInverse.to
⇒→ {k = surjection}  = Surjection.to
⇒→ {k = bijection}   = Bijection.to

-- Kinds whose interpretation include a function which "goes backwards".

data BackwardKind : Set where
  reverseImplication : BackwardKind
  equivalence        : BackwardKind
  reverseInjection   : BackwardKind
  leftInverse        : BackwardKind
  surjection         : BackwardKind
  bijection          : BackwardKind

-- Forgetful map.

⌊_⌋← : BackwardKind → Kind
⌊ reverseImplication ⌋← = reverseImplication
⌊ equivalence        ⌋← = equivalence
⌊ reverseInjection   ⌋← = reverseInjection
⌊ leftInverse        ⌋← = leftInverse
⌊ surjection         ⌋← = surjection
⌊ bijection          ⌋← = bijection

-- The function.

⇒← : ∀ {k} → A ∼[ ⌊ k ⌋← ] B → B → A
⇒← {k = reverseImplication} = Func.to
⇒← {k = equivalence}        = Equivalence.from
⇒← {k = reverseInjection}   = Injection.to
⇒← {k = leftInverse}        = RightInverse.from
⇒← {k = surjection}         = RightInverse.to ∘ ↠⇒↪
⇒← {k = bijection}          = Inverse.from ∘ ⤖⇒↔

-- Kinds whose interpretation include functions going in both
-- directions.

data EquivalenceKind : Set where
  equivalence : EquivalenceKind
  leftInverse : EquivalenceKind
  surjection  : EquivalenceKind
  bijection   : EquivalenceKind

-- Forgetful map.

⌊_⌋⇔ : EquivalenceKind → Kind
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

⇔⌊_⌋ : SymmetricKind → EquivalenceKind
⇔⌊ equivalence ⌋ = equivalence
⇔⌊ bijection   ⌋ = bijection

→⌊_⌋ : EquivalenceKind → ForwardKind
→⌊ equivalence ⌋ = equivalence
→⌊ leftInverse ⌋ = leftInverse
→⌊ surjection  ⌋ = surjection
→⌊ bijection   ⌋ = bijection

←⌊_⌋ : EquivalenceKind → BackwardKind
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
reverse {k = equivalence}        = Symmetry.⇔-sym
reverse {k = injection}          = id
reverse {k = reverseInjection}   = id
reverse {k = leftInverse}        = ↪⇒↠
reverse {k = surjection}         = ↠⇒↪
reverse {k = bijection}          = ↔⇒⤖ ∘ Symmetry.↔-sym ∘ ⤖⇒↔

------------------------------------------------------------------------
-- For a fixed universe level every kind is a preorder and each
-- symmetric kind is an equivalence

K-refl : Reflexive (Related {a} k)
K-refl {k = implication}        = Identity.⟶-id _
K-refl {k = reverseImplication} = Identity.⟶-id _
K-refl {k = equivalence}        = Identity.⇔-id _
K-refl {k = injection}          = Identity.↣-id _
K-refl {k = reverseInjection}   = Identity.↣-id _
K-refl {k = leftInverse}        = Identity.↪-id _
K-refl {k = surjection}         = Identity.↠-id _
K-refl {k = bijection}          = Identity.⤖-id _

K-reflexive : _≡_ Relation.Binary.⇒ Related {a} k
K-reflexive P.refl = K-refl

K-trans : Trans (Related {a} {b} k)
                (Related {b} {c} k)
                (Related {a} {c} k)
K-trans {k = implication}        = Composition._⟶-∘_
K-trans {k = reverseImplication} = flip Composition._⟶-∘_
K-trans {k = equivalence}        = Composition._⇔-∘_
K-trans {k = injection}          = Composition._↣-∘_
K-trans {k = reverseInjection}   = flip Composition._↣-∘_
K-trans {k = leftInverse}        = Composition._↪-∘_
K-trans {k = surjection}         = Composition._↠-∘_
K-trans {k = bijection}          = Composition._⤖-∘_

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

SK-setoid : SymmetricKind → (ℓ : Level) → Setoid _ _
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

  _≡⟨_⟩_ : (A : Set a) → A ≡ B → B ∼[ k ] C → A ∼[ k ] C
  A ≡⟨ A≡B ⟩ B⇔C = A ∼⟨ ≡⇒ A≡B ⟩ B⇔C

  _∎ : (A : Set a) → A ∼[ k ] A
  A ∎ = K-refl


------------------------------------------------------------------------
-- Every unary relation induces a preorder and, for symmetric kinds,
-- an equivalence. (No claim is made that these relations are unique.)

InducedRelation₁ : Kind → (P : A → Set p) → A → A → Set _
InducedRelation₁ k P = λ x y → P x ∼[ k ] P y

InducedPreorder₁ : Kind → (P : A → Set p) → Preorder _ _ _
InducedPreorder₁ k P = record
  { _≈_        = _≡_
  ; _∼_        = InducedRelation₁ k P
  ; isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = reflexive ∘
                      K-reflexive ∘
                      P.cong P
    ; trans         = K-trans
    }
  } where open Preorder (K-preorder _ _)

InducedEquivalence₁ : SymmetricKind → (P : A → Set p) → Setoid _ _
InducedEquivalence₁ k P = record
  { _≈_           = InducedRelation₁ ⌊ k ⌋ P
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
  { _≈_        = _≡_
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

InducedEquivalence₂ : SymmetricKind → ∀ {s} → (A → B → Set s) → Setoid _ _
InducedEquivalence₂ k _S_ = record
  { _≈_           = InducedRelation₂ ⌊ k ⌋ _S_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ i↝j → sym i↝j
    ; trans = λ i↝j j↝k → trans i↝j j↝k
    }
  } where open Setoid (SK-setoid _ _)
