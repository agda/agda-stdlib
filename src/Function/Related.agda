------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe which includes several kinds of "relatedness" for sets,
-- such as equivalences, surjections and bijections
------------------------------------------------------------------------

module Function.Related where

open import Level
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq      using (Equivalence)
open import Function.Injection   as Inj     using (Injection; _↣_)
open import Function.Inverse     as Inv     using (Inverse; _↔_)
open import Function.LeftInverse as LeftInv using (LeftInverse)
open import Function.Surjection  as Surj    using (Surjection)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Wrapper types

-- Synonyms which are used to make _∼[_]_ below "constructor-headed"
-- (which implies that Agda can deduce the universe code from an
-- expression matching any of the right-hand sides).

record _←_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor lam
  field app-← : B → A

open _←_ public

record _↢_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor lam
  field app-↢ : B ↣ A

open _↢_ public

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
A ∼[ implication         ] B = A → B
A ∼[ reverse-implication ] B = A ← B
A ∼[ equivalence         ] B = Equivalence (P.setoid A) (P.setoid B)
A ∼[ injection           ] B = Injection   (P.setoid A) (P.setoid B)
A ∼[ reverse-injection   ] B = A ↢ B
A ∼[ left-inverse        ] B = LeftInverse (P.setoid A) (P.setoid B)
A ∼[ surjection          ] B = Surjection  (P.setoid A) (P.setoid B)
A ∼[ bijection           ] B = Inverse     (P.setoid A) (P.setoid B)

-- A non-infix synonym.

Related : Kind → ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
Related k A B = A ∼[ k ] B

-- The bijective equality implies any kind of relatedness.

↔⇒ : ∀ {k x y} {X : Set x} {Y : Set y} →
     X ∼[ bijection ] Y → X ∼[ k ] Y
↔⇒ {implication}         = _⟨$⟩_ ∘ Inverse.to
↔⇒ {reverse-implication} = lam ∘′ _⟨$⟩_ ∘ Inverse.from
↔⇒ {equivalence}         = Inverse.equivalence
↔⇒ {injection}           = Inverse.injection
↔⇒ {reverse-injection}   = lam ∘′ Inverse.injection ∘ Inv.sym
↔⇒ {left-inverse}        = Inverse.left-inverse
↔⇒ {surjection}          = Inverse.surjection
↔⇒ {bijection}           = id

-- Actual equality also implies any kind of relatedness.

≡⇒ : ∀ {k ℓ} {X Y : Set ℓ} → X ≡ Y → X ∼[ k ] Y
≡⇒ P.refl = ↔⇒ Inv.id

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
⇒→ {implication}  = id
⇒→ {equivalence}  = _⟨$⟩_ ∘ Equivalence.to
⇒→ {injection}    = _⟨$⟩_ ∘ Injection.to
⇒→ {left-inverse} = _⟨$⟩_ ∘ LeftInverse.to
⇒→ {surjection}   = _⟨$⟩_ ∘ Surjection.to
⇒→ {bijection}    = _⟨$⟩_ ∘ Inverse.to

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
⇒← {reverse-implication} = app-←
⇒← {equivalence}         = _⟨$⟩_ ∘ Equivalence.from
⇒← {reverse-injection}   = _⟨$⟩_ ∘ Injection.to ∘ app-↢
⇒← {left-inverse}        = _⟨$⟩_ ∘ LeftInverse.from
⇒← {surjection}          = _⟨$⟩_ ∘ Surjection.from
⇒← {bijection}           = _⟨$⟩_ ∘ Inverse.from

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
⇒⇔ {left-inverse} = LeftInverse.equivalence
⇒⇔ {surjection}   = Surjection.equivalence
⇒⇔ {bijection}    = Inverse.equivalence

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
reverse {implication}         = lam
reverse {reverse-implication} = app-←
reverse {equivalence}         = Eq.sym
reverse {injection}           = lam
reverse {reverse-injection}   = app-↢
reverse {left-inverse}        = Surj.fromRightInverse
reverse {surjection}          = Surjection.right-inverse
reverse {bijection}           = Inv.sym

------------------------------------------------------------------------
-- For a fixed universe level every kind is a preorder and each
-- symmetric kind is an equivalence

K-refl : ∀ {k ℓ} → Reflexive (Related k {ℓ})
K-refl {implication}         = id
K-refl {reverse-implication} = lam id
K-refl {equivalence}         = Eq.id
K-refl {injection}           = Inj.id
K-refl {reverse-injection}   = lam Inj.id
K-refl {left-inverse}        = LeftInv.id
K-refl {surjection}          = Surj.id
K-refl {bijection}           = Inv.id

K-reflexive : ∀ {k ℓ} → _≡_ ⇒ Related k {ℓ}
K-reflexive P.refl = K-refl

K-trans : ∀ {k ℓ₁ ℓ₂ ℓ₃} → Trans (Related k {ℓ₁} {ℓ₂})
                                (Related k {ℓ₂} {ℓ₃})
                                (Related k {ℓ₁} {ℓ₃})
K-trans {implication}         = flip _∘′_
K-trans {reverse-implication} = λ f g → lam (app-← f ∘ app-← g)
K-trans {equivalence}         = flip Eq._∘_
K-trans {injection}           = flip Inj._∘_
K-trans {reverse-injection}   = λ f g → lam (Inj._∘_ (app-↢ f) (app-↢ g))
K-trans {left-inverse}        = flip LeftInv._∘_
K-trans {surjection}          = flip Surj._∘_
K-trans {bijection}           = flip Inv._∘_

SK-sym : ∀ {k ℓ₁ ℓ₂} → Sym (Related ⌊ k ⌋ {ℓ₁} {ℓ₂})
                          (Related ⌊ k ⌋ {ℓ₂} {ℓ₁})
SK-sym {equivalence} = Eq.sym
SK-sym {bijection}   = Inv.sym

SK-isEquivalence : ∀ k ℓ → IsEquivalence {ℓ = ℓ} (Related ⌊ k ⌋)
SK-isEquivalence k ℓ = record
  { refl  = K-refl
  ; sym   = SK-sym
  ; trans = K-trans
  }

SK-setoid : Symmetric-kind → (ℓ : Level) → Setoid _ _
SK-setoid k ℓ = record { isEquivalence = SK-isEquivalence k ℓ }

K-isPreorder : ∀ k ℓ → IsPreorder _↔_ (Related k)
K-isPreorder k ℓ = record
    { isEquivalence = SK-isEquivalence bijection ℓ
    ; reflexive     = ↔⇒
    ; trans         = K-trans
    }

K-preorder : Kind → (ℓ : Level) → Preorder _ _ _
K-preorder k ℓ = record { isPreorder = K-isPreorder k ℓ }

------------------------------------------------------------------------
-- Equational reasoning

-- Equational reasoning for related things.

module EquationalReasoning where

  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _↔⟨_⟩_ _↔⟨⟩_ _≡⟨_⟩_

  _∼⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ∼[ k ] Y → Y ∼[ k ] Z → X ∼[ k ] Z
  _ ∼⟨ X↝Y ⟩ Y↝Z = K-trans X↝Y Y↝Z

  -- Isomorphisms can be combined with any other kind of relatedness.

  _↔⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ↔ Y → Y ∼[ k ] Z → X ∼[ k ] Z
  X ↔⟨ X↔Y ⟩ Y⇔Z = X ∼⟨ ↔⇒ X↔Y ⟩ Y⇔Z

  _↔⟨⟩_ : ∀ {k x y} (X : Set x) {Y : Set y} →
          X ∼[ k ] Y → X ∼[ k ] Y
  X ↔⟨⟩ X⇔Y = X⇔Y

  _≡⟨_⟩_ : ∀ {k ℓ z} (X : Set ℓ) {Y : Set ℓ} {Z : Set z} →
           X ≡ Y → Y ∼[ k ] Z → X ∼[ k ] Z
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
  { _≈_        = _≡_
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

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.17

preorder = K-preorder
{-# WARNING_ON_USAGE preorder
"Warning: preorder was deprecated in v0.17.
Please use K-preorder instead."
#-}
setoid = SK-setoid
{-# WARNING_ON_USAGE setoid
"Warning: setoid was deprecated in v0.17.
Please use SK-setoid instead."
#-}
