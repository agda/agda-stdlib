------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe which includes several kinds of "relatedness" for sets,
-- such as equivalences, surjections and bijections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Related where

open import Level
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq      using (Equivalence)
open import Function.Injection   as Inj     using (Injection; _↣_)
open import Function.Inverse     as Inv     using (Inverse; _↔_)
open import Function.LeftInverse as LeftInv using (LeftInverse)
open import Function.Surjection  as Surj    using (Surjection)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P
open import Data.Product using (_,_; proj₁; proj₂; <_,_>)

import Function.Related.Propositional as R
import Function.Bundles as B

private
  variable
    ℓ₁ ℓ₂ : Level
    A : Set ℓ₁
    B : Set ℓ₂

------------------------------------------------------------------------
-- Re-export core concepts from non-deprecated Related code

open R public using
  ( Kind
  ; implication
  ; equivalence
  ; injection
  ; surjection
  ; bijection
  ) renaming
  ( reverseImplication to reverse-implication
  ; reverseInjection   to reverse-injection
  ; leftInverse        to left-inverse
  )

------------------------------------------------------------------------
-- Wrapper types

-- Synonyms which are used to make _∼[_]_ below "constructor-headed"
-- (which implies that Agda can deduce the universe code from an
-- expression matching any of the right-hand sides).

infix 3 _←_ _↢_

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

toRelated : {K : Kind} → A R.∼[ K ] B → A ∼[ K ] B
toRelated {K = implication}         rel = B.Func.to rel
toRelated {K = reverse-implication} rel = lam (B.Func.to rel)
toRelated {K = equivalence}         rel = Eq.equivalence (B.Equivalence.to rel) (B.Equivalence.from rel)
toRelated {K = injection}           rel = Inj.injection (B.Injection.to rel) (B.Injection.injective rel)
toRelated {K = reverse-injection}   rel = lam (Inj.injection (B.Injection.to rel) (B.Injection.injective rel))
toRelated {K = left-inverse}        rel =
  LeftInv.leftInverse (B.RightInverse.to rel) (B.RightInverse.from rel) (B.RightInverse.inverseʳ rel)
toRelated {K = surjection}          rel with B.Surjection.surjective rel
... | surj = Surj.surjection (B.Surjection.to rel) (proj₁ ∘ surj) (proj₂ ∘ surj)
toRelated {K = bijection}           rel with B.Bijection.bijective rel
... | (inj , surj) = Inv.inverse (B.Bijection.to rel) (proj₁ ∘ surj) (inj ∘ proj₂ ∘ surj ∘ (B.Bijection.to rel)) (proj₂ ∘ surj)

fromRelated : {K : Kind} → A ∼[ K ] B → A R.∼[ K ] B
fromRelated {K = implication}         rel = B.mk⟶ rel
fromRelated {K = reverse-implication} rel = B.mk⟶ (app-← rel)
fromRelated {K = equivalence}         record { to = to ; from = from } = B.mk⇔ (to ⟨$⟩_) (from ⟨$⟩_)
fromRelated {K = injection}           rel = B.mk↣ (Inj.Injection.injective rel)
fromRelated {K = reverse-injection}   (lam app-↢) = B.mk↣ (Inj.Injection.injective app-↢)
fromRelated {K = left-inverse}        record { to = to ; from = from ; left-inverse-of = left-inverse-of } =
  B.mk↪ {to = to ⟨$⟩_} {from = from ⟨$⟩_} left-inverse-of
fromRelated {K = surjection}          record { to = to ; surjective = surjective } with surjective
... | record { from = from ; right-inverse-of = right-inverse-of } = B.mk↠ {to = to ⟨$⟩_} < from ⟨$⟩_ , right-inverse-of >
fromRelated {K = bijection}           record { to = to ; from = from ; inverse-of = inverse-of } with inverse-of
... | record { left-inverse-of = left-inverse-of ; right-inverse-of = right-inverse-of } = B.mk⤖
  ((λ {x y} h → P.subst₂ P._≡_ (left-inverse-of x) (left-inverse-of y) (P.cong (from ⟨$⟩_) h)) ,
  < from ⟨$⟩_ , right-inverse-of >)

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
  infixr 2 _∼⟨_⟩_ _↔⟨_⟩_ _↔⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  1 begin_

  begin_ : ∀ {k x y} {X : Set x} {Y : Set y} →
           X ∼[ k ] Y → X ∼[ k ] Y
  begin_ x∼y = x∼y

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

  _≡˘⟨_⟩_ : ∀ {k ℓ z} (X : Set ℓ) {Y : Set ℓ} {Z : Set z} →
            Y ≡ X → Y ∼[ k ] Z → X ∼[ k ] Z
  X ≡˘⟨ Y≡X ⟩ Y⇔Z = X ∼⟨ ≡⇒ (P.sym Y≡X) ⟩ Y⇔Z

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
