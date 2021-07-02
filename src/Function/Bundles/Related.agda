------------------------------------------------------------------------

-- The Agda standard library
--
-- Relatedness for the function hierarchy
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Bundles.Related where

open import Level
open import Relation.Binary using (Sym; Reflexive; Trans; IsEquivalence; Setoid; IsPreorder; Preorder)
import Function.Related as R
open import Function.Bundles
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as Eq
import Function.Injection   as Inj
import Function.Inverse     as Inv
import Function.LeftInverse as LeftInv
import Function.Surjection  as Surj
import Relation.Binary.PropositionalEquality as P

open import Function.Properties.Inverse
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Identity as Identity
import Function.Construct.Composition as Composition

open import Data.Product

infix 4 _∼[_]_

_∼[_]_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → R.Kind → Set ℓ₂ → Set _
A ∼[ R.implication         ] B = A ⟶ B
A ∼[ R.reverse-implication ] B = B ⟶ A
A ∼[ R.equivalence         ] B = A ⇔ B
A ∼[ R.injection           ] B = A ↣ B
A ∼[ R.reverse-injection   ] B = B ↣ A
A ∼[ R.left-inverse        ] B = A ↪ B
A ∼[ R.surjection          ] B = A ↠ B
A ∼[ R.bijection           ] B = A ⤖ B

-- A non-infix synonym.

Related : R.Kind → ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
Related k A B = A ∼[ k ] B

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} where

  toRelated : {K : R.Kind} → A ∼[ K ] B → A R.∼[ K ] B
  toRelated {R.implication} rel = Func.f rel
  toRelated {R.reverse-implication} rel = R.lam (Func.f rel)
  toRelated {R.equivalence} rel = Eq.equivalence (Equivalence.f rel) (Equivalence.g rel)
  toRelated {R.injection} rel = Inj.injection (Injection.f rel) (Injection.injective rel)
  toRelated {R.reverse-injection} rel = R.lam (Inj.injection (Injection.f rel) (Injection.injective rel))
  toRelated {R.left-inverse} rel =
    LeftInv.leftInverse (RightInverse.f rel) (RightInverse.g rel) (RightInverse.inverseʳ rel)
  toRelated {R.surjection} rel with Surjection.surjective rel
  ... | surj = Surj.surjection (Surjection.f rel) (proj₁ ∘ surj) (proj₂ ∘ surj)
  toRelated {R.bijection} rel with Bijection.bijective rel
  ... | (inj , surj) = Inv.inverse (Bijection.f rel) (proj₁ ∘ surj) (inj ∘ proj₂ ∘ surj ∘ (Bijection.f rel)) (proj₂ ∘ surj)

  fromRelated : {K : R.Kind} → A R.∼[ K ] B → A ∼[ K ] B
  fromRelated {R.implication} rel = mk⟶ rel
  fromRelated {R.reverse-implication} rel = mk⟶ (R.app-← rel)
  fromRelated {R.equivalence} record { to = to ; from = from } = mk⇔ (to ⟨$⟩_) (from ⟨$⟩_)
  fromRelated {R.injection} rel = mk↣ (Inj.Injection.injective rel)
  fromRelated {R.reverse-injection} (R.lam app-↢) = mk↣ (Inj.Injection.injective app-↢)
  fromRelated {R.left-inverse} record { to = to ; from = from ; left-inverse-of = left-inverse-of } =
    mk↪ {f = to ⟨$⟩_} {g = from ⟨$⟩_} left-inverse-of
  fromRelated {R.surjection} record { to = to ; surjective = surjective } with surjective
  ... | record { from = from ; right-inverse-of = right-inverse-of } = mk↠ {f = to ⟨$⟩_} < from ⟨$⟩_ , right-inverse-of >
  fromRelated {R.bijection} record { to = to ; from = from ; inverse-of = inverse-of } with inverse-of
  ... | record { left-inverse-of = left-inverse-of ; right-inverse-of = right-inverse-of } = mk⤖
    ((λ {x y} h → P.subst₂ P._≡_ (left-inverse-of x) (left-inverse-of y) (P.cong (from ⟨$⟩_) h)) ,
    < from ⟨$⟩_ , right-inverse-of >)

-- The bijective equality implies any kind of relatedness.

⤖⇒ : ∀ {k x y} {X : Set x} {Y : Set y} →
     X ∼[ R.bijection ] Y → X ∼[ k ] Y
⤖⇒ h = fromRelated (R.↔⇒ (toRelated h))

-- Actual equality also implies any kind of relatedness.

≡⇒ : ∀ {k ℓ} {X Y : Set ℓ} → X P.≡ Y → X ∼[ k ] Y
≡⇒ h = fromRelated (R.≡⇒ h)

-- The forwards function.

⇒→ : ∀ {k x y} {X : Set x} {Y : Set y} → X ∼[ R.⌊ k ⌋→ ] Y → X → Y
⇒→ {R.implication}  = Func.f
⇒→ {R.equivalence}  = Equivalence.f
⇒→ {R.injection}    = Injection.f
⇒→ {R.left-inverse} = RightInverse.f
⇒→ {R.surjection}   = Surjection.f
⇒→ {R.bijection}    = Bijection.f

-- The backwards function

⇒← : ∀ {k x y} {X : Set x} {Y : Set y} → X ∼[ R.⌊ k ⌋← ] Y → Y → X
⇒← {R.reverse-implication} = Func.f
⇒← {R.equivalence}         = Equivalence.g
⇒← {R.reverse-injection}   = Injection.f
⇒← {R.left-inverse}        = RightInverse.g
⇒← {R.surjection}          = _⟨$⟩_ ∘ Surj.Surjection.from ∘ toRelated
⇒← {R.bijection}           = _⟨$⟩_ ∘ Inv.Inverse.from ∘ toRelated

-- The equivalence

⇒⇔ : ∀ {k x y} {X : Set x} {Y : Set y} →
     X ∼[ R.⌊ k ⌋⇔ ] Y → X ∼[ R.equivalence ] Y
⇒⇔ {R.equivalence}  = id
⇒⇔ {R.left-inverse} = fromRelated ∘ R.⇒⇔ ∘ toRelated
⇒⇔ {R.surjection}   = fromRelated ∘ R.⇒⇔ ∘ toRelated
⇒⇔ {R.bijection}    = ⤖⇒⇔

-- For every morphism there is a corresponding reverse morphism of the
-- opposite kind.

reverse : ∀ {k a b} {A : Set a} {B : Set b} →
          A ∼[ k ] B → B ∼[ k R.op ] A
reverse {R.implication}         = id
reverse {R.reverse-implication} = id
reverse {R.equivalence}         = Symmetry.sym-⇔
reverse {R.injection}           = id
reverse {R.reverse-injection}   = id
reverse {R.left-inverse}        = fromRelated ∘ R.reverse ∘ toRelated
reverse {R.surjection}          = fromRelated ∘ R.reverse ∘ toRelated
reverse {R.bijection}           = ↔⇒⤖ ∘ Symmetry.sym-↔ ∘ ⤖⇒↔

------------------------------------------------------------------------
-- For a fixed universe level every kind is a preorder and each
-- symmetric kind is an equivalence

K-refl : ∀ {k ℓ} → Reflexive (Related k {ℓ})
K-refl {R.implication}         = Identity.id-⟶ _
K-refl {R.reverse-implication} = Identity.id-⟶ _
K-refl {R.equivalence}         = Identity.id-⇔ _
K-refl {R.injection}           = Identity.id-↣ _
K-refl {R.reverse-injection}   = Identity.id-↣ _
K-refl {R.left-inverse}        = Identity.id-↪ _
K-refl {R.surjection}          = Identity.id-↠ _
K-refl {R.bijection}           = Identity.id-⤖ _

K-reflexive : ∀ {k ℓ} → P._≡_ Relation.Binary.⇒ Related k {ℓ}
K-reflexive P.refl = K-refl

K-trans : ∀ {k ℓ₁ ℓ₂ ℓ₃} → Trans (Related k {ℓ₁} {ℓ₂})
                                (Related k {ℓ₂} {ℓ₃})
                                (Related k {ℓ₁} {ℓ₃})
K-trans {R.implication}         = Composition._∘-⟶_
K-trans {R.reverse-implication} = flip Composition._∘-⟶_
K-trans {R.equivalence}         = Composition._∘-⇔_
K-trans {R.injection}           = Composition._∘-↣_
K-trans {R.reverse-injection}   = flip Composition._∘-↣_
K-trans {R.left-inverse}        = Composition._∘-↪_
K-trans {R.surjection}          = Composition._∘-↠_
K-trans {R.bijection}           = Composition._∘-⤖_

SK-sym : ∀ {k ℓ₁ ℓ₂} → Sym (Related R.⌊ k ⌋ {ℓ₁} {ℓ₂})
                          (Related R.⌊ k ⌋ {ℓ₂} {ℓ₁})
SK-sym {R.equivalence} = reverse
SK-sym {R.bijection}   = reverse

SK-isEquivalence : ∀ k ℓ → IsEquivalence {ℓ = ℓ} (Related R.⌊ k ⌋)
SK-isEquivalence k ℓ = record
  { refl  = K-refl
  ; sym   = SK-sym
  ; trans = K-trans
  }

SK-setoid : R.Symmetric-kind → (ℓ : Level) → Setoid _ _
SK-setoid k ℓ = record { isEquivalence = SK-isEquivalence k ℓ }

K-isPreorder : ∀ k ℓ → IsPreorder _⤖_ (Related k)
K-isPreorder k ℓ = record
    { isEquivalence = SK-isEquivalence R.bijection ℓ
    ; reflexive     = ⤖⇒
    ; trans         = K-trans
    }

K-preorder : R.Kind → (ℓ : Level) → Preorder _ _ _
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

InducedRelation₁ : R.Kind → ∀ {a s} {A : Set a} →
                   (A → Set s) → A → A → Set _
InducedRelation₁ k S = λ x y → S x ∼[ k ] S y

InducedPreorder₁ : R.Kind → ∀ {a s} {A : Set a} →
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

InducedEquivalence₁ : R.Symmetric-kind → ∀ {a s} {A : Set a} →
                      (A → Set s) → Setoid _ _
InducedEquivalence₁ k S = record
  { _≈_           = InducedRelation₁ R.⌊ k ⌋ S
  ; isEquivalence = record
    { refl  = K-refl
    ; sym   = SK-sym
    ; trans = K-trans
    }
  }

------------------------------------------------------------------------
-- Every binary relation induces a preorder and, for symmetric kinds,
-- an equivalence. (No claim is made that these relations are unique.)

InducedRelation₂ : R.Kind → ∀ {a b s} {A : Set a} {B : Set b} →
                   (A → B → Set s) → B → B → Set _
InducedRelation₂ k _S_ = λ x y → ∀ {z} → (z S x) ∼[ k ] (z S y)

InducedPreorder₂ : R.Kind → ∀ {a b s} {A : Set a} {B : Set b} →
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

InducedEquivalence₂ : R.Symmetric-kind →
                      ∀ {a b s} {A : Set a} {B : Set b} →
                      (A → B → Set s) → Setoid _ _
InducedEquivalence₂ k _S_ = record
  { _≈_           = InducedRelation₂ R.⌊ k ⌋ _S_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ i↝j → sym i↝j
    ; trans = λ i↝j j↝k → trans i↝j j↝k
    }
  } where open Setoid (SK-setoid _ _)
