------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting binary relations to the second parts of sigma types, while
-- requiring the first parts to be propositionally equal. This is
-- a special case of 'Data.Product.Relation.SigmaPointwise', which is
-- easier to use when it applies.
------------------------------------------------------------------------

module Data.Product.Relation.SigmaPropositional where

open import Level using (Level; _⊔_)

open import Relation.Binary as B using (REL; Rel)
import Relation.Binary.Indexed as I
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Data.Product.Relation.SigmaPointwise as PW

open import Data.Product using (Σ; ∃; _,_)

module HomogenouslyIndexed where

  -- Heterogenous, homogenously-indexed relations

  IREL : ∀ {i a₁ a₂} {I : Set i} → (I → Set a₁) → (I → Set a₂) → (ℓ : Level) → Set _
  IREL A₁ A₂ ℓ = ∀ {i} → A₁ i → A₂ i → Set ℓ

  -- Homogeneous, homogenously-indexed relations

  IRel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
  IRel A = IREL A A


  module _ {i a₁ a₂} {I : Set i} {A₁ : I → Set a₁} {A₂ : I → Set a₂} where

    OverPath
      : ∀ {ℓ} → IREL A₁ A₂ ℓ
      → {i j : I} → i ≡ j → REL (A₁ i) (A₂ j) ℓ
    OverPath ∼ P.refl = ∼

    OverΣ
      : ∀ {ℓ} → IREL A₁ A₂ ℓ
      → REL (Σ I A₁) (Σ I A₂) (i ⊔ ℓ)
    OverΣ ∼ (i , x) (j , y) = Σ (i ≡ j) (λ p → OverPath ∼ p x y)

    IRel-hetRel : ∀ {ℓ} → IREL A₁ A₂ ℓ → I.REL A₁ A₂ (i ⊔ ℓ)
    IRel-hetRel _∼_ {i} {j} x y = (p : i ≡ j) → OverPath _∼_ p x y

    hetRel-IRel : ∀ {ℓ} → I.REL A₁ A₂ ℓ → IREL A₁ A₂ ℓ
    hetRel-IRel _∼_ {i} = _∼_ {i} {i}


  module _ {i a} {I : Set i} (A : I → Set a) {ℓ} (_∼_ : IRel A ℓ) where
    Reflexive : Set _
    Reflexive = ∀ {i} → B.Reflexive (_∼_ {i})

    Symmetric : Set _
    Symmetric = ∀ {i} → B.Symmetric (_∼_ {i})

    Transitive : Set _
    Transitive = ∀ {i} → B.Transitive (_∼_ {i})

    IsEquivalence : Set _
    IsEquivalence = ∀ {i} → B.IsEquivalence (_∼_ {i})

open HomogenouslyIndexed using (OverPath; OverΣ) public
open HomogenouslyIndexed


module _ {i a} {I : Set i} {A : I → Set a} {ℓ} {_∼_ : IRel A ℓ} where
  refl : Reflexive A _∼_ → B.Reflexive (OverΣ {A₁ = A} _∼_)
  refl refl′ = P.refl , refl′

  symmetric : Symmetric A _∼_ → B.Symmetric (OverΣ {A₁ = A} _∼_)
  symmetric sym (P.refl , p) = P.refl , sym p

  transitive : Transitive A _∼_ → B.Transitive (OverΣ {A₁ = A} _∼_)
  transitive trans (P.refl , p) (P.refl , q) = P.refl , trans p q

  isEquivalence : IsEquivalence A _∼_ → B.IsEquivalence (OverΣ _∼_)
  isEquivalence isEquivalence′ = record
    { refl = refl (B.IsEquivalence.refl isEquivalence′)
    ; sym = symmetric (B.IsEquivalence.sym isEquivalence′)
    ; trans = transitive (B.IsEquivalence.trans isEquivalence′)
    }

setoid : ∀ {a b p} {A : Set a} → (A → B.Setoid b p) → B.Setoid (a ⊔ b) (a ⊔ p)
setoid S = record
  { isEquivalence = isEquivalence λ {x} → B.Setoid.isEquivalence (S x)
  }

module _ {a b} {A : Set a} {B : A → Set b} where
  module _ {p} {_∼_ : IRel B p} where
    hom
      : ∀ {c q} {C : A → Set c} {_∼′_ : IRel C q}
        {h : ∀ {x} → B x → C x}
      → (∀ {x} {y z : B x} → y ∼ z → h y ∼′ h z)
      → ∀ {x y} {s : B x} {t : B y}
      → OverΣ _∼_ (x , s) (y , t)
      → OverΣ _∼′_ (x , h s) (y , h t)
    hom h-hom (P.refl , p) = P.refl , h-hom p

    subst
      : {x y : A} (p : x ≡ y) {s t : B x}
      → s ∼ t → OverΣ _∼_ (x , s) (y , P.subst B p t)
    subst P.refl p = (P.refl , p)

module _ {a b} {A : Set a} {B : A → Set b} where
  module _ {p} {_∼_ : IRel B p} where
    ≡-cong :
      ∀ {c} {C : A → Set c}
      → Reflexive B _∼_
      → (h : ∀ {x} → C x → B x)
      → ∀ {x y}
      → {s : C x} {t : C y}
      → OverΣ _≡_ (x , s) (y , t)
      → OverΣ _∼_ (x , h s) (y , h t)
    ≡-cong refl h p = hom (λ {P.refl → refl}) p


-- OverΣ can be used to decompose _≡_

to-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : ∃ B} → OverΣ _≡_ x y → x ≡ y
to-≡ (P.refl , P.refl) = P.refl

from-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : ∃ B} → x ≡ y → OverΣ _≡_ x y
from-≡ P.refl = P.refl , P.refl


-- OverΣ is a special case of REL from SigmaPointwise

module _ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} where
  to-PW : ∀ {p} {_∼_ : IREL B₁ B₂ p} {x : ∃ B₁} {y : ∃ B₂} → OverΣ _∼_ x y → PW.REL B₁ B₂ _≡_ (IRel-hetRel {A₁ = B₁} _∼_) x y
  to-PW {x = i , s} {.i , t} (P.refl , q) = P.refl PW., λ {P.refl → q}

  from-PW : ∀ {p} {_∼_ : I.REL B₁ B₂ p} {x : ∃ B₁} {y : ∃ B₂} → PW.REL B₁ B₂ _≡_ _∼_ x y → OverΣ (hetRel-IRel {A₁ = B₁} {B₂} _∼_) x y
  from-PW {x = i , s} {.i , t} (P.refl PW., q) = P.refl , q
