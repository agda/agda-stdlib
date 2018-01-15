module Data.Product.Relation.SigmaPropositional where

open import Level using (_⊔_)

open import Relation.Binary as B using (REL; Rel)
open import Relation.Binary.PropositionalEquality
  as P
  using (_≡_; _→-setoid_; _≗_)
import Data.Product.Relation.SigmaPointwise as PW

open import Data.Product using (Σ; ∃; _,_)

module _ {a b} {A : Set a} {B : A → Set b} where
  OverPath
    : ∀ {p} → (∀ {x} → B x → B x → Set p)
    → {x y : A} → x ≡ y → REL (B x) (B y) p
  OverPath ∼ P.refl = ∼

  OverΣ
    : ∀ {p} → (∀ {x} → B x → B x → Set p)
    → Rel (∃ B) (a ⊔ p)
  OverΣ ∼ (i , x) (j , y) = Σ (i ≡ j) (λ p → OverPath ∼ p x y)

  module _ {p} {_∼_ : ∀ {x} → B x → B x → Set p} where
    refl : (∀ {x} → B.Reflexive (_∼_ {x})) → B.Reflexive (OverΣ _∼_)
    refl refl′ = P.refl , refl′

    symmetric : (∀ {x} → B.Symmetric (_∼_ {x})) → B.Symmetric (OverΣ _∼_)
    symmetric sym (P.refl , p) = P.refl , sym p

    transitive : (∀ {x} → B.Transitive (_∼_ {x})) → B.Transitive (OverΣ _∼_)
    transitive trans (P.refl , p) (P.refl , q) = P.refl , trans p q

    isEquivalence : (∀ {x} → B.IsEquivalence (_∼_ {x})) → B.IsEquivalence (OverΣ _∼_)
    isEquivalence isEquivalence′ = record
      { refl = refl (B.IsEquivalence.refl isEquivalence′)
      ; sym = symmetric (B.IsEquivalence.sym isEquivalence′)
      ; trans = transitive (B.IsEquivalence.trans isEquivalence′)
      }

setoid : ∀ {a b p} {A : Set a} → (A → B.Setoid b p) → B.Setoid (a ⊔ b) (a ⊔ p)
setoid S = record
  { isEquivalence = isEquivalence (λ {x} → B.Setoid.isEquivalence (S x))
  }

module _ {a b} {A : Set a} {B : A → Set b} where
  module _ {p} {_∼_ : ∀ {x} → B x → B x → Set p} where
    hom
      : ∀ {c q} {C : A → Set c} {_∼′_ : ∀ {x} → C x → C x → Set q}
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
  module _ {p} {_∼_ : ∀ {x} → B x → B x → Set p} where
    ≡-cong :
      ∀ {c} {C : A → Set c}
      → (∀ {x} → B.Reflexive (_∼_ {x}))
      → (h : ∀ {x} → C x → B x)
      → ∀ {x y}
      → {s : C x} {t : C y}
      → OverΣ _≡_ (x , s) (y , t)
      → OverΣ _∼_ (x , h s) (y , h t)
    ≡-cong refl h p = hom (λ {P.refl → refl}) p

to-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : ∃ B} → OverΣ _≡_ x y → x ≡ y
to-≡ (P.refl , P.refl) = P.refl

from-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : ∃ B} → x ≡ y → OverΣ _≡_ x y
from-≡ P.refl = P.refl , P.refl
