------------------------------------------------------------------------
-- The Agda standard library
--
-- Extensional pointwise lifting of relations to vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Binary.Pointwise.Extensional where

open import Data.Fin.Base using (zero; suc)
open import Data.Nat.Base using (zero; suc)
open import Data.Vec.Base as Vec hiding ([_]; head; tail; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Inductive
  using ([]; _∷_)
  renaming (Pointwise to IPointwise)
open import Level using (_⊔_)
open import Function using (_∘_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Equiv
  using (_⇔_; ⇔-setoid; equivalence; module Equivalence)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary.Construct.Closure.Transitive as Plus
  hiding (equivalent; map)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

private
  variable
    a b c ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definition

record Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
                 {n} (xs : Vec A n) (ys : Vec B n) : Set (a ⊔ b ⊔ ℓ)
                 where
  constructor ext
  field app : ∀ i → lookup xs i ∼ lookup ys i

------------------------------------------------------------------------
-- Operations

head : ∀ {_∼_ : REL A B ℓ} {n x y xs} {ys : Vec B n} →
       Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
head (ext app) = app zero

tail : ∀ {_∼_ : REL A B ℓ} {n x y xs} {ys : Vec B n} →
       Pointwise _∼_ (x ∷ xs) (y ∷ ys) → Pointwise _∼_ xs ys
tail (ext app) = ext (app ∘ suc)

map : ∀ {_∼_ _∼′_ : REL A B ℓ} {n} →
      _∼_ ⇒ _∼′_ → Pointwise _∼_ ⇒ Pointwise _∼′_ {n}
map ∼⇒∼′ xs∼ys = ext (∼⇒∼′ ∘ Pointwise.app xs∼ys)

gmap : ∀ {_∼_ : Rel A ℓ} {_∼′_ : Rel B ℓ} {f : A → B} {n} →
       _∼_ =[ f ]⇒ _∼′_ →
       Pointwise _∼_ =[ Vec.map {n = n} f ]⇒ Pointwise _∼′_
gmap {_}          ∼⇒∼′ {[]}      {[]}      xs∼ys = ext λ()
gmap {_∼′_ = _∼′_} ∼⇒∼′ {x ∷ xs} {y ∷ ys} xs∼ys = ext λ
  { zero    → ∼⇒∼′ (head xs∼ys)
  ; (suc i) → Pointwise.app (gmap {_∼′_ = _∼′_} ∼⇒∼′ (tail xs∼ys)) i
  }

------------------------------------------------------------------------
-- The inductive and extensional definitions are equivalent.

module _ {_∼_ : REL A B ℓ} where

  extensional⇒inductive : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
                           Pointwise _∼_ xs ys → IPointwise _∼_ xs ys
  extensional⇒inductive {zero} {[]}       {[]}      xs∼ys = []
  extensional⇒inductive {suc n} {x ∷ xs} {y ∷ ys} xs∼ys =
    (head xs∼ys) ∷ extensional⇒inductive (tail xs∼ys)

  inductive⇒extensional : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
                           IPointwise _∼_ xs ys → Pointwise _∼_ xs ys
  inductive⇒extensional []             = ext λ()
  inductive⇒extensional (x∼y ∷ xs∼ys) = ext λ
    { zero    → x∼y
    ; (suc i) → Pointwise.app (inductive⇒extensional xs∼ys) i
    }

  equivalent : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
               Pointwise _∼_ xs ys ⇔ IPointwise _∼_ xs ys
  equivalent = equivalence extensional⇒inductive inductive⇒extensional

------------------------------------------------------------------------
-- Relational properties

refl : ∀ {_∼_ : Rel A ℓ} {n} →
       Reflexive _∼_ → Reflexive (Pointwise _∼_ {n = n})
refl ∼-rfl = ext (λ _ → ∼-rfl)

sym : ∀ {P : REL A B ℓ} {Q : REL B A ℓ} {n} →
      Sym P Q → Sym (Pointwise P) (Pointwise Q {n = n})
sym sm xs∼ys = ext λ i → sm (Pointwise.app xs∼ys i)

trans : ∀ {P : REL A B ℓ} {Q : REL B C ℓ} {R : REL A C ℓ} {n} →
        Trans P Q R →
        Trans (Pointwise P) (Pointwise Q) (Pointwise R {n = n})
trans trns xs∼ys ys∼zs = ext λ i →
  trns (Pointwise.app xs∼ys i) (Pointwise.app ys∼zs i)

decidable : ∀ {_∼_ : REL A B ℓ} →
            Decidable _∼_ → ∀ {n} → Decidable (Pointwise _∼_ {n = n})
decidable dec xs ys = Dec.map
  (Setoid.sym (⇔-setoid _) equivalent)
  (Inductive.decidable dec xs ys)

isEquivalence : ∀ {_∼_ : Rel A ℓ} {n} →
                IsEquivalence _∼_ → IsEquivalence (Pointwise _∼_ {n = n})
isEquivalence equiv = record
  { refl  = refl  Eq.refl
  ; sym   = sym   Eq.sym
  ; trans = trans Eq.trans
  } where module Eq = IsEquivalence equiv

isDecEquivalence : ∀ {_∼_ : Rel A ℓ} {n} →
                   IsDecEquivalence _∼_ →
                   IsDecEquivalence (Pointwise _∼_ {n = n})
isDecEquivalence decEquiv = record
  { isEquivalence = isEquivalence DecEq.isEquivalence
  ; _≟_           = decidable DecEq._≟_
  } where module DecEq = IsDecEquivalence decEquiv

------------------------------------------------------------------------
-- Pointwise _≡_ is equivalent to _≡_.

Pointwise-≡⇒≡ : ∀ {n} {xs ys : Vec A n} → Pointwise _≡_ xs ys → xs ≡ ys
Pointwise-≡⇒≡ {xs = []}     {[]}     (ext app) = P.refl
Pointwise-≡⇒≡ {xs = x ∷ xs} {y ∷ ys} xs∼ys     =
  P.cong₂ _∷_ (head xs∼ys) (Pointwise-≡⇒≡ (tail xs∼ys))

≡⇒Pointwise-≡ : ∀ {n} {xs ys : Vec A n} → xs ≡ ys → Pointwise _≡_ xs ys
≡⇒Pointwise-≡ P.refl = refl P.refl

Pointwise-≡↔≡ : ∀ {n} {xs ys : Vec A n} → Pointwise _≡_ xs ys ⇔ xs ≡ ys
Pointwise-≡↔≡ {ℓ} {A} =
  Equiv.equivalence Pointwise-≡⇒≡ ≡⇒Pointwise-≡

------------------------------------------------------------------------
-- Pointwise and Plus commute when the underlying relation is
-- reflexive.

module _ {_∼_ : Rel A ℓ} where

  ⁺∙⇒∙⁺ : ∀ {n} {xs ys : Vec A n} →
          Plus (Pointwise _∼_) xs ys → Pointwise (Plus _∼_) xs ys
  ⁺∙⇒∙⁺ [ ρ≈ρ′ ]            = ext (λ x → [ Pointwise.app ρ≈ρ′ x ])
  ⁺∙⇒∙⁺ (ρ ∼⁺⟨ ρ≈ρ′ ⟩ ρ′≈ρ″) =  ext (λ x →
    _ ∼⁺⟨ Pointwise.app (⁺∙⇒∙⁺ ρ≈ρ′ ) x ⟩
         Pointwise.app (⁺∙⇒∙⁺ ρ′≈ρ″) x)

  ∙⁺⇒⁺∙ : ∀ {n} {xs ys : Vec A n} → Reflexive _∼_ →
          Pointwise (Plus _∼_) xs ys → Plus (Pointwise _∼_) xs ys
  ∙⁺⇒⁺∙ rfl =
    Plus.map (_⟨$⟩_ (Equivalence.from equivalent)) ∘
    helper ∘
    _⟨$⟩_ (Equivalence.to equivalent)
    where
    helper : ∀ {n} {xs ys : Vec A n} →
             IPointwise (Plus _∼_) xs ys → Plus (IPointwise _∼_) xs ys
    helper []                                                  = [ [] ]
    helper (_∷_ {x = x} {y = y} {xs = xs} {ys = ys} x∼y xs∼ys) =
      x ∷ xs  ∼⁺⟨ Plus.map (_∷ Inductive.refl rfl) x∼y ⟩
      y ∷ xs  ∼⁺⟨ Plus.map (rfl ∷_) (helper xs∼ys) ⟩∎
      y ∷ ys  ∎

-- ∙⁺⇒⁺∙ cannot be defined if the requirement of reflexivity
-- is dropped.
private

 module Counterexample where

  data D : Set where
    i j x y z : D

  data _R_ : Rel D 0ℓ where
    iRj : i R j
    xRy : x R y
    yRz : y R z

  xR⁺z : x [ _R_ ]⁺ z
  xR⁺z =
    x  ∼⁺⟨ [ xRy ] ⟩
    y  ∼⁺⟨ [ yRz ] ⟩∎
    z  ∎

  ix : Vec D 2
  ix = i ∷ x ∷ []

  jz : Vec D 2
  jz = j ∷ z ∷ []

  ix∙⁺jz : IPointwise (Plus _R_) ix jz
  ix∙⁺jz = [ iRj ] ∷ xR⁺z ∷ []

  ¬ix⁺∙jz : ¬ Plus′ (IPointwise _R_) ix jz
  ¬ix⁺∙jz [ iRj ∷ () ∷ [] ]
  ¬ix⁺∙jz ((iRj ∷ xRy ∷ []) ∷ [ () ∷ yRz ∷ [] ])
  ¬ix⁺∙jz ((iRj ∷ xRy ∷ []) ∷ (() ∷ yRz ∷ []) ∷ _)

  counterexample :
    ¬ (∀ {n} {xs ys : Vec D n} →
         Pointwise (Plus _R_) xs ys →
         Plus (Pointwise _R_) xs ys)
  counterexample ∙⁺⇒⁺∙ =
    ¬ix⁺∙jz (Equivalence.to Plus.equivalent ⟨$⟩
               Plus.map (_⟨$⟩_ (Equivalence.to equivalent))
                 (∙⁺⇒⁺∙ (Equivalence.from equivalent ⟨$⟩ ix∙⁺jz)))

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

Pointwise-≡ = Pointwise-≡↔≡
{-# WARNING_ON_USAGE Pointwise-≡
"Warning: Pointwise-≡ was deprecated in v0.15.
Please use Pointwise-≡↔≡ instead."
#-}
