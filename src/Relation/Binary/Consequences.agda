------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties imply others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Consequences where

open import Data.Maybe.Base using (just; nothing; decToMaybe)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Function.Base using (_∘_; _$_; flip)
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (yes; no; recompute)
open import Relation.Nullary.Decidable.Core using (map′)
open import Relation.Unary using (∁)

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Substitutive properties

module _ {_∼_ : Rel A ℓ} (P : Rel A p) where

  subst⟶respˡ : Substitutive _∼_ p → P Respectsˡ _∼_
  subst⟶respˡ subst {y} x'∼x Px'y = subst (flip P y) x'∼x Px'y

  subst⟶respʳ : Substitutive _∼_ p → P Respectsʳ _∼_
  subst⟶respʳ subst {x} y'∼y Pxy' = subst (P x) y'∼y Pxy'

  subst⟶resp₂ : Substitutive _∼_ p → P Respects₂ _∼_
  subst⟶resp₂ subst = subst⟶respʳ subst , subst⟶respˡ subst

module _ {_∼_ : Rel A ℓ} {P : A → Set p} where

  P-resp⟶¬P-resp : Symmetric _∼_ → P Respects _∼_ → (∁ P) Respects _∼_
  P-resp⟶¬P-resp sym resp x∼y ¬Px Py = ¬Px (resp (sym x∼y) Py)

------------------------------------------------------------------------
-- Proofs for non-strict orders

module _ {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂} where

  total⟶refl : _≤_ Respects₂ _≈_ → Symmetric _≈_ →
               Total _≤_ → _≈_ ⇒ _≤_
  total⟶refl (respʳ , respˡ) sym total {x} {y} x≈y with total x y
  ... | inj₁ x∼y = x∼y
  ... | inj₂ y∼x = respʳ x≈y (respˡ (sym x≈y) y∼x)

  total+dec⟶dec : _≈_ ⇒ _≤_ → Antisymmetric _≈_ _≤_ →
                  Total _≤_ → Decidable _≈_ → Decidable _≤_
  total+dec⟶dec refl antisym total _≟_ x y with total x y
  ... | inj₁ x≤y = yes x≤y
  ... | inj₂ y≤x = map′ refl (flip antisym y≤x) (x ≟ y)

------------------------------------------------------------------------
-- Proofs for strict orders

module _ {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where

  trans∧irr⟶asym : Reflexive _≈_ → Transitive _<_ →
                   Irreflexive _≈_ _<_ → Asymmetric _<_
  trans∧irr⟶asym refl trans irrefl x<y y<x =
    irrefl refl (trans x<y y<x)

  irr∧antisym⟶asym : Irreflexive _≈_ _<_ → Antisymmetric _≈_ _<_ →
                     Asymmetric _<_
  irr∧antisym⟶asym irrefl antisym x<y y<x =
    irrefl (antisym x<y y<x) x<y

  asym⟶antisym : Asymmetric _<_ → Antisymmetric _≈_ _<_
  asym⟶antisym asym x<y y<x = ⊥-elim (asym x<y y<x)

  asym⟶irr : _<_ Respects₂ _≈_ → Symmetric _≈_ →
             Asymmetric _<_ → Irreflexive _≈_ _<_
  asym⟶irr (respʳ , respˡ) sym asym {x} {y} x≈y x<y =
    asym x<y (respʳ (sym x≈y) (respˡ x≈y x<y))

  tri⟶asym : Trichotomous _≈_ _<_ → Asymmetric _<_
  tri⟶asym tri {x} {y} x<y x>y with tri x y
  ... | tri< _   _ x≯y = x≯y x>y
  ... | tri≈ _   _ x≯y = x≯y x>y
  ... | tri> x≮y _ _   = x≮y x<y

  tri⟶irr : Trichotomous _≈_ _<_ → Irreflexive _≈_ _<_
  tri⟶irr compare {x} {y} x≈y x<y with compare x y
  ... | tri< _   x≉y y≮x = x≉y x≈y
  ... | tri> x≮y x≉y y<x = x≉y x≈y
  ... | tri≈ x≮y _   y≮x = x≮y x<y

  tri⟶dec≈ : Trichotomous _≈_ _<_ → Decidable _≈_
  tri⟶dec≈ compare x y with compare x y
  ... | tri< _ x≉y _ = no  x≉y
  ... | tri≈ _ x≈y _ = yes x≈y
  ... | tri> _ x≉y _ = no  x≉y

  tri⟶dec< : Trichotomous _≈_ _<_ → Decidable _<_
  tri⟶dec< compare x y with compare x y
  ... | tri< x<y _ _ = yes x<y
  ... | tri≈ x≮y _ _ = no  x≮y
  ... | tri> x≮y _ _ = no  x≮y

  trans∧tri⟶respʳ≈ : Symmetric _≈_ → Transitive _≈_ →
                     Transitive _<_ → Trichotomous _≈_ _<_ →
                     _<_ Respectsʳ _≈_
  trans∧tri⟶respʳ≈ sym ≈-tr <-tr tri {x} {y} {z} y≈z x<y with tri x z
  ... | tri< x<z _ _ = x<z
  ... | tri≈ _ x≈z _ = ⊥-elim (tri⟶irr tri (≈-tr x≈z (sym y≈z)) x<y)
  ... | tri> _ _ z<x = ⊥-elim (tri⟶irr tri (sym y≈z) (<-tr z<x x<y))

  trans∧tri⟶respˡ≈ : Transitive _≈_ →
                     Transitive _<_ → Trichotomous _≈_ _<_ →
                     _<_ Respectsˡ _≈_
  trans∧tri⟶respˡ≈ ≈-tr <-tr tri {z} {_} {y} x≈y x<z with tri y z
  ... | tri< y<z _ _ = y<z
  ... | tri≈ _ y≈z _ = ⊥-elim (tri⟶irr tri (≈-tr x≈y y≈z) x<z)
  ... | tri> _ _ z<y = ⊥-elim (tri⟶irr tri x≈y (<-tr x<z z<y))

  trans∧tri⟶resp≈ : Symmetric _≈_ → Transitive _≈_ →
                    Transitive _<_ → Trichotomous _≈_ _<_ →
                    _<_ Respects₂ _≈_
  trans∧tri⟶resp≈ sym ≈-tr <-tr tri =
    trans∧tri⟶respʳ≈ sym ≈-tr <-tr tri ,
    trans∧tri⟶respˡ≈ ≈-tr <-tr tri

------------------------------------------------------------------------
-- Without Loss of Generality

module _  {_R_ : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  wlog : Total _R_ → Symmetric Q →
         (∀ a b → a R b → Q a b) →
         ∀ a b → Q a b
  wlog r-total q-sym prf a b with r-total a b
  ... | inj₁ aRb = prf a b aRb
  ... | inj₂ bRa = q-sym (prf b a bRa)

------------------------------------------------------------------------
-- Other proofs

module _ {P : REL A B p} where

  dec⟶weaklyDec : Decidable P → WeaklyDecidable P
  dec⟶weaklyDec dec x y = decToMaybe (dec x y)

module _ {P : REL A B ℓ₁} {Q : REL A B ℓ₂} where

  map-NonEmpty : P ⇒ Q → NonEmpty P → NonEmpty Q
  map-NonEmpty f x = nonEmpty (f (NonEmpty.proof x))

module _ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} where

  flip-Connex : Connex P Q → Connex Q P
  flip-Connex f x y = Sum.swap (f y x)

module _ {r} {R : REL A B r} where

  dec⟶recomputable : Decidable R → Recomputable R
  dec⟶recomputable dec {a} {b} = recompute $ dec a b
