------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties imply others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Consequences where

open import Data.Product.Base using (_,_)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_]′)
open import Function.Base using (_∘_; _∘₂_; _$_; flip)
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Decidable.Core
  using (yes; no; recompute; map′; dec⇒maybe)
open import Relation.Unary using (∁; Pred)

private
  variable
    a ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ p : Level
    A B C : Set a

------------------------------------------------------------------------
-- Substitutive properties

module _ {_∼_ : Rel A ℓ} (R : Rel A p) where

  subst⇒respˡ : Substitutive _∼_ p → R Respectsˡ _∼_
  subst⇒respˡ subst {y} x′∼x Px′y = subst (flip R y) x′∼x Px′y

  subst⇒respʳ : Substitutive _∼_ p → R Respectsʳ _∼_
  subst⇒respʳ subst {x} y′∼y Pxy′ = subst (R x) y′∼y Pxy′

  subst⇒resp₂ : Substitutive _∼_ p → R Respects₂ _∼_
  subst⇒resp₂ subst = subst⇒respʳ subst , subst⇒respˡ subst

module _ {_∼_ : Rel A ℓ} {P : Pred A p} where

  resp⇒¬-resp : Symmetric _∼_ → P Respects _∼_ → (∁ P) Respects _∼_
  resp⇒¬-resp sym resp x∼y ¬Px Py = ¬Px (resp (sym x∼y) Py)

------------------------------------------------------------------------
-- Proofs for negation

module _ {_∼_ : Rel A ℓ} where

  sym⇒¬-sym : Symmetric _∼_ → Symmetric (¬_ ∘₂ _∼_)
  sym⇒¬-sym sym≁ x≁y y∼x = x≁y (sym≁ y∼x)

  -- N.B. the implicit arguments to Cotransitive are permuted w.r.t.
  -- those of Transitive
  cotrans⇒¬-trans : Cotransitive _∼_ → Transitive (¬_ ∘₂ _∼_)
  cotrans⇒¬-trans cotrans x≁z z≁y x∼y = [ x≁z , z≁y ]′ (cotrans x∼y _)

------------------------------------------------------------------------
-- Proofs for Irreflexive relations

module _ {_≈_ : Rel A ℓ₁} {_∼_ : Rel A ℓ₂} where

  irrefl⇒¬-refl : Reflexive _≈_ → Irreflexive _≈_ _∼_ →
                  Reflexive (¬_ ∘₂ _∼_)
  irrefl⇒¬-refl re irr = irr re

------------------------------------------------------------------------
-- Proofs for non-strict orders

module _ {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂} where

  total⇒refl : _≤_ Respects₂ _≈_ → Symmetric _≈_ →
               Total _≤_ → _≈_ ⇒ _≤_
  total⇒refl (respʳ , respˡ) sym total {x} {y} x≈y with total x y
  ... | inj₁ x∼y = x∼y
  ... | inj₂ y∼x = respʳ x≈y (respˡ (sym x≈y) y∼x)

  total∧dec⇒dec : _≈_ ⇒ _≤_ → Antisymmetric _≈_ _≤_ →
                  Total _≤_ → Decidable _≈_ → Decidable _≤_
  total∧dec⇒dec refl antisym total _≈?_ x y with total x y
  ... | inj₁ x≤y = yes x≤y
  ... | inj₂ y≤x = map′ refl (flip antisym y≤x) (x ≈? y)

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) {≤₁ : Rel A ℓ₃} {≤₂ : Rel B ℓ₄} where

  mono⇒cong : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ →
              ∀ {f} → Monotonic₁ ≤₁ ≤₂ f → Monotonic₁ ≈₁ ≈₂ f
  mono⇒cong sym reflexive antisym mono x≈y = antisym
    (mono (reflexive x≈y))
    (mono (reflexive (sym x≈y)))

  antimono⇒cong : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ →
                  ∀ {f} → f Preserves ≤₁ ⟶ (flip ≤₂) → Monotonic₁ ≈₁ ≈₂ f
  antimono⇒cong sym reflexive antisym antimono p≈q = antisym
    (antimono (reflexive (sym p≈q)))
    (antimono (reflexive p≈q))

  mono₂⇒cong₂ : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ →
                ∀ {f} → Monotonic₂ ≤₁ ≤₁ ≤₂ f → Monotonic₂ ≈₁ ≈₁ ≈₂ f
  mono₂⇒cong₂ sym reflexive antisym mono x≈y u≈v = antisym
    (mono (reflexive x≈y) (reflexive u≈v))
    (mono (reflexive (sym x≈y)) (reflexive (sym u≈v)))

module _ (≤₁ : Rel A ℓ₁) (≤₂ : Rel B ℓ₂) (≤₃ : Rel C ℓ₂) where

  mono₂⇒monoˡ : ∀ {f} → Reflexive ≤₁ →
                Monotonic₂ ≤₁ ≤₂ ≤₃ f → LeftMonotonic ≤₂ ≤₃ f
  mono₂⇒monoˡ refl mono x = mono (refl {x = x})

  mono₂⇒monoʳ : ∀ {f} → Reflexive ≤₂ →
                Monotonic₂ ≤₁ ≤₂ ≤₃ f → RightMonotonic ≤₁ ≤₃ f
  mono₂⇒monoʳ refl mono y = flip mono (refl {x = y})

  monoˡ∧monoʳ⇒mono₂ : ∀ {f} → Transitive ≤₃ →
                      LeftMonotonic ≤₂ ≤₃ f → RightMonotonic ≤₁ ≤₃ f →
                      Monotonic₂ ≤₁ ≤₂ ≤₃ f
  monoˡ∧monoʳ⇒mono₂ trans monoˡ monoʳ x≤₁y u≤₂v =
    trans (monoˡ _ u≤₂v) (monoʳ _ x≤₁y)

------------------------------------------------------------------------
-- Proofs for strict orders

module _ {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where

  trans∧irr⇒asym : Reflexive _≈_ → Transitive _<_ →
                   Irreflexive _≈_ _<_ → Asymmetric _<_
  trans∧irr⇒asym refl trans irrefl x<y y<x =
    irrefl refl (trans x<y y<x)

  irr∧antisym⇒asym : Irreflexive _≈_ _<_ → Antisymmetric _≈_ _<_ →
                     Asymmetric _<_
  irr∧antisym⇒asym irrefl antisym x<y y<x =
    irrefl (antisym x<y y<x) x<y

  asym⇒antisym : Asymmetric _<_ → Antisymmetric _≈_ _<_
  asym⇒antisym asym x<y y<x = contradiction y<x (asym x<y)

  asym⇒irr : _<_ Respects₂ _≈_ → Symmetric _≈_ →
             Asymmetric _<_ → Irreflexive _≈_ _<_
  asym⇒irr (respʳ , respˡ) sym asym {x} {y} x≈y x<y =
    asym x<y (respʳ (sym x≈y) (respˡ x≈y x<y))

  tri⇒asym : Trichotomous _≈_ _<_ → Asymmetric _<_
  tri⇒asym tri {x} {y} x<y x>y with tri x y
  ... | tri< _   _ x≯y = x≯y x>y
  ... | tri≈ _   _ x≯y = x≯y x>y
  ... | tri> x≮y _ _   = x≮y x<y

  tri⇒irr : Trichotomous _≈_ _<_ → Irreflexive _≈_ _<_
  tri⇒irr compare {x} {y} x≈y x<y with compare x y
  ... | tri< _   x≉y y≮x = x≉y x≈y
  ... | tri> x≮y x≉y y<x = x≉y x≈y
  ... | tri≈ x≮y _   y≮x = x≮y x<y

  tri⇒dec≈ : Trichotomous _≈_ _<_ → Decidable _≈_
  tri⇒dec≈ compare x y with compare x y
  ... | tri< _ x≉y _ = no  x≉y
  ... | tri≈ _ x≈y _ = yes x≈y
  ... | tri> _ x≉y _ = no  x≉y

  tri⇒dec< : Trichotomous _≈_ _<_ → Decidable _<_
  tri⇒dec< compare x y with compare x y
  ... | tri< x<y _ _ = yes x<y
  ... | tri≈ x≮y _ _ = no  x≮y
  ... | tri> x≮y _ _ = no  x≮y

  trans∧tri⇒respʳ : Symmetric _≈_ → Transitive _≈_ →
                    Transitive _<_ → Trichotomous _≈_ _<_ →
                    _<_ Respectsʳ _≈_
  trans∧tri⇒respʳ sym ≈-tr <-tr tri {x} {y} {z} y≈z x<y with tri x z
  ... | tri< x<z _ _ = x<z
  ... | tri≈ _ x≈z _ = contradiction x<y (tri⇒irr tri (≈-tr x≈z (sym y≈z)))
  ... | tri> _ _ z<x = contradiction (<-tr z<x x<y) (tri⇒irr tri (sym y≈z))

  trans∧tri⇒respˡ : Transitive _≈_ →
                    Transitive _<_ → Trichotomous _≈_ _<_ →
                    _<_ Respectsˡ _≈_
  trans∧tri⇒respˡ ≈-tr <-tr tri {z} {_} {y} x≈y x<z with tri y z
  ... | tri< y<z _ _ = y<z
  ... | tri≈ _ y≈z _ = contradiction x<z (tri⇒irr tri (≈-tr x≈y y≈z))
  ... | tri> _ _ z<y = contradiction (<-tr x<z z<y) (tri⇒irr tri x≈y)

  trans∧tri⇒resp : Symmetric _≈_ → Transitive _≈_ →
                   Transitive _<_ → Trichotomous _≈_ _<_ →
                   _<_ Respects₂ _≈_
  trans∧tri⇒resp sym ≈-tr <-tr tri =
    trans∧tri⇒respʳ sym ≈-tr <-tr tri ,
    trans∧tri⇒respˡ ≈-tr <-tr tri

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

module _ {R : REL A B p} where

  dec⇒weaklyDec : Decidable R → WeaklyDecidable R
  dec⇒weaklyDec dec x y = dec⇒maybe (dec x y)

  dec⇒recomputable : Decidable R → Recomputable R
  dec⇒recomputable dec {a} {b} = recompute $ dec a b

module _ {R : REL A B ℓ₁} {S : REL A B ℓ₂} where

  map-NonEmpty : R ⇒ S → NonEmpty R → NonEmpty S
  map-NonEmpty f x = nonEmpty (f (NonEmpty.proof x))

module _ {R : REL A B ℓ₁} {S : REL B A ℓ₂} where

  flip-Connex : Connex R S → Connex S R
  flip-Connex f x y = Sum.swap (f y x)
