------------------------------------------------------------------------
-- The Agda standard library
--
-- Choosing between elements based on the result of applying a function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (SelectiveMagma)

module Algebra.Construct.LiftedChoice where

open import Algebra.FunctionProperties
open import Algebra.FunctionProperties.Consequences
open import Algebra.Structures
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_)
open import Level using (Level; _⊔_)
open import Function using (id; _on_)
open import Function.Injection using (Injection)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Unary using (Pred)
open import Relation.Nullary.Negation using (contradiction)

import Relation.Binary.Reasoning.Setoid as EqReasoning

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

module _ (_≈_ : Rel B ℓ) (_•_ : Op₂ B) where

  Lift : Selective _≈_ _•_ → (A → B) → Op₂ A
  Lift ∙-sel f x y with ∙-sel (f x) (f y)
  ... | inj₁ _ = x
  ... | inj₂ _ = y

------------------------------------------------------------------------
-- Algebraic properties

module _ {_≈_ : Rel B ℓ} {_∙_ : Op₂ B}
         (∙-isSelectiveMagma : IsSelectiveMagma _≈_ _∙_) where

  private module M = IsSelectiveMagma ∙-isSelectiveMagma
  open M hiding (sel; isMagma)
  open EqReasoning setoid

  module _ (f : A → B) where

    private
      _◦_ = Lift _≈_ _∙_ M.sel f

    sel-≡ : Selective _≡_ _◦_
    sel-≡ x y with M.sel (f x) (f y)
    ... | inj₁ _ = inj₁ P.refl
    ... | inj₂ _ = inj₂ P.refl

    distrib : ∀ x y → ((f x) ∙ (f y)) ≈ f (x ◦ y)
    distrib x y with M.sel (f x) (f y)
    ... | inj₁ fx∙fy≈fx = fx∙fy≈fx
    ... | inj₂ fx∙fy≈fy = fx∙fy≈fy

  module _ (f : A → B) {_≈′_ : Rel A ℓ}
           (≈-reflexive : _≡_ ⇒ _≈′_) where

    private
      _◦_ = Lift _≈_ _∙_ M.sel f

    sel : Selective _≈′_ _◦_
    sel x y = Sum.map ≈-reflexive ≈-reflexive (sel-≡ f x y)

    idem : Idempotent _≈′_ _◦_
    idem = sel⇒idem _≈′_ sel

  module _ {f : A → B} {_≈′_ : Rel A ℓ}
           (f-injective : ∀ {x y} → f x ≈ f y → x ≈′ y)
           where

    private
      _◦_ = Lift _≈_ _∙_ M.sel f

    cong : f Preserves _≈′_ ⟶ _≈_ → Congruent₂ _≈′_ _◦_
    cong f-cong {x} {y} {u} {v} x≈y u≈v
      with M.sel (f x) (f u) | M.sel (f y) (f v)
    ... | inj₁ fx∙fu≈fx | inj₁ fy∙fv≈fy = x≈y
    ... | inj₂ fx∙fu≈fu | inj₂ fy∙fv≈fv = u≈v
    ... | inj₁ fx∙fu≈fx | inj₂ fy∙fv≈fv = f-injective (begin
      f x       ≈⟨ sym fx∙fu≈fx ⟩
      f x ∙ f u ≈⟨ ∙-cong (f-cong x≈y) (f-cong u≈v) ⟩
      f y ∙ f v ≈⟨ fy∙fv≈fv ⟩
      f v       ∎)
    ... | inj₂ fx∙fu≈fu | inj₁ fy∙fv≈fy = f-injective (begin
      f u       ≈⟨ sym fx∙fu≈fu ⟩
      f x ∙ f u ≈⟨ ∙-cong (f-cong x≈y) (f-cong u≈v) ⟩
      f y ∙ f v ≈⟨ fy∙fv≈fy ⟩
      f y       ∎)

    assoc : Associative _≈_ _∙_ → Associative _≈′_ _◦_
    assoc ∙-assoc x y z = f-injective (begin
      f ((x ◦ y) ◦ z)   ≈˘⟨ distrib f (x ◦ y) z ⟩
      f (x ◦ y) ∙ f z   ≈˘⟨ ∙-congʳ (distrib f x y) ⟩
      (f x ∙ f y) ∙ f z ≈⟨  ∙-assoc (f x) (f y) (f z) ⟩
      f x ∙ (f y ∙ f z) ≈⟨  ∙-congˡ (distrib f y z) ⟩
      f x ∙ f (y ◦ z)   ≈⟨  distrib f x (y ◦ z) ⟩
      f (x ◦ (y ◦ z))   ∎)

    comm : Commutative _≈_ _∙_ → Commutative _≈′_ _◦_
    comm ∙-comm x y = f-injective (begin
      f (x ◦ y) ≈˘⟨ distrib f x y ⟩
      f x ∙ f y ≈⟨  ∙-comm (f x) (f y) ⟩
      f y ∙ f x ≈⟨  distrib f y x ⟩
      f (y ◦ x) ∎)

------------------------------------------------------------------------
-- Algebraic structures

  module _ {_≈′_ : Rel A ℓ} {f : A → B}
           (f-injective : ∀ {x y} → f x ≈ f y → x ≈′ y)
           (f-cong : f Preserves _≈′_ ⟶ _≈_)
           (≈′-isEquivalence : IsEquivalence _≈′_)
           where

    private
      module E = IsEquivalence ≈′-isEquivalence
      _◦_ = Lift _≈_ _∙_ M.sel f

    isMagma : IsMagma _≈′_ _◦_
    isMagma = record
      { isEquivalence = ≈′-isEquivalence
      ; ∙-cong        = cong (λ {x y} → f-injective {x} {y}) f-cong
      }

    isSemigroup : Associative _≈_ _∙_ → IsSemigroup _≈′_ _◦_
    isSemigroup ∙-assoc = record
      { isMagma = isMagma
      ; assoc   = assoc (λ {x y} → f-injective {x} {y}) ∙-assoc
      }

    isBand : Associative _≈_ _∙_ → IsBand _≈′_ _◦_
    isBand ∙-assoc = record
      { isSemigroup = isSemigroup ∙-assoc
      ; idem        = idem f E.reflexive
      }

    isSemilattice : Associative _≈_ _∙_ → Commutative _≈_ _∙_ →
                    IsSemilattice _≈′_ _◦_
    isSemilattice ∙-assoc ∙-comm = record
      { isBand = isBand ∙-assoc
      ; comm   = comm (λ {x y} → f-injective {x} {y}) ∙-comm
      }

    isSelectiveMagma : IsSelectiveMagma _≈′_ _◦_
    isSelectiveMagma = record
      { isMagma = isMagma
      ; sel     = sel f E.reflexive
      }

------------------------------------------------------------------------
-- Other properties

  module _ {ℓ} {_≈′_ : Rel A ℓ} {P : Pred A p} (f : A → B) where

    private
      _◦_ = Lift _≈_ _∙_ M.sel f

    preservesᵒ : (∀ {x y} → P x → (f x ∙ f y) ≈ f y → P y) →
                 (∀ {x y} → P y → (f x ∙ f y) ≈ f x → P x) →
                 ∀ x y → P x ⊎ P y → P (x ◦ y)
    preservesᵒ left right x y (inj₁ px) with M.sel (f x) (f y)
    ... | inj₁ _        = px
    ... | inj₂ fx∙fy≈fx = left px fx∙fy≈fx
    preservesᵒ left right x y (inj₂ py) with M.sel (f x) (f y)
    ... | inj₁ fx∙fy≈fy = right py fx∙fy≈fy
    ... | inj₂ _        = py

    preservesʳ : (∀ {x y} → P y → (f x ∙ f y) ≈ f x → P x) →
                 ∀ x {y} → P y → P (x ◦ y)
    preservesʳ right x {y} Py with M.sel (f x) (f y)
    ... | inj₁ fx∙fy≈fx = right Py fx∙fy≈fx
    ... | inj₂ fx∙fy≈fy = Py

    preservesᵇ : ∀ (P : Pred A p) → ∀ {x y} → P x → P y → P (x ◦ y)
    preservesᵇ P {x} {y} Px Py with M.sel (f x) (f y)
    ... | inj₁ _ = Px
    ... | inj₂ _ = Py

    forcesᵇ : (∀ {x y} → P x → (f x ∙ f y) ≈ f x → P y) →
              (∀ {x y} → P y → (f x ∙ f y) ≈ f y → P x) →
              ∀ x y → P (x ◦ y) → P x × P y
    forcesᵇ presˡ presʳ x y P[x∙y] with M.sel (f x) (f y)
    ... | inj₁ fx∙fy≈fx = P[x∙y] , presˡ P[x∙y] fx∙fy≈fx
    ... | inj₂ fx∙fy≈fy = presʳ P[x∙y] fx∙fy≈fy , P[x∙y]
