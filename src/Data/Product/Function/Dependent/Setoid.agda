------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for setoid equality preserving
-- functions.
--
-- NOTE: the first component of the equality is propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Function.Dependent.Setoid where

open import Data.Product.Base using (map; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent as Σ
open import Level using (Level)
open import Function
open import Function.Consequences.Setoid
open import Function.Properties.Injection using (mkInjection)
open import Function.Properties.Surjection using (mkSurjection; ↠⇒⇔)
open import Function.Properties.Equivalence using (mkEquivalence; ⇔⇒⟶; ⇔⇒⟵)
open import Function.Properties.RightInverse using (mkRightInverse)
import Function.Construct.Symmetry as Sym
open import Relation.Binary.Core using (_=[_]⇒_)
open import Relation.Binary.Bundles as B
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡

private
  variable
    i a b ℓ₁ ℓ₂ : Level
    I J : Set i
    A B : IndexedSetoid I a ℓ₁

------------------------------------------------------------------------
-- Properties related to "relatedness"
------------------------------------------------------------------------

private module _ (A : IndexedSetoid I a ℓ₁) where
  open IndexedSetoid A

  cast : ∀ {i j} → j ≡ i → Carrier i → Carrier j
  cast j≡i = ≡.subst Carrier (≡.sym $ j≡i)

  cast-cong : ∀ {i j} {x y : Carrier i}
               (j≡i : j ≡ i) →
               x ≈ y →
               cast j≡i x ≈ cast j≡i y
  cast-cong ≡.refl p = p

  cast-eq : ∀ {i j x} (eq : i ≡ j) → cast eq x ≈ x
  cast-eq ≡.refl = IndexedSetoid.refl A

private
  _×ₛ_ : (I : Set i) → IndexedSetoid I a ℓ₁ → Setoid _ _
  I ×ₛ A = Σ.setoid (≡.setoid I) A

------------------------------------------------------------------------
-- Functions

module _ where
  open Func
  open Setoid

  function :
    (f : I ⟶ J) →
    (∀ {i} → Func (A atₛ i) (B atₛ (to f i))) →
    Func (I ×ₛ A) (J ×ₛ B)
  function {I = I} {J = J} {A = A} {B = B} I⟶J A⟶B = record
    { to    = to′
    ; cong  = cong′
    }
    where
    to′ = map (to I⟶J) (to A⟶B)

    cong′ : Congruent (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′
    cong′ (≡.refl , ∼) = (≡.refl , cong A⟶B ∼)

------------------------------------------------------------------------
-- Equivalences

module _ where
  open Equivalence

  equivalence :
    (I⇔J : I ⇔ J) →
    (∀ {i} → Func (A atₛ i) (B atₛ (to   I⇔J i))) →
    (∀ {j} → Func (B atₛ j) (A atₛ (from I⇔J j))) →
    Equivalence (I ×ₛ A) (J ×ₛ B)
  equivalence I⇔J A⟶B B⟶A = mkEquivalence
    (function (⇔⇒⟶ I⇔J) A⟶B)
    (function (⇔⇒⟵ I⇔J) B⟶A)

  module _ (I↪J : I ↪ J) where

    private module ItoJ = RightInverse I↪J

    equivalence-↪ : (∀ {i} → Equivalence (A atₛ (ItoJ.from i)) (B atₛ i)) →
                    Equivalence (I ×ₛ A) (J ×ₛ B)
    equivalence-↪ {A = A} {B = B} A⇔B =
      equivalence ItoJ.equivalence A→B (fromFunction A⇔B)
      where
      A→B : ∀ {i} → Func (A atₛ i) (B atₛ (ItoJ.to i))
      A→B = record
        { to   = to      A⇔B ∘ cast      A (ItoJ.strictlyInverseʳ _)
        ; cong = to-cong A⇔B ∘ cast-cong A (ItoJ.strictlyInverseʳ _)
        }

  module _ (I↠J : I ↠ J) where

    private module ItoJ = Surjection I↠J

    equivalence-↠ : (∀ {x} → Equivalence (A atₛ x) (B atₛ (ItoJ.to x))) →
                    Equivalence (I ×ₛ A) (J ×ₛ B)
    equivalence-↠ {A = A} {B = B} A⇔B = equivalence (↠⇒⇔ I↠J) B-to B-from
      where
      B-to : ∀ {x} → Func (A atₛ x) (B atₛ (ItoJ.to x))
      B-to = toFunction A⇔B

      B-from : ∀ {y} → Func (B atₛ y) (A atₛ (ItoJ.from y))
      B-from = record
        { to   = from      A⇔B ∘ cast      B (ItoJ.strictlyInverseˡ _)
        ; cong = from-cong A⇔B ∘ cast-cong B (ItoJ.strictlyInverseˡ _)
        }

------------------------------------------------------------------------
-- Injections

module _ where
  open Injection hiding (function)
  open IndexedSetoid

  injection :
    (I↣J : I ↣ J) →
    (∀ {i} → Injection (A atₛ i) (B atₛ (Injection.to I↣J i))) →
    Injection (I ×ₛ A) (J ×ₛ B)
  injection {I = I} {J = J} {A = A} {B = B} I↣J A↣B = mkInjection func inj
    where
    func : Func (I ×ₛ A) (J ×ₛ B)
    func = function (Injection.function I↣J) (Injection.function A↣B)

    inj : Injective (Func.Eq₁._≈_ func) (Func.Eq₂._≈_ func) (Func.to func)
    inj (to[i]≡to[j] , y) =
      injective I↣J to[i]≡to[j] ,
      lemma (injective I↣J to[i]≡to[j]) y
      where
      lemma :
        ∀ {i j} {x : Carrier A i} {y : Carrier A j} →
          i ≡ j →
          (_≈_ B (to A↣B x) (to A↣B y)) →
          _≈_ A x y
      lemma ≡.refl = Injection.injective A↣B

------------------------------------------------------------------------
-- Surjections

module _ where
  open Surjection hiding (function)
  open Setoid

  surjection :
    (I↠J : I ↠ J) →
    (∀ {x} → Surjection (A atₛ x) (B atₛ (to I↠J x))) →
    Surjection (I ×ₛ A) (J ×ₛ B)
  surjection {I = I} {J = J} {A = A} {B = B} I↠J A↠B =
    mkSurjection func surj
    where
    func : Func (I ×ₛ A) (J ×ₛ B)
    func = function (Surjection.function I↠J) (Surjection.function A↠B)

    from′ : Carrier (J ×ₛ B) → Carrier (I ×ₛ A)
    from′ (j , y) = from I↠J j , from A↠B (cast B (strictlyInverseˡ I↠J _) y)

    strictlySurj : StrictlySurjective (Func.Eq₂._≈_ func) (Func.to func)
    strictlySurj (j , y) = from′ (j , y) ,
      strictlyInverseˡ I↠J j , IndexedSetoid.trans B (strictlyInverseˡ A↠B _) (cast-eq B (strictlyInverseˡ I↠J j))

    surj : Surjective (Func.Eq₁._≈_ func) (Func.Eq₂._≈_ func) (Func.to func)
    surj = strictlySurjective⇒surjective (I ×ₛ A) (J ×ₛ B) (Func.cong func) strictlySurj

------------------------------------------------------------------------
-- RightInverse

module _ where
  open RightInverse
  open Setoid

  rightInverse :
    (I↪J : I ↪ J) →
    (∀ {j} → RightInverse (A atₛ (from I↪J j)) (B atₛ j)) →
    RightInverse (I ×ₛ A) (J ×ₛ B)
  rightInverse {I = I} {J = J} {A = A} {B = B} I↪J A↪B =
    mkRightInverse equiv invʳ
    where
    equiv : Equivalence (I ×ₛ A) (J ×ₛ B)
    equiv = equivalence-↪ I↪J (RightInverse.equivalence A↪B)

    strictlyInvʳ : StrictlyInverseʳ (_≈_ (I ×ₛ A)) (Equivalence.to equiv) (Equivalence.from equiv)
    strictlyInvʳ (i , x) = strictlyInverseʳ I↪J i , IndexedSetoid.trans A (strictlyInverseʳ A↪B _) (cast-eq A (strictlyInverseʳ I↪J i))

    invʳ : Inverseʳ (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) (Equivalence.to equiv) (Equivalence.from equiv)
    invʳ = strictlyInverseʳ⇒inverseʳ (I ×ₛ A) (J ×ₛ B) (Equivalence.from-cong equiv) strictlyInvʳ

------------------------------------------------------------------------
-- LeftInverse

module _ where
  open LeftInverse
  open Setoid

  leftInverse :
    (I↩J : I ↩ J) →
    (∀ {i} → LeftInverse (A atₛ i) (B atₛ (to I↩J i))) →
    LeftInverse (I ×ₛ A) (J ×ₛ B)
  leftInverse {I = I} {J = J} {A = A} {B = B} I↩J A↩B =
    Sym.leftInverse (rightInverse (Sym.rightInverse I↩J) (Sym.rightInverse A↩B))

------------------------------------------------------------------------
-- Inverses

module _ where
  open Inverse hiding (inverse)
  open Setoid

  inverse : (I↔J : I ↔ J) →
            (∀ {i} → Inverse (A atₛ i) (B atₛ (to I↔J i))) →
            Inverse (I ×ₛ A) (J ×ₛ B)
  inverse {I = I} {J = J} {A = A} {B = B} I↔J A↔B = record
    { to = to′
    ; from = from′
    ; to-cong = to′-cong
    ; from-cong = from′-cong
    ; inverse = invˡ , invʳ
    }
    where
    to′ : Carrier (I ×ₛ A) → Carrier (J ×ₛ B)
    to′ (i , x) = to I↔J i , to A↔B x

    to′-cong : Congruent (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′
    to′-cong (≡.refl , x≈y) = to-cong I↔J ≡.refl , to-cong A↔B x≈y

    from′ : Carrier (J ×ₛ B) → Carrier (I ×ₛ A)
    from′ (j , y) = from I↔J j , from A↔B (cast B (strictlyInverseˡ I↔J _) y)

    from′-cong : Congruent (_≈_ (J ×ₛ B)) (_≈_ (I ×ₛ A)) from′
    from′-cong (≡.refl , x≈y) = from-cong I↔J ≡.refl , from-cong A↔B (cast-cong B (strictlyInverseˡ I↔J _) x≈y)

    strictlyInvˡ : StrictlyInverseˡ (_≈_ (J ×ₛ B)) to′ from′
    strictlyInvˡ (i , x) = strictlyInverseˡ I↔J i ,
        IndexedSetoid.trans B (strictlyInverseˡ A↔B _)
          (cast-eq B (strictlyInverseˡ I↔J i))

    invˡ : Inverseˡ (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′ from′
    invˡ = strictlyInverseˡ⇒inverseˡ (I ×ₛ A) (J ×ₛ B) to′-cong strictlyInvˡ

    lem : ∀ {i j} → i ≡ j → ∀ {x : IndexedSetoid.Carrier B (to I↔J i)} {y : IndexedSetoid.Carrier B (to I↔J j)} →
          IndexedSetoid._≈_ B x y →
          IndexedSetoid._≈_ A (from A↔B x) (from A↔B y)
    lem ≡.refl x≈y = from-cong A↔B x≈y

    strictlyInvʳ : StrictlyInverseʳ (_≈_ (I ×ₛ A)) to′ from′
    strictlyInvʳ (i , x) = strictlyInverseʳ I↔J i ,
      IndexedSetoid.trans A (lem (strictlyInverseʳ I↔J _) (cast-eq B (strictlyInverseˡ I↔J _))) (strictlyInverseʳ A↔B _)

    invʳ : Inverseʳ (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′ from′
    invʳ = strictlyInverseʳ⇒inverseʳ (I ×ₛ A) (J ×ₛ B) from′-cong strictlyInvʳ


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

left-inverse = rightInverse
{-# WARNING_ON_USAGE left-inverse
"Warning: left-inverse was deprecated in v2.3.
Please use rightInverse or leftInverse instead."
#-}
