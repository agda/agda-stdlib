------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for setoid equality preserving
-- functions.
--
-- NOTE: the first component of the equality is propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.Dependent.Setoid where

open import Data.Product.Base using (map; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent as Σ
open import Level using (Level)
open import Function
open import Function.Consequences
open import Function.Properties.Injection
open import Function.Properties.Surjection
open import Function.Properties.Equivalence
open import Function.Properties.RightInverse
import Function.Properties.Inverse as InverseProperties
open import Relation.Binary.Core using (_=[_]⇒_)
open import Relation.Binary.Bundles as B
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P

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
  cast j≡i = P.subst Carrier (P.sym $ j≡i)
  
  cast-cong : ∀ {i j} {x y : Carrier i}
               (j≡i : j ≡ i) →
               x ≈ y →
               cast j≡i x ≈ cast j≡i y
  cast-cong P.refl p = p

  cast-eq : ∀ {i j x} (eq : i ≡ j) → cast eq x ≈ x
  cast-eq P.refl = IndexedSetoid.refl A

private
  _×ₛ_ : (I : Set i) → IndexedSetoid I a ℓ₁ → Setoid _ _
  I ×ₛ A = Σ.setoid (P.setoid I) A

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
    cong′ (P.refl , ∼) = (P.refl , cong A⟶B ∼)

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

  equivalence-↪ :
    (I↪J : I ↪ J) →
    (∀ {i} → Equivalence (A atₛ (RightInverse.from I↪J i)) (B atₛ i)) →
    Equivalence (I ×ₛ A) (J ×ₛ B)
  equivalence-↪ {A = A} {B = B} I↪J A⇔B =
    equivalence (RightInverse.equivalence I↪J) A→B (fromFunction A⇔B)
    where
    A→B : ∀ {i} → Func (A atₛ i) (B atₛ (RightInverse.to I↪J i))
    A→B = record
      { to   = to      A⇔B ∘ cast      A (RightInverse.strictlyInverseʳ I↪J _)
      ; cong = to-cong A⇔B ∘ cast-cong A (RightInverse.strictlyInverseʳ I↪J _)
      }

  equivalence-↠ :
    (I↠J : I ↠ J) →
    (∀ {x} → Equivalence (A atₛ x) (B atₛ (Surjection.to I↠J x))) →
    Equivalence (I ×ₛ A) (J ×ₛ B)
  equivalence-↠ {A = A} {B = B} I↠J A⇔B =
    equivalence (↠⇒⇔ I↠J) B-to B-from
    where
    B-to : ∀ {x} → Func (A atₛ x) (B atₛ (Surjection.to I↠J x))
    B-to = toFunction A⇔B

    B-from : ∀ {y} → Func (B atₛ y) (A atₛ (Surjection.to⁻ I↠J y))
    B-from = record
      { to   = from      A⇔B ∘ cast      B (Surjection.to∘to⁻ I↠J _)
      ; cong = from-cong A⇔B ∘ cast-cong B (Surjection.to∘to⁻ I↠J _)
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
      lemma P.refl = Injection.injective A↣B

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

    to⁻′ : Carrier (J ×ₛ B) → Carrier (I ×ₛ A)
    to⁻′ (j , y) = to⁻ I↠J j , to⁻ A↠B (cast B (Surjection.to∘to⁻ I↠J _) y)

    strictlySurj : StrictlySurjective (Func.Eq₂._≈_ func) (Func.to func)
    strictlySurj (j , y) = to⁻′ (j , y) ,
      to∘to⁻ I↠J j , IndexedSetoid.trans B (to∘to⁻ A↠B _) (cast-eq B (to∘to⁻ I↠J j))

    surj : Surjective (Func.Eq₁._≈_ func) (Func.Eq₂._≈_ func) (Func.to func)
    surj = strictlySurjective⇒surjective (trans (J ×ₛ B)) (Func.cong func) strictlySurj

------------------------------------------------------------------------
-- LeftInverse

module _ where
  open RightInverse
  open Setoid
  
  left-inverse :
    (I↪J : I ↪ J) →
    (∀ {j} → RightInverse (A atₛ (from I↪J j)) (B atₛ j)) →
    RightInverse (I ×ₛ A) (J ×ₛ B)
  left-inverse {I = I} {J = J} {A = A} {B = B} I↪J A↪B =
    mkRightInverse equiv invʳ
    where
    equiv : Equivalence (I ×ₛ A) (J ×ₛ B)
    equiv = equivalence-↪ I↪J (RightInverse.equivalence A↪B)

    strictlyInvʳ : StrictlyInverseʳ (_≈_ (I ×ₛ A)) (Equivalence.to equiv) (Equivalence.from equiv)
    strictlyInvʳ (i , x) = strictlyInverseʳ I↪J i , IndexedSetoid.trans A (strictlyInverseʳ A↪B _) (cast-eq A (strictlyInverseʳ I↪J i))

    invʳ : Inverseʳ (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) (Equivalence.to equiv) (Equivalence.from equiv)
    invʳ = strictlyInverseʳ⇒inverseʳ {f⁻¹ = Equivalence.from equiv} (trans (I ×ₛ A)) (Equivalence.from-cong equiv) strictlyInvʳ
    

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
    to′-cong (P.refl , x≈y) = to-cong I↔J P.refl , to-cong A↔B x≈y

    from′ : Carrier (J ×ₛ B) → Carrier (I ×ₛ A)
    from′ (j , y) = from I↔J j , from A↔B (cast B (strictlyInverseˡ I↔J _) y)

    from′-cong : Congruent (_≈_ (J ×ₛ B)) (_≈_ (I ×ₛ A)) from′
    from′-cong (P.refl , x≈y) = from-cong I↔J P.refl , from-cong A↔B (cast-cong B (strictlyInverseˡ I↔J _) x≈y)    
    
    strictlyInvˡ : StrictlyInverseˡ (_≈_ (J ×ₛ B)) to′ from′
    strictlyInvˡ (i , x) = strictlyInverseˡ I↔J i ,
        IndexedSetoid.trans B (strictlyInverseˡ A↔B _)
          (cast-eq B (strictlyInverseˡ I↔J i))

    invˡ : Inverseˡ (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′ from′
    invˡ = strictlyInverseˡ⇒inverseˡ {≈₁ = _≈_ (I ×ₛ A)} {f⁻¹ = from′} (trans (J ×ₛ B)) to′-cong strictlyInvˡ

    lem : ∀ {i j} → i ≡ j → ∀ {x : IndexedSetoid.Carrier B (to I↔J i)} {y : IndexedSetoid.Carrier B (to I↔J j)} →
          IndexedSetoid._≈_ B x y →
          IndexedSetoid._≈_ A (from A↔B x) (from A↔B y)
    lem P.refl x≈y = from-cong A↔B x≈y
    
    strictlyInvʳ : StrictlyInverseʳ (_≈_ (I ×ₛ A)) to′ from′
    strictlyInvʳ (i , x) = strictlyInverseʳ I↔J i ,
      IndexedSetoid.trans A (lem (strictlyInverseʳ I↔J _) (cast-eq B (strictlyInverseˡ I↔J _))) (strictlyInverseʳ A↔B _)
      
    invʳ : Inverseʳ (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′ from′
    invʳ = strictlyInverseʳ⇒inverseʳ {f⁻¹ = from′} (trans (I ×ₛ A)) from′-cong strictlyInvʳ
    

