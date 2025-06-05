------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by directed complete partial orders
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Properties.Domain where

open import Relation.Binary.Bundles using (Poset)
open import Level using (Level; Lift; lift)
open import Function using (_∘_; id)
open import Data.Product using (_,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.Domain.Definitions
open import Relation.Binary.Domain.Bundles using (DirectedCompletePartialOrder)
open import Relation.Binary.Domain.Structures
  using (IsDirectedFamily; IsDirectedCompletePartialOrder; IsLub; IsScottContinuous)
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)

private variable
  c ℓ₁ ℓ₂ o ℓ : Level
  Ix A B : Set o

------------------------------------------------------------------------
-- Properties of least upper bounds

module _ {c ℓ₁ ℓ₂} {D : DirectedCompletePartialOrder c ℓ₁ ℓ₂ } where
  private
    module D = DirectedCompletePartialOrder D

  uniqueLub : ∀ {Ix} {s : Ix → D.Carrier}
    → (x y : D.Carrier) → IsLub D.poset s x → IsLub D.poset s y
    →  x D.≈ y
  uniqueLub x y x-lub y-lub = D.antisym
    (IsLub.isLeast x-lub y (IsLub.isUpperBound y-lub))
    (IsLub.isLeast y-lub x (IsLub.isUpperBound x-lub))

  IsLub-cong : ∀ {Ix} {s : Ix → D.Carrier}
    → (x y : D.Carrier)
    → x D.≈ y
    → IsLub D.poset s x → IsLub D.poset s y
  IsLub-cong x y x≈y x-lub = record
    { isLeastUpperBound = (λ i → D.trans (IsLub.isUpperBound x-lub i) (D.reflexive x≈y)) ,
                         (λ z ub → D.trans (D.reflexive (D.Eq.sym x≈y))
                           (IsLub.isLeast x-lub z (λ i → D.trans (ub i) (D.reflexive D.Eq.refl))))
    }

------------------------------------------------------------------------
-- Scott continuity and monotonicity

module _ {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} where

  private
    module P = Poset P
    module Q = Poset Q

  DirectedCompletePartialOrder+scott→monotone : (P-DirectedCompletePartialOrder : IsDirectedCompletePartialOrder P)
    → (f : P.Carrier → Q.Carrier)
    → (scott : IsScottContinuous f)
    → IsOrderHomomorphism (Poset._≈_ P) (Poset._≈_ Q) (Poset._≤_ P) (Poset._≤_ Q) f
  DirectedCompletePartialOrder+scott→monotone P-DirectedCompletePartialOrder f scott = record
    { cong = λ {x} {y} x≈y → IsScottContinuous.preserveEquality scott x≈y
    ; mono = λ {x} {y} x≤y → mono-proof x y x≤y
    }
    where
      mono-proof : ∀ x y → x P.≤ y → f x Q.≤ f y
      mono-proof x y x≤y = IsLub.isUpperBound fs-lub (lift true)
        where
          s : Lift c Bool → P.Carrier
          s (lift b) = if b then x else y

          sx≤sfalse : ∀ b → s b P.≤ s (lift false)
          sx≤sfalse (lift true) = x≤y
          sx≤sfalse (lift false) = P.refl

          s-directed : IsDirectedFamily P s
          s-directed = record
            { elt = lift true
            ; semidirected = λ i j → (lift false , sx≤sfalse i , sx≤sfalse j)
            }

          s-lub : IsLub P s y
          s-lub = record
            { isLeastUpperBound = sx≤sfalse , (λ z proof → proof (lift false))
            }

          fs-lub : IsLub Q (f ∘ s) (f y)
          fs-lub = IsScottContinuous.preserveLub scott s-directed y s-lub

  monotone∘directed : ∀ {Ix : Set c} {s : Ix → P.Carrier}
    → (f : P.Carrier → Q.Carrier)
    → IsOrderHomomorphism (Poset._≈_ P) (Poset._≈_ Q) (Poset._≤_ P) (Poset._≤_ Q) f
    → IsDirectedFamily P s
    → IsDirectedFamily Q (f ∘ s)
  monotone∘directed f ismonotone dir = record
    { elt = IsDirectedFamily.elt dir
    ; isSemidirected = λ i j →
        let (k , s[i]≤s[k] , s[j]≤s[k]) = IsDirectedFamily.semidirected dir i j
        in k , IsOrderHomomorphism.mono ismonotone s[i]≤s[k] , IsOrderHomomorphism.mono ismonotone s[j]≤s[k]
    }

------------------------------------------------------------------------
-- Scott continuous functions

ScottId : ∀ {c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} → IsScottContinuous {P = P} {Q = P} id
ScottId = record
  { preserveLub = λ dir lub z → z
  ; preserveEquality = λ z → z }

scott-∘ : ∀ {c ℓ₁ ℓ₂} {P Q R : Poset c ℓ₁ ℓ₂}
  → (f : Poset.Carrier R → Poset.Carrier Q) (g : Poset.Carrier P → Poset.Carrier R)
  → IsScottContinuous {P = R} {Q = Q} f → IsScottContinuous {P = P} {Q = R} g
  → IsOrderHomomorphism (Poset._≈_ P) (Poset._≈_ R) (Poset._≤_ P) (Poset._≤_ R) g
  → IsScottContinuous {P = P} {Q = Q} (f ∘ g)
scott-∘ f g scottf scottg monog = record
  { preserveLub = λ dir lub z → f.preserveLub
      (monotone∘directed g monog dir)
      (g lub)
      (g.preserveLub dir lub z)
  ; preserveEquality = λ {x} {y} z →
    f.preserveEquality (g.preserveEquality z)
  }
  where
    module f = IsScottContinuous scottf
    module g = IsScottContinuous scottg

------------------------------------------------------------------------
-- Suprema and pointwise ordering

module _ {c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} (D : DirectedCompletePartialOrder c ℓ₁ ℓ₂) where
  private
    module D = DirectedCompletePartialOrder D

  open import Relation.Binary.Reasoning.PartialOrder D.poset

  ⋃-pointwise : ∀ {Ix} {s s' : Ix → D.Carrier}
    → {fam : IsDirectedFamily D.poset s} {fam' : IsDirectedFamily D.poset s'}
    → (∀ ix → s ix D.≤ s' ix)
    → D.⋁ s fam D.≤ D.⋁ s' fam'
  ⋃-pointwise {s = s} {s'} {fam} {fam'} p =
    D.⋁-least (D.⋁ s' fam') λ i → D.trans (p i) (D.⋁-≤ i)

------------------------------------------------------------------------
-- Scott continuity module

module Scott
  {c ℓ₁ ℓ₂}
  {P : Poset c ℓ₁ ℓ₂}
  {D E : DirectedCompletePartialOrder c ℓ₁ ℓ₂}
  (let module D = DirectedCompletePartialOrder D)
  (let module E = DirectedCompletePartialOrder E)
  (f : D.Carrier → E.Carrier)
  (isScott : IsScottContinuous {P = D.poset} {Q = E.poset} f)
  (mono : IsOrderHomomorphism (Poset._≈_ D.poset) (Poset._≈_ E.poset)
                             (Poset._≤_ D.poset) (Poset._≤_ E.poset) f)
  where

    open DirectedCompletePartialOrder D
    open DirectedCompletePartialOrder E

    pres-⋁
      : ∀ {Ix} (s : Ix → D.Carrier) → (dir : IsDirectedFamily D.poset s)
      → f (D.⋁ s dir) E.≈ E.⋁ (f ∘ s) (monotone∘directed f mono dir)
    pres-⋁ s dir = E.antisym
      (IsLub.isLeast
        (IsScottContinuous.preserveLub isScott dir (D.⋁ s dir) (D.⋁-isLub s dir))
        (E.⋁ (f ∘ s) (monotone∘directed f mono dir))
        E.⋁-≤
        )
      (IsLub.isLeast
        (E.⋁-isLub (f ∘ s) (monotone∘directed f mono dir))
        (f (D.⋁ s dir))
        (λ i → IsOrderHomomorphism.mono mono (D.⋁-≤ i))
        )

------------------------------------------------------------------------
-- Converting to Scott continuity

module _ {c ℓ₁ ℓ₂} {D E : DirectedCompletePartialOrder c ℓ₁ ℓ₂} where
  private
    module D = DirectedCompletePartialOrder D
    module E = DirectedCompletePartialOrder E

  to-scott : (f : D.Carrier → E.Carrier)
    → IsOrderHomomorphism (Poset._≈_ D.poset) (Poset._≈_ E.poset)
    (Poset._≤_ D.poset) (Poset._≤_ E.poset) f
    → (∀ {Ix} (s : Ix → D.Carrier) (dir : IsDirectedFamily D.poset s)
    → IsLub E.poset (f ∘ s) (f (D.⋁ s dir)))
    → IsScottContinuous {P = D.poset} {Q = E.poset} f
  to-scott f mono pres-⋁ = record
    { preserveLub = λ dir lub x → IsLub-cong {P = E.poset} {D = E} (f (D.⋁ _ dir)) (f lub)
        (IsOrderHomomorphism.cong mono (uniqueLub {P = E.poset} {D = D} (D.⋁ _ dir) lub (D.⋁-isLub _ dir) x))
        (pres-⋁ _ dir)
    ; preserveEquality = IsOrderHomomorphism.cong mono }
