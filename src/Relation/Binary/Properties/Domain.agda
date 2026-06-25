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
open import Data.Product using (_,_; ∃)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.Domain.Definitions
open import Relation.Binary.Domain.Bundles using (DirectedCompletePartialOrder)
open import Relation.Binary.Domain.Structures
  using (IsDirectedFamily; IsDirectedCompletePartialOrder; IsLub; IsScottContinuous)
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)

private variable
  c₁ ℓ₁₁ ℓ₁₂ c₂ ℓ₂₁ ℓ₂₂ c ℓ₁ ℓ₂ a ℓ : Level
  Ix A B : Set a

------------------------------------------------------------------------
-- Properties of least upper bounds

module _ (D : DirectedCompletePartialOrder c ℓ₁ ℓ₂) where
  private
    module D = DirectedCompletePartialOrder D

  uniqueLub : ∀ {s : Ix → D.Carrier} → (x y : D.Carrier) →
              IsLub D.poset s x → IsLub D.poset s y →  x D.≈ y
  uniqueLub x y x-lub y-lub = D.antisym
    (IsLub.isLeast x-lub y (IsLub.isUpperBound y-lub))
    (IsLub.isLeast y-lub x (IsLub.isUpperBound x-lub))

  IsLub-cong : ∀ {s : Ix → D.Carrier} → {x y : D.Carrier} → x D.≈ y →
              IsLub D.poset s x → IsLub D.poset s y
  IsLub-cong x≈y x-lub = record
    { isLeastUpperBound =
    (λ i → D.trans (IsLub.isUpperBound x-lub i) (D.reflexive x≈y))
    , (λ z ub → D.trans (D.reflexive (D.Eq.sym x≈y)) (IsLub.isLeast x-lub z (λ i → D.trans (ub i) (D.reflexive D.Eq.refl))))
    }

------------------------------------------------------------------------
-- Scott continuity and monotonicity

module _ {P : Poset c₁ ℓ₁₁ ℓ₁₂} {Q : Poset c₂ ℓ₂₁ ℓ₂₂} where
  private
    module P = Poset P
    module Q = Poset Q

  isMonotone : (P-DirectedCompletePartialOrder : IsDirectedCompletePartialOrder P) →
               (f : P.Carrier → Q.Carrier) → (isCts : IsScottContinuous P Q f) →
               IsOrderHomomorphism P._≈_ Q._≈_ P._≤_ Q._≤_ f
  isMonotone P-DirectedCompletePartialOrder f isCts = record
    { cong = IsScottContinuous.cong isCts
    ; mono = mono-proof
    }
    where
      mono-proof : ∀ {x y} → x P.≤ y → f x Q.≤ f y
      mono-proof {x} {y} x≤y = IsLub.isUpperBound fs-lub (lift true)
        where
          s : Lift c₁ Bool → P.Carrier
          s (lift b) = if b then x else y

          sx≤sfalse : ∀ b → s b P.≤ s (lift false)
          sx≤sfalse (lift true) = x≤y
          sx≤sfalse (lift false) = P.refl

          s-directed : IsDirectedFamily P s
          s-directed = record
            { elt = lift true
            ; isSemidirected = λ i j → (lift false , sx≤sfalse i , sx≤sfalse j)
            }

          s-lub : IsLub P s y
          s-lub = record { isLeastUpperBound = sx≤sfalse , (λ _ proof → proof (lift false))}

          fs-lub : IsLub Q (f ∘ s) (f y)
          fs-lub = IsScottContinuous.preserveLub isCts s-directed y s-lub

  map-directed : {s : Ix → P.Carrier} → (f : P.Carrier → Q.Carrier)→
                      IsOrderHomomorphism P._≈_ Q._≈_ P._≤_ Q._≤_ f →
                      IsDirectedFamily P s → IsDirectedFamily Q (f ∘ s)
  map-directed f ismonotone dir = record
    { elt = IsDirectedFamily.elt dir
    ; isSemidirected = semi
    }
    where
      module f = IsOrderHomomorphism ismonotone

      semi = λ i j → let (k , s[i]≤s[k] , s[j]≤s[k]) = IsDirectedFamily.isSemidirected dir i j
            in k , f.mono  s[i]≤s[k] , f.mono s[j]≤s[k]

------------------------------------------------------------------------
-- Scott continuous functions

module _  {P Q R : Poset c ℓ₁ ℓ₂} where
  private
    module P = Poset P
    module Q = Poset Q
    module R = Poset R

  ScottId : {P : Poset c ℓ₁ ℓ₂} → IsScottContinuous P P id
  ScottId = record
    { preserveLub = λ _ _ → id
    ; cong = id }

  cts-cong : (f : R.Carrier  → Q.Carrier) (g : P.Carrier → R.Carrier) →
            IsScottContinuous R Q f → IsScottContinuous P R g →
            IsOrderHomomorphism P._≈_ R._≈_ P._≤_ R._≤_ g → IsScottContinuous P Q (f ∘ g)
  cts-cong f g isCtsf isCtsG monog = record
    { preserveLub = λ dir lub → f.preserveLub (map-directed g monog dir) (g lub) ∘ g.preserveLub dir lub
    ; cong = f.cong ∘ g.cong
    }
    where
      module f = IsScottContinuous isCtsf
      module g = IsScottContinuous isCtsG

------------------------------------------------------------------------
-- Suprema and pointwise ordering

module _ {P : Poset c ℓ₁ ℓ₂} (D : DirectedCompletePartialOrder c ℓ₁ ℓ₂) where
  private
    module D = DirectedCompletePartialOrder D
    DP = D.poset

  lub-monotone : {s s' : Ix → D.Carrier} →
                {fam : IsDirectedFamily DP s} {fam' : IsDirectedFamily DP s'} →
                (∀ i → s i D.≤ s' i) → D.⋁ s fam D.≤ D.⋁ s' fam'
  lub-monotone {s' = s'} {fam' = fam'} p = D.⋁-least (D.⋁ s' fam') λ i → D.trans (p i) (D.⋁-≤ i)

------------------------------------------------------------------------
-- Scott continuity module

module ScottContinuity
  (D E : DirectedCompletePartialOrder c ℓ₁ ℓ₂)
  where
  private
    module D = DirectedCompletePartialOrder D
    module E = DirectedCompletePartialOrder E
    DP = D.poset
    EP = E.poset

  module _ (f : D.Carrier → E.Carrier)
           (isScott : IsScottContinuous DP EP f)
           (mono : IsOrderHomomorphism D._≈_ E._≈_ D._≤_ E._≤_ f)
    where
      private module f = IsOrderHomomorphism mono

      pres-lub : (s : Ix → D.Carrier) → (dir : IsDirectedFamily DP s) →
                f (D.⋁ s dir) E.≈ E.⋁ (f ∘ s) (map-directed f mono dir)
      pres-lub s dir = E.antisym
        (IsLub.isLeast
          (IsScottContinuous.preserveLub isScott dir (D.⋁ s dir) (D.⋁-isLub s dir))
          (E.⋁ (f ∘ s) (map-directed f mono dir))
          E.⋁-≤
          )
        (IsLub.isLeast
          (E.⋁-isLub (f ∘ s) (map-directed f mono dir))
          (f (D.⋁ s dir))
          (λ i → f.mono (D.⋁-≤ i))
          )

      isScottContinuous : (∀ {Ix} (s : Ix → D.Carrier) (dir : IsDirectedFamily DP s) →
                IsLub E.poset (f ∘ s) (f (D.⋁ s dir))) →
                IsScottContinuous DP EP f
      isScottContinuous pres-⋁ = record
        { preserveLub = λ {_} {s} dir lub x →
          IsLub-cong E (f.cong (uniqueLub D (D.⋁ s dir) lub (D.⋁-isLub s dir) x)) (pres-⋁ s dir)
        ; cong = f.cong
        }
