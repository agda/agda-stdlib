------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over Fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-} -- for deprecated _≺_ (issue #1726)

open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _∸_; s≤s)
open import Data.Nat.Properties using (n<1+n; ≤⇒≯)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (_,_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.Linked as Linked using (Linked; [-]; _∷_)
import Data.Vec.Relation.Unary.Linked.Properties as Linkedₚ
open import Function.Base using (flip; _$_)
open import Induction
open import Induction.WellFounded as WF
open import Level using (Level)
open import Relation.Binary
  using (Rel; Decidable; IsPartialOrder; IsStrictPartialOrder; StrictPartialOrder)
import Relation.Binary.Construct.Flip.EqAndOrd as EqAndOrd
import Relation.Binary.Construct.Flip.Ord as Ord
import Relation.Binary.Construct.NonStrictToStrict as ToStrict
import Relation.Binary.Construct.On as On
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

module Data.Fin.Induction where

private
  variable
    ℓ : Level
    n : ℕ

------------------------------------------------------------------------
-- Re-export accessability

open WF public using (Acc; acc)

------------------------------------------------------------------------
-- Induction over _<_

<-wellFounded : WellFounded {A = Fin n} _<_
<-wellFounded = On.wellFounded toℕ ℕ.<-wellFounded

<-weakInduction-startingFrom : ∀ (P : Pred (Fin (suc n)) ℓ) →
                               ∀ {i} → P i →
                               (∀ j → P (inject₁ j) → P (suc j)) →
                               ∀ {j} → j ≥ i → P j
<-weakInduction-startingFrom P {i} Pi Pᵢ⇒Pᵢ₊₁ {j} j≥i = induct (<-wellFounded _) (<-cmp i j) j≥i
  where
  induct : ∀ {j} → Acc _<_ j → Tri (i < j) (i ≡ j) (i > j) → j ≥ i → P j
  induct (acc rs) (tri≈ _ refl _) i≤j = Pi
  induct (acc rs) (tri> _ _ i>sj) i≤j with () ← ≤⇒≯ i≤j i>sj
  induct {suc j} (acc rs) (tri< (s≤s i≤j) _ _) _ = Pᵢ⇒Pᵢ₊₁ j P[1+j]
    where
    toℕj≡toℕinjJ = sym $ toℕ-inject₁ j
    P[1+j] = induct (rs _ (s≤s (subst (ℕ._≤ toℕ j) toℕj≡toℕinjJ ≤-refl)))
      (<-cmp i $ inject₁ j) (subst (toℕ i ℕ.≤_) toℕj≡toℕinjJ i≤j)

<-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P zero →
                  (∀ i → P (inject₁ i) → P (suc i)) →
                  ∀ i → P i
<-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁ i = <-weakInduction-startingFrom P P₀ Pᵢ⇒Pᵢ₊₁ ℕ.z≤n


------------------------------------------------------------------------
-- Induction over _>_

private
  acc-map : ∀ {x : Fin n} → Acc ℕ._<_ (n ∸ toℕ x) → Acc _>_ x
  acc-map {n} (acc rs) = acc λ y y>x →
    acc-map (rs (n ∸ toℕ y) (ℕ.∸-monoʳ-< y>x (toℕ≤n y)))

>-wellFounded : WellFounded {A = Fin n} _>_
>-wellFounded {n} x = acc-map (ℕ.<-wellFounded (n ∸ toℕ x))

>-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P (fromℕ n) →
                  (∀ i → P (suc i) → P (inject₁ i)) →
                  ∀ i → P i
>-weakInduction {n = n} P Pₙ Pᵢ₊₁⇒Pᵢ i = induct (>-wellFounded i)
  where
  induct : ∀ {i} → Acc _>_ i → P i
  induct {i} (acc rec) with n ℕ.≟ toℕ i
  ... | yes n≡i = subst P (toℕ-injective (trans (toℕ-fromℕ n) n≡i)) Pₙ
  ... | no  n≢i = subst P (inject₁-lower₁ i n≢i) (Pᵢ₊₁⇒Pᵢ _ Pᵢ₊₁)
    where Pᵢ₊₁ = induct (rec _ (ℕ.≤-reflexive (cong suc (sym (toℕ-lower₁ i n≢i)))))

------------------------------------------------------------------------
-- Well-foundedness of other (strict) partial orders on Fin

module _ {_≈_ : Rel (Fin n) ℓ} where

  -- Every (strict) partial order over `Fin n' is well-founded.

  -- Intuition: there cannot be any infinite descending chains simply
  -- because Fin n has only finitely many inhabitants.  Thus any chain
  -- of length > n must have a cycle (which is forbidden by
  -- irreflexivity).

  spo-wellFounded : ∀ {r} {_⊏_ : Rel (Fin n) r} →
                    IsStrictPartialOrder _≈_ _⊏_ → WellFounded _⊏_
  spo-wellFounded {_} {_⊏_} isSPO i = go n i pigeon where

    module ⊏ = IsStrictPartialOrder isSPO

    go : ∀ m i →
         ((xs : Vec (Fin n) m) → Linked (flip _⊏_) (i ∷ xs) → WellFounded _⊏_) →
         Acc _⊏_ i
    go zero    i k = k [] [-] i
    go (suc m) i k = acc $ λ j j⊏i → go m j (λ xs i∷xs↑ → k (j ∷ xs) (j⊏i ∷ i∷xs↑))

    pigeon : (xs : Vec (Fin n) n) → Linked (flip _⊏_) (i ∷ xs) → WellFounded _⊏_
    pigeon xs i∷xs↑ =
      let (i₁ , i₂ , i₁<i₂ , xs[i₁]≡xs[i₂]) = pigeonhole (n<1+n n) (Vec.lookup (i ∷ xs)) in
      let xs[i₁]⊏xs[i₂] = Linkedₚ.lookup⁺ (Ord.transitive _⊏_ ⊏.trans) {xs = i ∷ xs} i∷xs↑ i₁<i₂ in
      let xs[i₁]⊏xs[i₁] = ⊏.<-respʳ-≈ (⊏.Eq.reflexive xs[i₁]≡xs[i₂]) xs[i₁]⊏xs[i₂] in
      contradiction xs[i₁]⊏xs[i₁] (⊏.irrefl ⊏.Eq.refl)

  po-wellFounded : ∀ {r} {_⊑_ : Rel (Fin n) r} →
                   IsPartialOrder _≈_ _⊑_ → WellFounded (ToStrict._<_ _≈_ _⊑_)
  po-wellFounded isPO =
    spo-wellFounded (ToStrict.<-isStrictPartialOrder _≈_ _ isPO)

  -- The inverse order is also well-founded, i.e. every (strict)
  -- partial order is also Noetherian.

  spo-noetherian : ∀ {r} {_⊏_ : Rel (Fin n) r} →
                   IsStrictPartialOrder _≈_ _⊏_ → WellFounded (flip _⊏_)
  spo-noetherian isSPO = spo-wellFounded (EqAndOrd.isStrictPartialOrder isSPO)

  po-noetherian : ∀ {r} {_⊑_ : Rel (Fin n) r} → IsPartialOrder _≈_ _⊑_ →
                  WellFounded (flip (ToStrict._<_ _≈_ _⊑_))
  po-noetherian isPO =
    spo-noetherian (ToStrict.<-isStrictPartialOrder _≈_ _ isPO)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

≺-Rec : RecStruct ℕ ℓ ℓ
≺-Rec = WfRec _≺_

≺-wellFounded : WellFounded _≺_
≺-wellFounded = Subrelation.wellFounded ≺⇒<′ ℕ.<′-wellFounded

module _ {ℓ} where
  open WF.All ≺-wellFounded ℓ public
    renaming
    ( wfRecBuilder to ≺-recBuilder
    ; wfRec        to ≺-rec
    )
    hiding (wfRec-builder)

{-# WARNING_ON_USAGE ≺-Rec
"Warning: ≺-Rec was deprecated in v2.0.
Please use <-Rec instead."
#-}
{-# WARNING_ON_USAGE ≺-wellFounded
"Warning: ≺-wellFounded was deprecated in v2.0.
Please use <-wellFounded instead."
#-}
{-# WARNING_ON_USAGE ≺-recBuilder
"Warning: ≺-recBuilder was deprecated in v2.0.
Please use <-recBuilder instead."
#-}
{-# WARNING_ON_USAGE ≺-rec
"Warning: ≺-rec was deprecated in v2.0.
Please use <-rec instead."
#-}

