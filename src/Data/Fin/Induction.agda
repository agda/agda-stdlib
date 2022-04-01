------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over Fin
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (n<1+n)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Function.Base using (flip; _$_)
open import Induction
open import Induction.WellFounded as WF
open import Level using (Level)
open import Relation.Binary using (Rel; Decidable; IsStrictPartialOrder)
import Relation.Binary.Construct.On as On
open import Relation.Unary using (Pred)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality

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

<-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P zero →
                  (∀ i → P (inject₁ i) → P (suc i)) →
                  ∀ i → P i
<-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁ i = induct (<-wellFounded i)
  where
  induct : ∀ {i} → Acc _<_ i → P i
  induct {zero}  _         = P₀
  induct {suc i} (acc rec) = Pᵢ⇒Pᵢ₊₁ i (induct (rec (inject₁ i) i<i+1))
    where i<i+1 = ℕ<⇒inject₁< (i<1+i i)

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
-- Induction over _≺_

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


------------------------------------------------------------------------
-- Well-foundedness of other (strict) partial orders on Fin
------------------------------------------------------------------------

-- Every (strict) partial order over `Fin n' is well-founded, provided
-- the underlying equality is decidable.

module StrictWf {n e r} {_≈_ : Rel (Fin n) e} {_⊏_ : Rel (Fin n) r}
                (_≈?_  : Decidable _≈_)
                (isSPO : IsStrictPartialOrder _≈_ _⊏_) where

  import Relation.Binary.Construct.Flip as Flip
  open import Data.Product using (_,_)
  open import Data.Vec.Base as Vec using (Vec; []; _∷_)
  open import Data.Vec.Relation.Unary.Linked as Linked using (Linked; [-]; _∷_)
  import Data.Vec.Relation.Unary.Linked.Properties as Linkedₚ

  ⊏-wellFounded : WellFounded _⊏_
  ⊏-wellFounded i = go n i pigeon where

    go : ∀ m i →
         ((xs : Vec (Fin n) m) → Linked (flip _⊏_) (i ∷ xs) → WellFounded _⊏_) →
         Acc _⊏_ i
    go zero    i k = k [] [-] i
    go (suc m) i k = acc $ λ j j⊏i → go m j (λ xs i∷xs↑ → k (j ∷ xs) (j⊏i ∷ i∷xs↑))

    pigeon : (xs : Vec (Fin n) n) → Linked (flip _⊏_) (i ∷ xs) → WellFounded _⊏_
    pigeon xs i∷xs↑ =
      let module STO = IsStrictPartialOrder isSPO in
      let (i₁ , i₂ , i₁<i₂ , xs[i₁]≡xs[i₂]) = pigeonhole (n<1+n n) (Vec.lookup (i ∷ xs)) in
      let xs[i₁]⊏xs[i₂] = Linkedₚ.lookup (Flip.transitive _⊏_ STO.trans) {xs = i ∷ xs} i₁<i₂ i∷xs↑ in
      let xs[i₁]⊏xs[i₁] = STO.<-respʳ-≈ (STO.Eq.reflexive xs[i₁]≡xs[i₂]) xs[i₁]⊏xs[i₂] in
      contradiction xs[i₁]⊏xs[i₁] (STO.irrefl STO.Eq.refl)
