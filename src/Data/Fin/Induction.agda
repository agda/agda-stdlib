------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over Fin
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool as Bool
  using (Bool; false; true; if_then_else_; f≤t; b≤b; f<t)
open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Maybe using (Maybe; just; nothing; is-nothing)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _∸_; z≤n; s≤s)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (∃; _,_; proj₁; proj₂; curry; uncurry)
open import Function using (_∘_; flip)
open import Induction
open import Induction.WellFounded as WF
open import Level using (Level)
open import Relation.Binary
  using (Rel; Decidable; IsPartialOrder; IsStrictPartialOrder; StrictPartialOrder)
import Relation.Binary.Construct.NonStrictToStrict as ToStrict
import Relation.Binary.Construct.On as On
import Relation.Binary.Properties.StrictPartialOrder as SPO
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
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

  open IsStrictPartialOrder isSPO using (irrefl; module Eq)
    renaming (trans to ⊏-trans; <-respʳ-≈ to ⊏-respʳ-≈)

  -- Intuition: there cannot be any infinite descending chains simply
  -- because Fin n has only finitely many inhabitants.  Thus any chain
  -- of length > n must have a cycle (which is forbidden by
  -- irreflexivity).

  private  -- Private setup/helpers for the proof

    -- Step 1: define prefix tables, a data structure to keep track of
    -- the possible prefixes of a chain starting at `x'.  If the chain
    -- has a prefix ending in `y', then the table contains a proof of
    -- `x ⊏ y' in row `y'.  Otherwise, that row is blank (represented
    -- by `nothing').  Since the "table" is really just a map from
    -- `Fin n' to ⊏-proofs, we represent it using a function.

    Prefixes : Fin n → Set r
    Prefixes x = (y : Fin n) → Maybe (x ⊏ y)

    -- The empty prefix table (all rows are blank).

    empty : ∀ x → Prefixes x
    empty _ _ = nothing

    -- Extend every prefix in the the table with `x ⊏ y' and add a new
    -- entry at `y'.

    extend : ∀ {x y} → x ⊏ y → Prefixes y → Prefixes x
    extend {_} {y} x⊏y ps z with ps z | y ≈? z
    ... | just y⊏z | _       = just (⊏-trans x⊏y y⊏z)
    ... | nothing  | yes y≈z = just (⊏-respʳ-≈ y≈z x⊏y)
    ... | nothing  | no  y≉z = nothing

    -- A helper: count the number of `true' instances in Boolean
    -- valuation.

    count : ∀ {k} → (Fin k → Bool) → ℕ
    count {zero}  f = zero
    count {suc k} f = if f zero then suc rest else rest
      where rest = count (f ∘ suc)

    -- The number of blank rows in a prefix table.

    blanks : ∀ {x} → Prefixes x → ℕ
    blanks ps = count (is-nothing ∘ ps)

    -- Step 2: define a well-founded order on prefix tables.  We note
    -- that the number of blanks in a prefix table strictly decreases
    -- whenever we extend the table with a new ⊏-step.  This is
    -- because a (decreasing) ⊏-chain can never revisit an element of
    -- `Fin n' twice, otherwise there would be a cycle.  Hence an
    -- extension by `x ⊏ y' must add a _new_ entry at `y' in the
    -- prefix table (see proofs `extend-*' below).  Hence we may use
    -- the number of blanks as a (termination) measure and derive a
    -- well-founded order from it.

    _≺P_ : Rel (∃ Prefixes) _
    (_ , ps) ≺P (_ , ps′) = blanks ps ℕ.< blanks ps′

    ≺P-wf : WellFounded _≺P_
    ≺P-wf = On.wellFounded (blanks ∘ proj₂) ℕ.<-wellFounded

    -- More helpers: pointwise greater valuations have a greater
    -- number of `true' entries.

    count-≤ : ∀ {k} {f g : Fin k → Bool} →
              (∀ z → f z Bool.≤ g z) → count f ℕ.≤ count g
    count-≤ {zero}          f≤g = z≤n
    count-≤ {suc k} {f} {g} f≤g with f zero | g zero | f≤g zero
    ... | .false | .true  | f≤t = ℕ.≤-step (count-≤ (f≤g ∘ suc))
    ... | false  | .false | b≤b = count-≤ (f≤g ∘ suc)
    ... | true   | .true  | b≤b = s≤s (count-≤ (f≤g ∘ suc))

    count-< : ∀ {k} {f g : Fin k → Bool} x →
              f x Bool.< g x → (∀ z → f z Bool.≤ g z) → count f ℕ.< count g
    count-< {_} {f} {g} zero diff f≤g with f zero | g zero
    count-< zero f<t f≤g | .false | .true = s≤s (count-≤ (f≤g ∘ suc))
    count-< {_} {f} {g} (suc x) diff f≤g with f zero | g zero | f≤g zero
    ... | .false | .true  | f≤t = s≤s (count-≤ (f≤g ∘ suc))
    ... | false  | .false | b≤b = count-< x diff (f≤g ∘ suc)
    ... | true   | .true  | b≤b = s≤s (count-< x diff (f≤g ∘ suc))

    -- Extending a prefix table decreases the number of blanks.

    extend-≤ : ∀ {x y} (p : x ⊏ y) (ps : Prefixes y) →
               ∀ z → is-nothing ((extend p ps) z) Bool.≤ is-nothing (ps z)
    extend-≤ {_} {y} x⊏y ps z with ps z | y ≈? z
    ... | just _  | _       = b≤b
    ... | nothing | yes y≈z = f≤t
    ... | nothing | no _    = b≤b

    extend-< : ∀ {x y} (p : x ⊏ y) (ps : Prefixes y) →
               is-nothing ((extend p ps) y) Bool.< is-nothing (ps y)
    extend-< {_} {y} x⊏y ps with ps y | y ≈? y
    ... | just y⊏y | _      = contradiction y⊏y (irrefl Eq.refl)
    ... | nothing  | yes _  = f<t
    ... | nothing  | no y≉y = contradiction Eq.refl y≉y

    extend-≺P : ∀ {x y} (p : x ⊏ y) (ps : Prefixes y) →
               (x , extend p ps) ≺P (y , ps)
    extend-≺P {_} {y} x⊏y ps = count-< y (extend-< x⊏y ps) (extend-≤ x⊏y ps)

    -- Step 3: prove that very element `x' is accessible by
    -- well-founded recursion on prefix tables.  Every recursive step
    -- adds a new entry to the prefix table and thus decreases the
    -- number of blank rows in the table, making the table "smaller".

    ⊏-acc′ : ∀ x → (ps : Prefixes x) →
             (∀ y → (qs : Prefixes y) → blanks qs ℕ.< blanks ps → Acc _⊏_ y) →
             Acc _⊏_ x
    ⊏-acc′ x ps rec = acc (λ y y⊏x → rec y (extend y⊏x ps) (extend-≺P y⊏x ps))

  ⊏-acc : ∀ x → Acc _⊏_ x
  ⊏-acc x =
    All.wfRec ≺P-wf r (Acc _⊏_ ∘ proj₁)
              (uncurry λ x ps rec → ⊏-acc′ x ps (curry rec)) (x , empty x)

  ⊏-wellFounded : WellFounded _⊏_
  ⊏-wellFounded x = ⊏-acc x

module Wf {n e r} {_≈_ : Rel (Fin n) e} {_⊑_ : Rel (Fin n) r}
          (_≈?_  : Decidable _≈_)
          (isPO : IsPartialOrder _≈_ _⊑_) where

  open StrictWf _≈?_ (ToStrict.<-isStrictPartialOrder _≈_ _⊑_ isPO) public
    using (⊏-wellFounded)

-- The inverse order is also well-founded, i.e. every (strict) partial
-- order is also Noetherian.

module StrictNoetherian {n e r} {_≈_ : Rel (Fin n) e} {_⊏_ : Rel (Fin n) r}
                        (_≈?_  : Decidable _≈_)
                        (isSPO : IsStrictPartialOrder _≈_ _⊏_) where

  spo : StrictPartialOrder _ _ _
  spo = record { isStrictPartialOrder = isSPO }
  open SPO spo using (_>_; >-isStrictPartialOrder)
  open StrictWf _≈?_ >-isStrictPartialOrder public
    using () renaming (⊏-wellFounded to ⊏-noetherian)

module Noetherian {n e r} {_≈_ : Rel (Fin n) e} {_⊑_ : Rel (Fin n) r}
                  (_≈?_  : Decidable _≈_)
                  (isPO : IsPartialOrder _≈_ _⊑_) where

  open StrictNoetherian _≈?_ (ToStrict.<-isStrictPartialOrder _≈_ _⊑_ isPO)
    public using (⊏-noetherian)

-- A special case: every strict partial order over `Fin n' is
-- well-founded and noetherian if the underlying equality is just _≡_.

module _ {n r} {_⊏_ : Rel (Fin n) r} where

  spo-wellFounded : IsStrictPartialOrder _≡_ _⊏_ → WellFounded _⊏_
  spo-wellFounded spo = StrictWf.⊏-wellFounded _≟_ spo

  spo-noetherian : IsStrictPartialOrder _≡_ _⊏_ → WellFounded (flip _⊏_)
  spo-noetherian spo = StrictNoetherian.⊏-noetherian _≟_ spo
