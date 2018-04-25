------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Properties where

open import Algebra
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin
open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s; z≤n; _∸_) renaming
  (_≤_ to _ℕ≤_
  ; _<_ to _ℕ<_
  ; _+_ to _ℕ+_)
import Data.Nat.Properties as ℕₚ
open import Data.Product
open import Function
open import Function.Equality as FunS using (_⟨$⟩_)
open import Function.Injection using (_↣_)
open import Algebra.FunctionProperties
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Unary using (Pred)
open import Category.Functor
open import Category.Applicative

------------------------------------------------------------------------
-- Properties of _≡_

suc-injective : ∀ {o} {m n : Fin o} → Fin.suc m ≡ suc n → m ≡ n
suc-injective refl = refl

preorder : ℕ → Preorder _ _ _
preorder n = P.preorder (Fin n)

setoid : ℕ → Setoid _ _
setoid n = P.setoid (Fin n)

isDecEquivalence : ∀ {n} → IsDecEquivalence (_≡_ {A = Fin n})
isDecEquivalence = record
  { isEquivalence = P.isEquivalence
  ; _≟_           = _≟_
  }

decSetoid : ℕ → DecSetoid _ _
decSetoid n = record
  { Carrier          = Fin n
  ; _≈_              = _≡_
  ; isDecEquivalence = isDecEquivalence
  }

------------------------------------------------------------------------
-- Converting between Fin n and Nat

to-from : ∀ n → toℕ (fromℕ n) ≡ n
to-from zero    = refl
to-from (suc n) = cong suc (to-from n)

from-to : ∀ {n} (i : Fin n) → fromℕ (toℕ i) ≡ strengthen i
from-to zero    = refl
from-to (suc i) = cong suc (from-to i)

toℕ-strengthen : ∀ {n} (i : Fin n) → toℕ (strengthen i) ≡ toℕ i
toℕ-strengthen zero    = refl
toℕ-strengthen (suc i) = cong suc (toℕ-strengthen i)

toℕ-injective : ∀ {n} {i j : Fin n} → toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {zero}  {}      {}      _
toℕ-injective {suc n} {zero}  {zero}  eq = refl
toℕ-injective {suc n} {zero}  {suc j} ()
toℕ-injective {suc n} {suc i} {zero}  ()
toℕ-injective {suc n} {suc i} {suc j} eq =
  cong suc (toℕ-injective (cong ℕ.pred eq))

bounded : ∀ {n} (i : Fin n) → toℕ i ℕ< n
bounded zero    = s≤s z≤n
bounded (suc i) = s≤s (bounded i)

prop-toℕ-≤ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ ℕ.pred n
prop-toℕ-≤ zero                 = z≤n
prop-toℕ-≤ (suc {n = zero}  ())
prop-toℕ-≤ (suc {n = suc n} i)  = s≤s (prop-toℕ-≤ i)

-- A simpler implementation of prop-toℕ-≤,
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of prop-toℕ-≤,
-- it can be removed in favor of prop-toℕ-≤′.
prop-toℕ-≤′ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ ℕ.pred n
prop-toℕ-≤′ i = ℕₚ.<⇒≤pred (bounded i)

fromℕ≤-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i ℕ< m) → fromℕ≤ i<m ≡ i
fromℕ≤-toℕ zero    (s≤s z≤n)       = refl
fromℕ≤-toℕ (suc i) (s≤s (s≤s m≤n)) = cong suc (fromℕ≤-toℕ i (s≤s m≤n))

toℕ-fromℕ≤ : ∀ {m n} (m<n : m ℕ< n) → toℕ (fromℕ≤ m<n) ≡ m
toℕ-fromℕ≤ (s≤s z≤n)       = refl
toℕ-fromℕ≤ (s≤s (s≤s m<n)) = cong suc (toℕ-fromℕ≤ (s≤s m<n))

-- fromℕ is a special case of fromℕ≤.
fromℕ-def : ∀ n → fromℕ n ≡ fromℕ≤ ℕₚ.≤-refl
fromℕ-def zero    = refl
fromℕ-def (suc n) = cong suc (fromℕ-def n)

-- fromℕ≤ and fromℕ≤″ give the same result.
fromℕ≤≡fromℕ≤″ :
  ∀ {m n} (m<n : m ℕ< n) (m<″n : m ℕ.<″ n) →
  fromℕ≤ m<n ≡ fromℕ≤″ m m<″n
fromℕ≤≡fromℕ≤″ (s≤s z≤n)       (ℕ.less-than-or-equal refl) = refl
fromℕ≤≡fromℕ≤″ (s≤s (s≤s m<n)) (ℕ.less-than-or-equal refl) =
  cong suc (fromℕ≤≡fromℕ≤″ (s≤s m<n) (ℕ.less-than-or-equal refl))

------------------------------------------------------------------------
-- Properties of _≤_

≤-reflexive : ∀ {n} → _≡_ ⇒ (_≤_ {n})
≤-reflexive refl = ℕₚ.≤-refl

≤-refl : ∀ {n} → Reflexive (_≤_ {n})
≤-refl = ≤-reflexive refl

≤-trans : ∀ {n} → Transitive (_≤_ {n})
≤-trans = ℕₚ.≤-trans

≤-antisym : ∀ {n} → Antisymmetric _≡_ (_≤_ {n})
≤-antisym x≤y y≤x = toℕ-injective (ℕₚ.≤-antisym x≤y y≤x)

≤-total : ∀ {n} → Total (_≤_ {n})
≤-total x y = ℕₚ.≤-total (toℕ x) (toℕ y)

≤-isPreorder : ∀ {n} → IsPreorder _≡_ (_≤_ {n})
≤-isPreorder = record
  { isEquivalence = P.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : ∀ {n} → IsPartialOrder _≡_ (_≤_ {n})
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : ∀ {n} → IsTotalOrder _≡_ (_≤_ {n})
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-irrelevance : ∀ {n} → P.IrrelevantRel (_≤_ {n})
≤-irrelevance = ℕₚ.≤-irrelevance

≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

------------------------------------------------------------------------
-- Properties of _<_

<-irrefl : ∀ {n} → Irreflexive _≡_ (_<_ {n})
<-irrefl refl = ℕₚ.<-irrefl refl

<-asym : ∀ {n} → Asymmetric (_<_ {n})
<-asym = ℕₚ.<-asym

<-trans : ∀ {n} → Transitive (_<_ {n})
<-trans = ℕₚ.<-trans

<-cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
<-cmp zero    zero    = tri≈ (λ())     refl  (λ())
<-cmp zero    (suc j) = tri< (s≤s z≤n) (λ()) (λ())
<-cmp (suc i) zero    = tri> (λ())     (λ()) (s≤s z≤n)
<-cmp (suc i) (suc j) with <-cmp i j
... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)         (¬eq ∘ suc-injective) (¬gt ∘ ℕ.≤-pred)
... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ ℕ.≤-pred) (¬eq ∘ suc-injective) (s≤s gt)
... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ ℕ.≤-pred) (cong suc eq)    (¬gt ∘ ℕ.≤-pred)

<-isStrictTotalOrder : ∀ {n} → IsStrictTotalOrder _≡_ (_<_ {n})
<-isStrictTotalOrder = record
  { isEquivalence = P.isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictTotalOrder : ℕ → StrictTotalOrder _ _ _
<-strictTotalOrder n = record
  { Carrier            = Fin n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }

<-irrelevance : ∀ {n} → P.IrrelevantRel (_<_ {n})
<-irrelevance = ℕₚ.<-irrelevance

------------------------------------------------------------------------
-- Injection properties

-- Lemma:  n - i ≤ n.
nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ≤ n
nℕ-ℕi≤n n       zero     = ℕₚ.≤-refl
nℕ-ℕi≤n zero    (suc ())
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i  ≤⟨ nℕ-ℕi≤n n i ⟩
  n        ≤⟨ ℕₚ.n≤1+n n ⟩
  suc n    ∎
  where open ℕₚ.≤-Reasoning

inject-lemma : ∀ {n} {i : Fin n} (j : Fin′ i) →
               toℕ (inject j) ≡ toℕ j
inject-lemma {i = zero}  ()
inject-lemma {i = suc i} zero    = refl
inject-lemma {i = suc i} (suc j) = cong suc (inject-lemma j)

inject+-lemma : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (inject+ n i)
inject+-lemma n zero    = refl
inject+-lemma n (suc i) = cong suc (inject+-lemma n i)

inject₁-lemma : ∀ {m} (i : Fin m) → toℕ (inject₁ i) ≡ toℕ i
inject₁-lemma zero    = refl
inject₁-lemma (suc i) = cong suc (inject₁-lemma i)

inject≤-lemma : ∀ {m n} (i : Fin m) (le : m ℕ≤ n) →
                toℕ (inject≤ i le) ≡ toℕ i
inject≤-lemma zero    (s≤s le) = refl
inject≤-lemma (suc i) (s≤s le) = cong suc (inject≤-lemma i le)

-- Lemma:  inject≤ i n≤n ≡ i.
inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ≤ n) → inject≤ i n≤n ≡ i
inject≤-refl zero    (s≤s _  ) = refl
inject≤-refl (suc i) (s≤s n≤n) = cong suc (inject≤-refl i n≤n)

≺⇒<′ : _≺_ ⇒ ℕ._<′_
≺⇒<′ (n ≻toℕ i) = ℕₚ.≤⇒≤′ (bounded i)

<′⇒≺ : ℕ._<′_ ⇒ _≺_
<′⇒≺ {n} ℕ.≤′-refl    = subst (λ i → i ≺ suc n) (to-from n)
                              (suc n ≻toℕ fromℕ n)
<′⇒≺ (ℕ.≤′-step m≤′n) with <′⇒≺ m≤′n
<′⇒≺ (ℕ.≤′-step m≤′n) | n ≻toℕ i =
  subst (λ i → i ≺ suc n) (inject₁-lemma i) (suc n ≻toℕ (inject₁ i))

toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n ℕ+ toℕ i
toℕ-raise zero    i = refl
toℕ-raise (suc n) i = cong suc (toℕ-raise n i)

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (ℕ.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (ℕₚ.+-mono-≤ (prop-toℕ-≤ i) ℕₚ.≤-refl)

-- If there is an injection from a type to a finite set, then the type
-- has decidable equality.

eq? : ∀ {a n} {A : Set a} → A ↣ Fin n → Decidable {A = A} _≡_
eq? inj = Dec.via-injection inj _≟_

-- Quantification over finite sets commutes with applicative functors.

sequence : ∀ {p F n} {P : Pred (Fin n) p} → RawApplicative F →
           (∀ i → F (P i)) → F (∀ i → P i)
sequence {p} {F} RA = helper _ _
  where
  open RawApplicative RA

  helper : ∀ n (P : Fin n → Set p) → (∀ i → F (P i)) → F (∀ i → P i)
  helper zero    P ∀iPi = pure (λ())
  helper (suc n) P ∀iPi =
    combine <$> ∀iPi zero ⊛ helper n (P ∘ suc) (∀iPi ∘ suc)
    where
    combine : P zero → (∀ i → P (suc i)) → ∀ i → P i
    combine z s zero    = z
    combine z s (suc i) = s i

-- Included just to show that sequence above has an inverse (under
-- an equivalence relation with two equivalence classes, one with
-- all inhabited sets and the other with all uninhabited sets).

sequence⁻¹ : ∀ {p} {A : Set} {P : Pred A p} {F} →
             RawFunctor F → F (∀ i → P i) → ∀ i → F (P i)
sequence⁻¹ RF F∀iPi i = (λ f → f i) <$> F∀iPi
  where open RawFunctor RF

------------------------------------------------------------------------

punchOut-injective : ∀ {m} {i j k : Fin (suc m)}
                     (i≢j : i ≢ j) (i≢k : i ≢ k) →
                     punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-injective {_}     {zero}   {zero}  {_}     i≢j _   _     = ⊥-elim (i≢j refl)
punchOut-injective {_}     {zero}   {_}     {zero}  _   i≢k _     = ⊥-elim (i≢k refl)
punchOut-injective {_}     {zero}   {suc j} {suc k} _   _   pⱼ≡pₖ = cong suc pⱼ≡pₖ
punchOut-injective {zero}  {suc ()}
punchOut-injective {suc n} {suc i}  {zero}  {zero}  _   _    _    = refl
punchOut-injective {suc n} {suc i}  {zero}  {suc k} _   _   ()
punchOut-injective {suc n} {suc i}  {suc j} {zero}  _   _   ()
punchOut-injective {suc n} {suc i}  {suc j} {suc k} i≢j i≢k pⱼ≡pₖ =
  cong suc (punchOut-injective (i≢j ∘ cong suc) (i≢k ∘ cong suc) (suc-injective pⱼ≡pₖ))

punchIn-injective : ∀ {m} i (j k : Fin m) →
                    punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective zero    _       _       refl      = refl
punchIn-injective (suc i) zero    zero    _         = refl
punchIn-injective (suc i) zero    (suc k) ()
punchIn-injective (suc i) (suc j) zero    ()
punchIn-injective (suc i) (suc j) (suc k) ↑j+1≡↑k+1 =
  cong suc (punchIn-injective i j k (suc-injective ↑j+1≡↑k+1))

punchIn-punchOut : ∀ {m} {i j : Fin (suc m)} (i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut {_}     {zero}   {zero}  0≢0 = ⊥-elim (0≢0 refl)
punchIn-punchOut {_}     {zero}   {suc j} _   = refl
punchIn-punchOut {zero}  {suc ()}
punchIn-punchOut {suc m} {suc i}  {zero}  i≢j = refl
punchIn-punchOut {suc m} {suc i}  {suc j} i≢j =
  cong suc (punchIn-punchOut (i≢j ∘ cong suc))

punchInᵢ≢i : ∀ {m} i (j : Fin m) → punchIn i j ≢ i
punchInᵢ≢i zero    _    ()
punchInᵢ≢i (suc i) zero ()
punchInᵢ≢i (suc i) (suc j) = punchInᵢ≢i i j ∘ suc-injective

-- A version of 'cong' for 'punchOut' in which the inequality argument can be
-- changed out arbitrarily (reflecting the proof-irrelevance of that argument).

punchOut-cong : ∀ {n} (i : Fin (suc n)) {j k} {i≢j : i ≢ j} {i≢k : i ≢ k} → j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong zero {zero} {i≢j = i≢j} = ⊥-elim (i≢j refl)
punchOut-cong zero {suc j} {zero} {i≢k = i≢k} = ⊥-elim (i≢k refl)
punchOut-cong zero {suc j} {suc k} = suc-injective
punchOut-cong {zero} (suc ())
punchOut-cong {suc n} (suc i) {zero} {zero} _ = refl
punchOut-cong {suc n} (suc i) {zero} {suc k} ()
punchOut-cong {suc n} (suc i) {suc j} {zero} ()
punchOut-cong {suc n} (suc i) {suc j} {suc k} = cong suc ∘ punchOut-cong i ∘ suc-injective

-- An alternative to 'punchOut-cong' in the which the new inequality argument is
-- specific. Useful for enabling the omission of that argument during equational
-- reasoning.

punchOut-cong′ : ∀ {n} (i : Fin (suc n)) {j k} {p : i ≢ j} (q : j ≡ k) → punchOut p ≡ punchOut (p ∘ sym ∘ trans q ∘ sym)
punchOut-cong′ i q = punchOut-cong i q

punchOut-punchIn : ∀ {n} i {j : Fin n} → punchOut {i = i} {j = punchIn i j} (punchInᵢ≢i i j ∘ sym) ≡ j
punchOut-punchIn zero {j} = refl
punchOut-punchIn (suc i) {zero} = refl
punchOut-punchIn (suc i) {suc j} = cong suc (
  begin
    punchOut (punchInᵢ≢i i j ∘ suc-injective ∘ sym ∘ cong suc)  ≡⟨ punchOut-cong i refl ⟩
    punchOut (punchInᵢ≢i i j ∘ sym)                             ≡⟨ punchOut-punchIn i ⟩
    j                                                           ∎)
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

cmp              = <-cmp
strictTotalOrder = <-strictTotalOrder

open import Data.Fin public using (_≟_; _<?_)
