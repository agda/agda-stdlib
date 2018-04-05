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
open import Data.Product hiding (swap)
open import Data.Bool using (true; false; if_then_else_)
open import Function
open import Function.Equality as FunS using (_⟨$⟩_)
open import Function.Injection using (_↣_)
open import Function.Inverse using (Inverse; _↔_)
open import Algebra.FunctionProperties
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec using (⌊_⌋)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; cong; subst)
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

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (ℕₚ.n∸m≤n (toℕ i) (suc n))

reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
reverse-prop {zero} ()
reverse-prop {suc n} i = begin
  toℕ (inject≤ (n ℕ- i) _)  ≡⟨ inject≤-lemma _ _ ⟩
  toℕ (n ℕ- i)              ≡⟨ toℕ‿ℕ- n i ⟩
  n ∸ toℕ i                 ∎
  where
  open P.≡-Reasoning

  toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
  toℕ‿ℕ- n       zero     = to-from n
  toℕ‿ℕ- zero    (suc ())
  toℕ‿ℕ- (suc n) (suc i)  = toℕ‿ℕ- n i

reverse-involutive : ∀ {n} → Involutive _≡_ (reverse {n})
reverse-involutive {zero}  ()
reverse-involutive {suc n} i = toℕ-injective (begin
  toℕ (reverse (reverse i)) ≡⟨ reverse-prop (reverse i) ⟩
  n ∸ (toℕ (reverse i))     ≡⟨ P.cong (n ∸_) (reverse-prop i) ⟩
  n ∸ (n ∸ (toℕ i))         ≡⟨ ℕₚ.m∸[m∸n]≡n (ℕ.≤-pred (bounded i)) ⟩
  toℕ i                     ∎)
  where open P.≡-Reasoning

reverse-suc : ∀{n}{i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
reverse-suc {n}{i} = begin
  toℕ (reverse (suc i))      ≡⟨ reverse-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ P.sym (reverse-prop i) ⟩
  toℕ (reverse i)            ∎
  where
  open P.≡-Reasoning

-- If there is an injection from a type to a finite set, then the type
-- has decidable equality.

eq? : ∀ {a n} {A : Set a} → A ↣ Fin n → Decidable {A = A} _≡_
eq? inj = Dec.via-injection inj _≟_

-- Quantification over finite sets commutes with applicative functors.

sequence : ∀ {F n} {P : Fin n → Set} → RawApplicative F →
           (∀ i → F (P i)) → F (∀ i → P i)
sequence {F} RA = helper _ _
  where
  open RawApplicative RA

  helper : ∀ n (P : Fin n → Set) → (∀ i → F (P i)) → F (∀ i → P i)
  helper zero    P ∀iPi = pure (λ())
  helper (suc n) P ∀iPi =
    combine <$> ∀iPi zero ⊛ helper n (λ n → P (suc n)) (∀iPi ∘ suc)
    where
    combine : P zero → (∀ i → P (suc i)) → ∀ i → P i
    combine z s zero    = z
    combine z s (suc i) = s i

private

  -- Included just to show that sequence above has an inverse (under
  -- an equivalence relation with two equivalence classes, one with
  -- all inhabited sets and the other with all uninhabited sets).

  sequence⁻¹ : ∀ {F}{A} {P : A → Set} → RawFunctor F →
               F (∀ i → P i) → ∀ i → F (P i)
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

punchOut-punchIn : ∀ {n} {i} {j : Fin n} (p : ¬ i ≡ punchIn i j) → punchOut p ≡ j
punchOut-punchIn {i = zero} p = refl
punchOut-punchIn {i = suc i} {zero} p = refl
punchOut-punchIn {i = suc i} {suc j} p = cong suc (punchOut-punchIn (p ∘ cong suc))

punchInᵢ≢i : ∀ {m} i (j : Fin m) → punchIn i j ≢ i
punchInᵢ≢i zero    _    ()
punchInᵢ≢i (suc i) zero ()
punchInᵢ≢i (suc i) (suc j) = punchInᵢ≢i i j ∘ suc-injective

-- A version of 'cong' for 'punchOut' in which the inequality argument can be
-- changed out arbitrarily (reflecting the proof-irrelevance of that argument).

punchOut-cong : ∀ {n} (i : Fin (ℕ.suc n)) {j k} {i≢j : i ≢ j} {i≢k : i ≢ k} → j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong zero {zero} {i≢j = i≢j} = ⊥-elim (i≢j refl)
punchOut-cong zero {suc j} {zero} {i≢k = i≢k} = ⊥-elim (i≢k refl)
punchOut-cong zero {suc j} {suc k} = suc-injective
punchOut-cong {ℕ.zero} (suc ())
punchOut-cong {ℕ.suc n} (suc i) {zero} {zero} _ = refl
punchOut-cong {ℕ.suc n} (suc i) {zero} {suc k} ()
punchOut-cong {ℕ.suc n} (suc i) {suc j} {zero} ()
punchOut-cong {ℕ.suc n} (suc i) {suc j} {suc k} = cong suc ∘ punchOut-cong i ∘ suc-injective

-- An alternative to 'punchOut-cong' in the which the new inequality argument is
-- specific. Useful for enabling the omission of that argument during equational
-- reasoning.

punchOut-cong′ : ∀ {n} (i : Fin (ℕ.suc n)) {j k} {p : ¬ i ≡ j} (q : j ≡ k) → punchOut p ≡ punchOut (p ∘ P.sym ∘ P.trans q ∘ P.sym)
punchOut-cong′ i q = punchOut-cong i q

--------------------------------------------------------------------------------
--  Bijections on finite sets
--------------------------------------------------------------------------------

-- A permuation that swaps the two given indices.

swap-perm : ∀ {n} → Fin n → Fin n → Fin n ↔ Fin n
swap-perm {n} i j = record
  { to = P.→-to-⟶ (swap i j)
  ; from = P.→-to-⟶ (swap j i)
  ; inverse-of = record
    { left-inverse-of = λ _ → swap-inverse _ _
    ; right-inverse-of = λ _ → swap-inverse _ _
    }
  }
  where
  swap-inverse : ∀ (i j : Fin n) {k} → swap i j (swap j i k) ≡ k
  swap-inverse i j {k} with k ≟ j
  swap-inverse i j {k} | yes p with i ≟ i
  swap-inverse i j {k} | yes p | yes q = P.sym p
  swap-inverse i j {k} | yes p | no ¬q = ⊥-elim (¬q refl)
  swap-inverse i j {k} | no ¬p with k ≟ i
  swap-inverse i j {k} | no ¬p | yes q with j ≟ i
  swap-inverse i j {k} | no ¬p | yes q | yes r = ⊥-elim (¬p (P.trans q (P.sym r)))
  swap-inverse i j {k} | no ¬p | yes q | no ¬r with j ≟ j
  swap-inverse i j {k} | no ¬p | yes q | no ¬r | yes _ = P.sym q
  swap-inverse i j {k} | no ¬p | yes q | no ¬r | no ¬s = ⊥-elim (¬s refl)
  swap-inverse i j {k} | no ¬p | no ¬q with k ≟ i
  swap-inverse i j {k} | no ¬p | no ¬q | yes q = ⊥-elim (¬q q)
  swap-inverse i j {k} | no ¬p | no ¬q | no _ with k ≟ j
  swap-inverse i j {k} | no ¬p | no ¬q | no _ | yes p = ⊥-elim (¬p p)
  swap-inverse i j {k} | no ¬p | no ¬q | no _ | no _ = refl


-- Given a permutation
--
-- [0 ↦ i₀, …, k ↦ iₖ, …, n ↦ iₙ]
--
-- yields a permutation
--
-- [0 ↦ i₀, …, k-1 ↦ i_{k-1}, k ↦ i_{k+1}, k+1 ↦ i_{k+2}, …, n-1 ↦ iₙ]
--
-- Intuitively, 'removeIn↔ k π' removes the element at index 'k' from the
-- permutation 'π'.

removeIn↔ : ∀ {m n} (i : Fin (ℕ.suc m)) → Fin (ℕ.suc m) ↔ Fin (ℕ.suc n) → Fin m ↔ Fin n
removeIn↔ {m}{n} i π = record
  { to = P.→-to-⟶ to
  ; from = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = left-inverse-of
    ; right-inverse-of = right-inverse-of
    }
  }
  where
    πR = Inverse.to π ⟨$⟩_
    πL = Inverse.from π ⟨$⟩_

    πi : Fin (ℕ.suc n)
    πi = πR i

    open P.≡-Reasoning

    permute-≢ : ∀ {i j} → ¬ i ≡ j → πR i ≢ πR j
    permute-≢ p q = p (Inverse.injective π q)

    to-punchOut : ∀ {j : Fin m} → πi ≢ πR (punchIn i j)
    to-punchOut = permute-≢ (punchInᵢ≢i _ _) ∘ P.sym

    from-punchOut : ∀ {j : Fin n} → i ≢ πL (punchIn πi j)
    from-punchOut {j} p = punchInᵢ≢i πi j (
      begin
        punchIn πi j            ≡⟨ P.sym (Inverse.right-inverse-of π _) ⟩
        πR (πL (punchIn πi j))  ≡⟨ P.cong πR (P.sym p) ⟩
        πi                      ∎)

    to : Fin m → Fin n
    to j = punchOut to-punchOut

    from : Fin n → Fin m
    from j = punchOut {i = i} {πL (punchIn πi j)} from-punchOut

    left-inverse-of : ∀ j → from (to j) ≡ j
    left-inverse-of j =
      begin
        from (to j)                                                  ≡⟨⟩
        punchOut {i = i} {πL (punchIn πi (punchOut to-punchOut))} _  ≡⟨ punchOut-cong′ i (P.cong πL (punchIn-punchOut {i = πi} _)) ⟩
        punchOut {i = i} {πL (πR (punchIn i j))}                  _  ≡⟨ punchOut-cong′ i (Inverse.left-inverse-of π _) ⟩
        punchOut {i = i} {punchIn i j}                            _  ≡⟨ punchOut-punchIn {i = i} _ ⟩
        j                                                            ∎

    right-inverse-of : ∀ j → to (from j) ≡ j
    right-inverse-of j =
      begin
        to (from j)                                                    ≡⟨⟩
        punchOut {i = πi} {πR (punchIn i (punchOut from-punchOut))} _  ≡⟨ punchOut-cong′ πi (P.cong πR (punchIn-punchOut {i = i} _)) ⟩
        punchOut {i = πi} {πR (πL (punchIn πi j))}                  _  ≡⟨ punchOut-cong′ πi (Inverse.right-inverse-of π _) ⟩
        punchOut {i = πi} {punchIn πi j}                            _  ≡⟨ punchOut-punchIn {i = πi} _ ⟩
        j                                                              ∎

module _ {n} (π : Fin (ℕ.suc n) ↔ Fin (ℕ.suc n)) where
  private
    πR = Inverse.to π ⟨$⟩_
    πL = Inverse.from π ⟨$⟩_

  punchIn-permute :
    ∀ i (j : Fin n)
    → πR (punchIn i j) ≡ punchIn (πR i) (Inverse.to (removeIn↔ i π) ⟨$⟩ j)
  punchIn-permute i j =
    begin
      πR (punchIn i j)                                       ≡⟨ P.sym (punchIn-punchOut {i = πi} _) ⟩
      punchIn πi (punchOut {i = πi} {πR (punchIn i j)} lem)  ≡⟨⟩
      punchIn πi (Inverse.to (removeIn↔ i π) ⟨$⟩ j)          ∎
    where
      open P.≡-Reasoning

      πi = πR i

      lem : ¬ πi ≡ πR (punchIn i j)
      lem p = punchInᵢ≢i i j (Inverse.injective π (P.sym p))

  punchIn-permute′ :
    ∀ i (j : Fin n)
    → πR (punchIn (πL i) j) ≡
      punchIn i (Inverse.to (removeIn↔ (πL i) π) ⟨$⟩ j)
  punchIn-permute′ i j =
    begin
      πR (punchIn (πL i) j)                                         ≡⟨ punchIn-permute _ _ ⟩
      punchIn (πR (πL i)) (Inverse.to (removeIn↔ (πL i) π) ⟨$⟩ j)   ≡⟨ P.cong₂ punchIn (Inverse.right-inverse-of π i) P.refl ⟩
      punchIn i (Inverse.to (removeIn↔ (πL i) π) ⟨$⟩ j)             ∎
    where
      open P.≡-Reasoning

-- If there is a bijection between finite sets of size 'm' and 'n', then
-- 'm' = 'n'.

↔-≡ : ∀ {m n} → Fin m ↔ Fin n → m ≡ n
↔-≡ {ℕ.zero} {ℕ.zero} p = P.refl
↔-≡ {ℕ.zero} {ℕ.suc n} p with Inverse.from p ⟨$⟩ zero
↔-≡ {ℕ.zero} {ℕ.suc n} p | ()
↔-≡ {ℕ.suc m} {ℕ.zero} p with Inverse.to p ⟨$⟩ zero
↔-≡ {ℕ.suc m} {ℕ.zero} p | ()
↔-≡ {ℕ.suc m} {ℕ.suc n} p = P.cong ℕ.suc (↔-≡ (removeIn↔ zero p))

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

cmp              = <-cmp
strictTotalOrder = <-strictTotalOrder

open import Data.Fin public using (_≟_; _<?_)
