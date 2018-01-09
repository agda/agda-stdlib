------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Properties where

open import Algebra
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat as N using (ℕ; zero; suc; s≤s; z≤n; _∸_) renaming
  (_≤_ to _ℕ≤_
  ; _<_ to _ℕ<_
  ; _+_ to _ℕ+_)
import Data.Nat.Properties as N
open import Data.Product
open import Data.Bool using (if_then_else_)
open import Function
open import Function.Equality as FunS using (_⟨$⟩_)
open import Function.Injection using (_↣_)
open import Function.Inverse using (Inverse; _↔_)
open import Algebra.FunctionProperties
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; cong; subst)
open import Category.Functor
open import Category.Applicative

------------------------------------------------------------------------
-- Equality properties

infix 4 _≟_

suc-injective : ∀ {o} {m n : Fin o} → Fin.suc m ≡ suc n → m ≡ n
suc-injective refl = refl

_≟_ : {n : ℕ} → Decidable {A = Fin n} _≡_
zero  ≟ zero  = yes refl
zero  ≟ suc y = no λ()
suc x ≟ zero  = no λ()
suc x ≟ suc y with x ≟ y
... | yes x≡y = yes (cong suc x≡y)
... | no  x≢y = no (x≢y ∘ suc-injective)

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
  cong suc (toℕ-injective (cong N.pred eq))

bounded : ∀ {n} (i : Fin n) → toℕ i ℕ< n
bounded zero    = s≤s z≤n
bounded (suc i) = s≤s (bounded i)

prop-toℕ-≤ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ N.pred n
prop-toℕ-≤ zero                 = z≤n
prop-toℕ-≤ (suc {n = zero}  ())
prop-toℕ-≤ (suc {n = suc n} i)  = s≤s (prop-toℕ-≤ i)

-- A simpler implementation of prop-toℕ-≤,
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of prop-toℕ-≤,
-- it can be removed in favor of prop-toℕ-≤′.
prop-toℕ-≤′ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ N.pred n
prop-toℕ-≤′ i = N.<⇒≤pred (bounded i)

fromℕ≤-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i ℕ< m) → fromℕ≤ i<m ≡ i
fromℕ≤-toℕ zero    (s≤s z≤n)       = refl
fromℕ≤-toℕ (suc i) (s≤s (s≤s m≤n)) = cong suc (fromℕ≤-toℕ i (s≤s m≤n))

toℕ-fromℕ≤ : ∀ {m n} (m<n : m ℕ< n) → toℕ (fromℕ≤ m<n) ≡ m
toℕ-fromℕ≤ (s≤s z≤n)       = refl
toℕ-fromℕ≤ (s≤s (s≤s m<n)) = cong suc (toℕ-fromℕ≤ (s≤s m<n))

-- fromℕ is a special case of fromℕ≤.
fromℕ-def : ∀ n → fromℕ n ≡ fromℕ≤ N.≤-refl
fromℕ-def zero    = refl
fromℕ-def (suc n) = cong suc (fromℕ-def n)

-- fromℕ≤ and fromℕ≤″ give the same result.

fromℕ≤≡fromℕ≤″ :
  ∀ {m n} (m<n : m N.< n) (m<″n : m N.<″ n) →
  fromℕ≤ m<n ≡ fromℕ≤″ m m<″n
fromℕ≤≡fromℕ≤″ (s≤s z≤n)       (N.less-than-or-equal refl) = refl
fromℕ≤≡fromℕ≤″ (s≤s (s≤s m<n)) (N.less-than-or-equal refl) =
  cong suc (fromℕ≤≡fromℕ≤″ (s≤s m<n) (N.less-than-or-equal refl))

------------------------------------------------------------------------
-- Ordering properties

-- _≤_ ordering

≤-reflexive : ∀ {n} → _≡_ ⇒ (_≤_ {n})
≤-reflexive refl = N.≤-refl

≤-refl : ∀ {n} → Reflexive (_≤_ {n})
≤-refl = ≤-reflexive refl

≤-trans : ∀ {n} → Transitive (_≤_ {n})
≤-trans = N.≤-trans

≤-antisym : ∀ {n} → Antisymmetric _≡_ (_≤_ {n})
≤-antisym x≤y y≤x = toℕ-injective (N.≤-antisym x≤y y≤x)

≤-total : ∀ {n} → Total (_≤_ {n})
≤-total x y = N.≤-total (toℕ x) (toℕ y)

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

-- _<_ ordering

<-trans : ∀ {n} → Transitive (_<_ {n})
<-trans = N.<-trans

cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
cmp zero    zero    = tri≈ (λ())     refl  (λ())
cmp zero    (suc j) = tri< (s≤s z≤n) (λ()) (λ())
cmp (suc i) zero    = tri> (λ())     (λ()) (s≤s z≤n)
cmp (suc i) (suc j) with cmp i j
... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)         (¬eq ∘ suc-injective) (¬gt ∘ N.≤-pred)
... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ N.≤-pred) (¬eq ∘ suc-injective) (s≤s gt)
... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ N.≤-pred) (cong suc eq)    (¬gt ∘ N.≤-pred)

_<?_ : ∀ {n} → Decidable (_<_ {n})
m <? n = suc (toℕ m) N.≤? toℕ n

<-isStrictTotalOrder : ∀ {n} → IsStrictTotalOrder _≡_ (_<_ {n})
<-isStrictTotalOrder = record
  { isEquivalence = P.isEquivalence
  ; trans         = <-trans
  ; compare       = cmp
  }

strictTotalOrder : ℕ → StrictTotalOrder _ _ _
strictTotalOrder n = record
  { Carrier            = Fin n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- Injection properties

-- Lemma:  n - i ≤ n.
nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ≤ n
nℕ-ℕi≤n n       zero     = N.≤-refl
nℕ-ℕi≤n zero    (suc ())
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i  ≤⟨ nℕ-ℕi≤n n i ⟩
  n        ≤⟨ N.n≤1+n n ⟩
  suc n    ∎
  where open N.≤-Reasoning

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
inject≤-lemma zero    (N.s≤s le) = refl
inject≤-lemma (suc i) (N.s≤s le) = cong suc (inject≤-lemma i le)

-- Lemma:  inject≤ i n≤n ≡ i.
inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ≤ n) → inject≤ i n≤n ≡ i
inject≤-refl zero    (s≤s _  ) = refl
inject≤-refl (suc i) (s≤s n≤n) = cong suc (inject≤-refl i n≤n)

≺⇒<′ : _≺_ ⇒ N._<′_
≺⇒<′ (n ≻toℕ i) = N.≤⇒≤′ (bounded i)

<′⇒≺ : N._<′_ ⇒ _≺_
<′⇒≺ {n} N.≤′-refl    = subst (λ i → i ≺ suc n) (to-from n)
                              (suc n ≻toℕ fromℕ n)
<′⇒≺ (N.≤′-step m≤′n) with <′⇒≺ m≤′n
<′⇒≺ (N.≤′-step m≤′n) | n ≻toℕ i =
  subst (λ i → i ≺ suc n) (inject₁-lemma i) (suc n ≻toℕ (inject₁ i))

toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n ℕ+ toℕ i
toℕ-raise zero    i = refl
toℕ-raise (suc n) i = cong suc (toℕ-raise n i)

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (N.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (N.+-mono-≤ (prop-toℕ-≤ i) N.≤-refl)

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (N.n∸m≤n (toℕ i) (suc n))

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

reverse-involutive : ∀ {n} → Involutive _≡_ reverse
reverse-involutive {n} i = toℕ-injective (begin
  toℕ (reverse (reverse i))  ≡⟨ reverse-prop _ ⟩
  n ∸ suc (toℕ (reverse i))  ≡⟨ eq ⟩
  toℕ i                      ∎)
  where
  open P.≡-Reasoning

  lem₁ : ∀ m n → (m ℕ+ n) ∸ (m ℕ+ n ∸ m) ≡ m
  lem₁ m n = begin
    m ℕ+ n ∸ (m ℕ+ n ∸ m) ≡⟨ cong (λ ξ → m ℕ+ n ∸ (ξ ∸ m)) (N.+-comm m n) ⟩
    m ℕ+ n ∸ (n ℕ+ m ∸ m) ≡⟨ cong (λ ξ → m ℕ+ n ∸ ξ) (N.m+n∸n≡m n m) ⟩
    m ℕ+ n ∸ n            ≡⟨ N.m+n∸n≡m m n ⟩
    m                     ∎

  lem₂ : ∀ n → (i : Fin n) → n ∸ suc (n ∸ suc (toℕ i)) ≡ toℕ i
  lem₂ zero    ()
  lem₂ (suc n) i  = begin
    n ∸ (n ∸ toℕ i)                     ≡⟨ cong (λ ξ → ξ ∸ (ξ ∸ toℕ i)) i+j≡k ⟩
    (toℕ i ℕ+ j) ∸ (toℕ i ℕ+ j ∸ toℕ i) ≡⟨ lem₁ (toℕ i) j ⟩
    toℕ i                               ∎
    where
    decompose-n : ∃ λ j → n ≡ toℕ i ℕ+ j
    decompose-n = n ∸ toℕ i , P.sym (N.m+n∸m≡n (prop-toℕ-≤ i))

    j     = proj₁ decompose-n
    i+j≡k = proj₂ decompose-n

  eq : n ∸ suc (toℕ (reverse i)) ≡ toℕ i
  eq = begin
    n ∸ suc (toℕ (reverse i)) ≡⟨ cong (λ ξ → n ∸ suc ξ) (reverse-prop i) ⟩
    n ∸ suc (n ∸ suc (toℕ i)) ≡⟨ lem₂ n i ⟩
    toℕ i                     ∎

-- Lemma: reverse {suc n} (suc i) ≡ reverse n i  (in ℕ).

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

swapFin : ∀ {n} → Fin n → Fin n → Fin n → Fin n
swapFin i j k =
  if Dec.⌊ k ≟ i ⌋
  then j
  else (if Dec.⌊ k ≟ j ⌋
        then i
        else k)

if-dec-true : ∀ {a}{A : Set a} {n} (i j : Fin n) {x y : A} → i ≡ j → (if Dec.⌊ i ≟ j ⌋ then x else y) ≡ x
if-dec-true i j p with i ≟ j
... | yes _ = P.refl
... | no ¬p = ⊥-elim (¬p p)

if-dec-false : ∀ {a}{A : Set a} {n} (i j : Fin n) {x y : A} → ¬ (i ≡ j) → (if Dec.⌊ i ≟ j ⌋ then x else y) ≡ y
if-dec-false i j ¬p with i ≟ j
... | yes p = ⊥-elim (¬p p)
... | no _ = P.refl

private
  swap-lem₁ : ∀ {n} i (j : Fin n) → swapFin i j j ≡ i
  swap-lem₁ i j with j ≟ i
  swap-lem₁ i j | yes p = p
  swap-lem₁ i j | no ¬p = if-dec-true j j P.refl

  swap-lem₂ : ∀ {n} i (j : Fin n) → swapFin i j i ≡ j
  swap-lem₂ i j = if-dec-true i i P.refl

  swapFin-inverse : ∀ {n} (i j : Fin n) {k} → swapFin i j (swapFin j i k) ≡ k
  swapFin-inverse i j {k} with k ≟ j
  swapFin-inverse i j {.j} | yes P.refl = if-dec-true i i P.refl
  swapFin-inverse i j {k} | no ¬p with k ≟ i
  swapFin-inverse i j {k} | no ¬p | yes q =
    begin
      (if Dec.⌊ j ≟ i ⌋ then j else (if Dec.⌊ j ≟ j ⌋ then i else j))  ≡⟨ if-dec-false j i (¬p ∘ P.trans q ∘ P.sym) ⟩
      (if Dec.⌊ j ≟ j ⌋ then i else j)                                 ≡⟨ if-dec-true j j P.refl  ⟩
      i                                                                ≡⟨ P.sym q ⟩
      k                                                                ∎
    where open P.≡-Reasoning
  swapFin-inverse i j {k} | no ¬p | no ¬q =
    begin
      (if Dec.⌊ k ≟ i ⌋ then j else (if Dec.⌊ k ≟ j ⌋ then i else k))  ≡⟨ if-dec-false k i ¬q ⟩
      (if Dec.⌊ k ≟ j ⌋ then i else k)                                 ≡⟨ if-dec-false k j ¬p ⟩
      k                                                                ∎
    where open P.≡-Reasoning

-- A permuation that swaps the two given indices.

swapIndices : ∀ {n} → Fin n → Fin n → Fin n ↔ Fin n
swapIndices i j = record
  { to = P.→-to-⟶ (swapFin i j)
  ; from = P.→-to-⟶ (swapFin j i)
  ; inverse-of = record
    { left-inverse-of = λ _ → swapFin-inverse _ _
    ; right-inverse-of = λ _ → swapFin-inverse _ _
    }
  }

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
    πi : Fin (ℕ.suc n)
    πi = Inverse.to π ⟨$⟩ i

    open P.≡-Reasoning

    permute-≢ : ∀ {i j} → ¬ i ≡ j → (Inverse.to π ⟨$⟩ i) ≢ (Inverse.to π ⟨$⟩ j)
    permute-≢ p q = p (Inverse.injective π q)

    to-punchOut : ∀ {j : Fin m} → πi ≢ (Inverse.to π ⟨$⟩ punchIn i j)
    to-punchOut = permute-≢ (punchInᵢ≢i _ _) ∘ P.sym

    from-punchOut : ∀ {j : Fin n} → i ≢ (Inverse.from π ⟨$⟩ punchIn πi j)
    from-punchOut {j} p = punchInᵢ≢i πi j (
      begin
        punchIn πi j                                        ≡⟨ P.sym (Inverse.right-inverse-of π _) ⟩
        Inverse.to π ⟨$⟩ (Inverse.from π ⟨$⟩ punchIn πi j)  ≡⟨ P.cong (Inverse.to π ⟨$⟩_) (P.sym p) ⟩
        πi                                                  ∎)

    to : Fin m → Fin n
    to j = punchOut to-punchOut

    from : Fin n → Fin m
    from j = punchOut {i = i} {Inverse.from π ⟨$⟩ punchIn πi j} from-punchOut

    left-inverse-of : ∀ j → from (to j) ≡ j
    left-inverse-of j =
      begin
        from (to j)                                                                ≡⟨⟩
        punchOut {i = i} {Inverse.from π ⟨$⟩ punchIn πi (punchOut to-punchOut)} _  ≡⟨ punchOut-cong′ i (P.cong (Inverse.from π ⟨$⟩_) (punchIn-punchOut {i = πi} _)) ⟩
        punchOut {i = i} {Inverse.from π ⟨$⟩ (Inverse.to π ⟨$⟩ punchIn i j)}    _  ≡⟨ punchOut-cong′ i (Inverse.left-inverse-of π _) ⟩
        punchOut {i = i} {punchIn i j}                                          _  ≡⟨ punchOut-punchIn {i = i} _ ⟩
        j                                                                          ∎

    right-inverse-of : ∀ j → to (from j) ≡ j
    right-inverse-of j =
      begin
        to (from j)                                                                ≡⟨⟩
        punchOut {i = πi} {Inverse.to π ⟨$⟩ punchIn i (punchOut from-punchOut)} _  ≡⟨ punchOut-cong′ πi (P.cong (Inverse.to π ⟨$⟩_) (punchIn-punchOut {i = i} _)) ⟩
        punchOut {i = πi} {Inverse.to π ⟨$⟩ (Inverse.from π ⟨$⟩ punchIn πi j)}  _  ≡⟨ punchOut-cong′ πi (Inverse.right-inverse-of π _) ⟩
        punchOut {i = πi} {punchIn πi j}                                        _  ≡⟨ punchOut-punchIn {i = πi} _ ⟩
        j                                                                          ∎

punchIn-permute :
  ∀ {n} (π : Fin (ℕ.suc n) ↔ Fin (ℕ.suc n)) i (j : Fin n)
  → Inverse.to π ⟨$⟩ (punchIn i j) ≡
    punchIn (Inverse.to π ⟨$⟩ i) (Inverse.to (removeIn↔ i π) ⟨$⟩ j)
punchIn-permute π i j =
  begin
    Inverse.to π ⟨$⟩ (punchIn i j)                                       ≡⟨ P.sym (punchIn-punchOut {i = πi} _) ⟩
    punchIn πi (punchOut {i = πi} {Inverse.to π ⟨$⟩ (punchIn i j)} lem)  ≡⟨⟩
    punchIn πi (Inverse.to (removeIn↔ i π) ⟨$⟩ j)                        ∎
  where
    open P.≡-Reasoning

    πi = Inverse.to π ⟨$⟩ i

    lem : ¬ πi ≡ Inverse.to π ⟨$⟩ punchIn i j
    lem p = punchInᵢ≢i i j (Inverse.injective π (P.sym p))

punchIn-permute′ :
  ∀ {n} π i (j : Fin n)
  → Inverse.to π ⟨$⟩ (punchIn (Inverse.from π ⟨$⟩ i) j) ≡
    punchIn i (Inverse.to (removeIn↔ (Inverse.from π ⟨$⟩ i) π) ⟨$⟩ j)
punchIn-permute′ π i j =
  begin
    Inverse.to π ⟨$⟩ (punchIn (Inverse.from π ⟨$⟩ i) j)                                                         ≡⟨ punchIn-permute π _ _ ⟩
    punchIn (Inverse.to π ⟨$⟩ (Inverse.from π ⟨$⟩ i)) (Inverse.to (removeIn↔ (Inverse.from π ⟨$⟩ i) π) ⟨$⟩ j)   ≡⟨ P.cong₂ punchIn (Inverse.right-inverse-of π i) P.refl ⟩
    punchIn i (Inverse.to (removeIn↔ (Inverse.from π ⟨$⟩ i) π) ⟨$⟩ j)                                           ∎
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
