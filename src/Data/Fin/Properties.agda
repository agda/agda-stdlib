------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Properties where

open import Algebra.FunctionProperties using (Involutive)
open import Category.Applicative using (RawApplicative)
open import Category.Functor using (RawFunctor)
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s; z≤n; _∸_)
  renaming
  ( _≤_ to _ℕ≤_
  ; _<_ to _ℕ<_
  ; _+_ to _ℕ+_
  )
import Data.Nat.Properties as ℕₚ
open import Data.Unit using (tt)
open import Data.Product using (∃; ∃₂; ∄; _×_; _,_; map; proj₁)
open import Function using (_∘_; id)
open import Function.Injection using (_↣_)
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Unary as U using (U; Pred; Decidable; _⊆_)
open import Relation.Unary.Properties using (U?)

------------------------------------------------------------------------
-- Fin

¬Fin0 : ¬ Fin 0
¬Fin0 ()

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
-- toℕ

toℕ-injective : ∀ {n} {i j : Fin n} → toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {zero}  {}      {}      _
toℕ-injective {suc n} {zero}  {zero}  eq = refl
toℕ-injective {suc n} {zero}  {suc j} ()
toℕ-injective {suc n} {suc i} {zero}  ()
toℕ-injective {suc n} {suc i} {suc j} eq =
  cong suc (toℕ-injective (cong ℕ.pred eq))

toℕ-strengthen : ∀ {n} (i : Fin n) → toℕ (strengthen i) ≡ toℕ i
toℕ-strengthen zero    = refl
toℕ-strengthen (suc i) = cong suc (toℕ-strengthen i)

toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n ℕ+ toℕ i
toℕ-raise zero    i = refl
toℕ-raise (suc n) i = cong suc (toℕ-raise n i)

toℕ<n : ∀ {n} (i : Fin n) → toℕ i ℕ< n
toℕ<n zero    = s≤s z≤n
toℕ<n (suc i) = s≤s (toℕ<n i)

toℕ≤pred[n] : ∀ {n} (i : Fin n) → toℕ i ℕ≤ ℕ.pred n
toℕ≤pred[n] zero                 = z≤n
toℕ≤pred[n] (suc {n = zero}  ())
toℕ≤pred[n] (suc {n = suc n} i)  = s≤s (toℕ≤pred[n] i)

-- A simpler implementation of toℕ≤pred[n],
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of toℕ≤pred[n],
-- it can be removed in favor of toℕ≤pred[n]′.
toℕ≤pred[n]′ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ ℕ.pred n
toℕ≤pred[n]′ i = ℕₚ.<⇒≤pred (toℕ<n i)

------------------------------------------------------------------------
-- fromℕ

toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = cong suc (toℕ-fromℕ n)

fromℕ-toℕ : ∀ {n} (i : Fin n) → fromℕ (toℕ i) ≡ strengthen i
fromℕ-toℕ zero    = refl
fromℕ-toℕ (suc i) = cong suc (fromℕ-toℕ i)

------------------------------------------------------------------------
-- fromℕ≤

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

------------------------------------------------------------------------
-- fromℕ≤″

fromℕ≤≡fromℕ≤″ : ∀ {m n} (m<n : m ℕ< n) (m<″n : m ℕ.<″ n) →
                  fromℕ≤ m<n ≡ fromℕ≤″ m m<″n
fromℕ≤≡fromℕ≤″ (s≤s z≤n)       (ℕ.less-than-or-equal refl) = refl
fromℕ≤≡fromℕ≤″ (s≤s (s≤s m<n)) (ℕ.less-than-or-equal refl) =
  cong suc (fromℕ≤≡fromℕ≤″ (s≤s m<n) (ℕ.less-than-or-equal refl))

toℕ-fromℕ≤″ : ∀ {m n} (m<n : m ℕ.<″ n) → toℕ (fromℕ≤″ m m<n) ≡ m
toℕ-fromℕ≤″ {m} {n} m<n = begin
  toℕ (fromℕ≤″ m m<n)  ≡⟨ cong toℕ (sym (fromℕ≤≡fromℕ≤″ _ m<n)) ⟩
  toℕ (fromℕ≤ _)       ≡⟨ toℕ-fromℕ≤ (ℕₚ.≤″⇒≤ m<n) ⟩
  m ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _≤_

-- Relational properties
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

≤-preorder : ℕ → Preorder _ _ _
≤-preorder n = record
  { isPreorder = ≤-isPreorder {n}
  }

≤-isPartialOrder : ∀ {n} → IsPartialOrder _≡_ (_≤_ {n})
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-poset : ℕ → Poset _ _ _
≤-poset n = record
  { isPartialOrder = ≤-isPartialOrder {n}
  }

≤-isTotalOrder : ∀ {n} → IsTotalOrder _≡_ (_≤_ {n})
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-totalOrder : ℕ → TotalOrder _ _ _
≤-totalOrder n = record
  { isTotalOrder = ≤-isTotalOrder {n}
  }

≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

≤-decTotalOrder : ℕ → DecTotalOrder _ _ _
≤-decTotalOrder n = record
  { isDecTotalOrder = ≤-isDecTotalOrder {n}
  }

-- Other properties
≤-irrelevance : ∀ {n} → Irrelevant (_≤_ {n})
≤-irrelevance = ℕₚ.≤-irrelevance

------------------------------------------------------------------------
-- Properties of _<_

-- Relational properties
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
... | tri< i<j i≢j j≮i = tri< (s≤s i<j)         (i≢j ∘ suc-injective) (j≮i ∘ ℕ.≤-pred)
... | tri> i≮j i≢j j<i = tri> (i≮j ∘ ℕ.≤-pred) (i≢j ∘ suc-injective) (s≤s j<i)
... | tri≈ i≮j i≡j j≮i = tri≈ (i≮j ∘ ℕ.≤-pred) (cong suc i≡j)        (j≮i ∘ ℕ.≤-pred)

<-respˡ-≡ : ∀ {n} → (_<_ {n}) Respectsˡ _≡_
<-respˡ-≡ refl x≤y = x≤y

<-respʳ-≡ : ∀ {n} → (_<_ {n}) Respectsʳ _≡_
<-respʳ-≡ refl x≤y = x≤y

<-resp₂-≡ : ∀ {n} → (_<_ {n}) Respects₂ _≡_
<-resp₂-≡ = <-respʳ-≡ , <-respˡ-≡

<-isStrictPartialOrder : ∀ {n} → IsStrictPartialOrder _≡_ (_<_ {n})
<-isStrictPartialOrder = record
  { isEquivalence = P.isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp₂-≡
  }

<-strictPartialOrder : ℕ → StrictPartialOrder _ _ _
<-strictPartialOrder n = record
  { isStrictPartialOrder = <-isStrictPartialOrder {n}
  }

<-isStrictTotalOrder : ∀ {n} → IsStrictTotalOrder _≡_ (_<_ {n})
<-isStrictTotalOrder = record
  { isEquivalence = P.isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictTotalOrder : ℕ → StrictTotalOrder _ _ _
<-strictTotalOrder n = record
  { isStrictTotalOrder = <-isStrictTotalOrder {n}
  }

-- Other properties
<-irrelevance : ∀ {n} → Irrelevant (_<_ {n})
<-irrelevance = ℕₚ.<-irrelevance

<⇒≢ : ∀ {n} {i j : Fin n} → i < j → i ≢ j
<⇒≢ i<i refl = ℕₚ.n≮n _ i<i

≤+≢⇒< : ∀ {n} {i j : Fin n} → i ≤ j → i ≢ j → i < j
≤+≢⇒< {i = zero}  {zero}  _         0≢0     = contradiction refl 0≢0
≤+≢⇒< {i = zero}  {suc j} _         _       = s≤s z≤n
≤+≢⇒< {i = suc i} {zero}  ()
≤+≢⇒< {i = suc i} {suc j} (s≤s i≤j) 1+i≢1+j =
  s≤s (≤+≢⇒< i≤j (1+i≢1+j ∘ (cong suc)))

------------------------------------------------------------------------
-- inject

toℕ-inject : ∀ {n} {i : Fin n} (j : Fin′ i) →
               toℕ (inject j) ≡ toℕ j
toℕ-inject {i = zero}  ()
toℕ-inject {i = suc i} zero    = refl
toℕ-inject {i = suc i} (suc j) = cong suc (toℕ-inject j)

------------------------------------------------------------------------
-- inject+

toℕ-inject+ : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (inject+ n i)
toℕ-inject+ n zero    = refl
toℕ-inject+ n (suc i) = cong suc (toℕ-inject+ n i)

------------------------------------------------------------------------
-- inject₁

inject₁-injective : ∀ {n} {i j : Fin n} → inject₁ i ≡ inject₁ j → i ≡ j
inject₁-injective {i = zero}  {zero}  i≡j = refl
inject₁-injective {i = zero}  {suc j} ()
inject₁-injective {i = suc i} {zero}  ()
inject₁-injective {i = suc i} {suc j} i≡j =
  cong suc (inject₁-injective (suc-injective i≡j))

toℕ-inject₁ : ∀ {n} (i : Fin n) → toℕ (inject₁ i) ≡ toℕ i
toℕ-inject₁ zero    = refl
toℕ-inject₁ (suc i) = cong suc (toℕ-inject₁ i)

------------------------------------------------------------------------
-- inject≤

toℕ-inject≤ : ∀ {m n} (i : Fin m) (le : m ℕ≤ n) →
                toℕ (inject≤ i le) ≡ toℕ i
toℕ-inject≤ zero    (s≤s le) = refl
toℕ-inject≤ (suc i) (s≤s le) = cong suc (toℕ-inject≤ i le)

inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ≤ n) → inject≤ i n≤n ≡ i
inject≤-refl zero    (s≤s _  ) = refl
inject≤-refl (suc i) (s≤s n≤n) = cong suc (inject≤-refl i n≤n)

------------------------------------------------------------------------
-- _≺_

≺⇒<′ : _≺_ ⇒ ℕ._<′_
≺⇒<′ (n ≻toℕ i) = ℕₚ.≤⇒≤′ (toℕ<n i)

<′⇒≺ : ℕ._<′_ ⇒ _≺_
<′⇒≺ {n} ℕ.≤′-refl = subst (_≺ suc n) (toℕ-fromℕ n)
                              (suc n ≻toℕ fromℕ n)
<′⇒≺ (ℕ.≤′-step m≤′n) with <′⇒≺ m≤′n
... | n ≻toℕ i = subst (_≺ suc n) (toℕ-inject₁ i) (suc n ≻toℕ _)

------------------------------------------------------------------------
-- pred

<⇒≤pred : ∀ {n} {i j : Fin n} → j < i → j ≤ pred i
<⇒≤pred {i = zero}  {_}     ()
<⇒≤pred {i = suc i} {zero}  j<i       = z≤n
<⇒≤pred {i = suc i} {suc j} (s≤s j<i) =
  subst (_ ℕ≤_) (sym (toℕ-inject₁ i)) j<i

------------------------------------------------------------------------
-- ℕ-

toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
toℕ‿ℕ- n       zero     = toℕ-fromℕ n
toℕ‿ℕ- zero    (suc ())
toℕ‿ℕ- (suc n) (suc i)  = toℕ‿ℕ- n i

------------------------------------------------------------------------
-- ℕ-ℕ

nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ≤ n
nℕ-ℕi≤n n       zero     = ℕₚ.≤-refl
nℕ-ℕi≤n zero    (suc ())
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i  ≤⟨ nℕ-ℕi≤n n i ⟩
  n        ≤⟨ ℕₚ.n≤1+n n ⟩
  suc n    ∎
  where open ℕₚ.≤-Reasoning

------------------------------------------------------------------------
-- punchIn

punchIn-injective : ∀ {m} i (j k : Fin m) →
                    punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective zero    _       _       refl      = refl
punchIn-injective (suc i) zero    zero    _         = refl
punchIn-injective (suc i) zero    (suc k) ()
punchIn-injective (suc i) (suc j) zero    ()
punchIn-injective (suc i) (suc j) (suc k) ↑j+1≡↑k+1 =
  cong suc (punchIn-injective i j k (suc-injective ↑j+1≡↑k+1))

punchInᵢ≢i : ∀ {m} i (j : Fin m) → punchIn i j ≢ i
punchInᵢ≢i zero    _    ()
punchInᵢ≢i (suc i) zero ()
punchInᵢ≢i (suc i) (suc j) = punchInᵢ≢i i j ∘ suc-injective

------------------------------------------------------------------------
-- punchOut

-- A version of 'cong' for 'punchOut' in which the inequality argument can be
-- changed out arbitrarily (reflecting the proof-irrelevance of that argument).

punchOut-cong : ∀ {n} (i : Fin (suc n)) {j k} {i≢j : i ≢ j} {i≢k : i ≢ k} → j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong zero {zero} {i≢j = 0≢0} = contradiction refl 0≢0
punchOut-cong zero {suc j} {zero} {i≢k = 0≢0} = contradiction refl 0≢0
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

punchOut-injective : ∀ {m} {i j k : Fin (suc m)}
                     (i≢j : i ≢ j) (i≢k : i ≢ k) →
                     punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-injective {_}     {zero}   {zero}  {_}     0≢0 _   _     = contradiction refl 0≢0
punchOut-injective {_}     {zero}   {_}     {zero}  _   0≢0 _     = contradiction refl 0≢0
punchOut-injective {_}     {zero}   {suc j} {suc k} _   _   pⱼ≡pₖ = cong suc pⱼ≡pₖ
punchOut-injective {zero}  {suc ()}
punchOut-injective {suc n} {suc i}  {zero}  {zero}  _   _    _    = refl
punchOut-injective {suc n} {suc i}  {zero}  {suc k} _   _   ()
punchOut-injective {suc n} {suc i}  {suc j} {zero}  _   _   ()
punchOut-injective {suc n} {suc i}  {suc j} {suc k} i≢j i≢k pⱼ≡pₖ =
  cong suc (punchOut-injective (i≢j ∘ cong suc) (i≢k ∘ cong suc) (suc-injective pⱼ≡pₖ))

punchIn-punchOut : ∀ {m} {i j : Fin (suc m)} (i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut {_}     {zero}   {zero}  0≢0 = contradiction refl 0≢0
punchIn-punchOut {_}     {zero}   {suc j} _   = refl
punchIn-punchOut {zero}  {suc ()}
punchIn-punchOut {suc m} {suc i}  {zero}  i≢j = refl
punchIn-punchOut {suc m} {suc i}  {suc j} i≢j =
  cong suc (punchIn-punchOut (i≢j ∘ cong suc))

punchOut-punchIn : ∀ {n} i {j : Fin n} → punchOut {i = i} {j = punchIn i j} (punchInᵢ≢i i j ∘ sym) ≡ j
punchOut-punchIn zero {j} = refl
punchOut-punchIn (suc i) {zero} = refl
punchOut-punchIn (suc i) {suc j} = cong suc (begin
  punchOut (punchInᵢ≢i i j ∘ suc-injective ∘ sym ∘ cong suc)  ≡⟨ punchOut-cong i refl ⟩
  punchOut (punchInᵢ≢i i j ∘ sym)                             ≡⟨ punchOut-punchIn i ⟩
  j                                                           ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- _+′_

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (ℕ.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (ℕₚ.+-mono-≤ (toℕ≤pred[n] i) ℕₚ.≤-refl)

------------------------------------------------------------------------
-- Quantification

∀-cons : ∀ {n p} {P : Pred (Fin (suc n)) p} →
         P zero → (∀ i → P (suc i)) → (∀ i → P i)
∀-cons z s zero    = z
∀-cons z s (suc i) = s i

decFinSubset : ∀ {n p q} {P : Pred (Fin n) p} {Q : Pred (Fin n) q} →
               Decidable Q → (∀ {f} → Q f → Dec (P f)) → Dec (Q ⊆ P)
decFinSubset {zero}  {_}     {_} _  _  = yes λ{}
decFinSubset {suc n} {P = P} {Q} Q? P? with decFinSubset (Q? ∘ suc) P?
... | no ¬q⟶p = no (λ q⟶p → ¬q⟶p (q⟶p))
... | yes q⟶p with Q? zero
...   | no ¬q₀ = yes (∀-cons {P = Q U.⇒ P} (⊥-elim ∘ ¬q₀) (λ _ → q⟶p) _)
...   | yes q₀ with P? q₀
...     | no ¬p₀ = no (λ q⟶p → ¬p₀ (q⟶p q₀))
...     | yes p₀ = yes (∀-cons {P = Q U.⇒ P} (λ _ → p₀) (λ _ → q⟶p) _)

any? : ∀ {n p} {P : Fin n → Set p} → Decidable P → Dec (∃ P)
any? {zero}  {_} P? = no λ { (() , _) }
any? {suc n} {P} P? with P? zero | any? (P? ∘ suc)
... | yes P₀ | _              = yes (_ , P₀)
... | no  _  | yes (_ , P₁₊ᵢ) = yes (_ , P₁₊ᵢ)
... | no ¬P₀ | no ¬P₁₊ᵢ       = no λ
  { (zero  , P₀)   → ¬P₀ P₀
  ; (suc f , P₁₊ᵢ) → ¬P₁₊ᵢ (_ , P₁₊ᵢ)
  }

all? : ∀ {n p} {P : Pred (Fin n) p} →
       Decidable P → Dec (∀ f → P f)
all? P? with decFinSubset U? (λ {f} _ → P? f)
... | yes ∀p = yes (λ f → ∀p tt)
... | no ¬∀p = no  (λ ∀p → ¬∀p (λ _ → ∀p _))

-- If a decidable predicate P over a finite set is sometimes false,
-- then we can find the smallest value for which this is the case.

¬∀⟶∃¬-smallest : ∀ n {p} (P : Pred (Fin n) p) → Decidable P →
                 ¬ (∀ i → P i) → ∃ λ i → ¬ P i × ((j : Fin′ i) → P (inject j))
¬∀⟶∃¬-smallest zero    P P? ¬∀P = contradiction (λ()) ¬∀P
¬∀⟶∃¬-smallest (suc n) P P? ¬∀P with P? zero
... | no ¬P₀ = (zero , ¬P₀ , λ ())
... | yes P₀ = map suc (map id (∀-cons P₀))
  (¬∀⟶∃¬-smallest n (P ∘ suc) (P? ∘ suc) (¬∀P ∘ (∀-cons P₀)))

-- When P is a decidable predicate over a finite set the following
-- lemma can be proved.

¬∀⟶∃¬ : ∀ n {p} (P : Pred (Fin n) p) → Decidable P →
          ¬ (∀ i → P i) → (∃ λ i → ¬ P i)
¬∀⟶∃¬ n P P? ¬P = map id proj₁ (¬∀⟶∃¬-smallest n P P? ¬P)

-- The pigeonhole principle.

pigeonhole : ∀ {m n} → m ℕ.< n → (f : Fin n → Fin m) →
             ∃₂ λ i j → i ≢ j × f i ≡ f j
pigeonhole (s≤s z≤n)       f = contradiction (f zero) λ()
pigeonhole (s≤s (s≤s m≤n)) f with any? (λ k → f zero ≟ f (suc k))
... | yes (j , f₀≡fⱼ) = zero , suc j , (λ()) , f₀≡fⱼ
... | no  f₀≢fₖ with pigeonhole (s≤s m≤n) (λ j → punchOut (f₀≢fₖ ∘ (j ,_ )))
...   | (i , j , i≢j , fᵢ≡fⱼ) =
  suc i , suc j , i≢j ∘ suc-injective ,
  punchOut-injective (f₀≢fₖ ∘ (i ,_)) _ fᵢ≡fⱼ

------------------------------------------------------------------------
-- Categorical

module _ {f} {F : Set f → Set f} (RA : RawApplicative F) where

  open RawApplicative RA

  sequence : ∀ {n} {P : Pred (Fin n) f} →
             (∀ i → F (P i)) → F (∀ i → P i)
  sequence {zero}  ∀iPi = pure λ()
  sequence {suc n} ∀iPi = ∀-cons <$> ∀iPi zero ⊛ sequence (∀iPi ∘ suc)

module _ {f} {F : Set f → Set f} (RF : RawFunctor F) where

  open RawFunctor RF

  sequence⁻¹ : ∀ {A : Set f} {P : Pred A f} →
               F (∀ i → P i) → (∀ i → F (P i))
  sequence⁻¹ F∀iPi i = (λ f → f i) <$> F∀iPi

------------------------------------------------------------------------
-- If there is an injection from a type to a finite set, then the type
-- has decidable equality.

module _ {a} {A : Set a} where

  eq? : ∀ {n} → A ↣ Fin n → B.Decidable {A = A} _≡_
  eq? inj = Dec.via-injection inj _≟_

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

cmp              = <-cmp
strictTotalOrder = <-strictTotalOrder

to-from          = toℕ-fromℕ
from-to          = fromℕ-toℕ

bounded          = toℕ<n
prop-toℕ-≤      = toℕ≤pred[n]
prop-toℕ-≤′     = toℕ≤pred[n]′

inject-lemma     = toℕ-inject
inject+-lemma    = toℕ-inject+
inject₁-lemma    = toℕ-inject₁
inject≤-lemma    = toℕ-inject≤

open import Data.Fin public using (_≟_; _<?_)
