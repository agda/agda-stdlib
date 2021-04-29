------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Properties where

open import Category.Applicative using (RawApplicative)
open import Category.Functor using (RawFunctor)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s; z≤n; _∸_)
import Data.Nat.Properties as ℕₚ
open import Data.Unit using (tt)
open import Data.Product using (Σ-syntax; ∃; ∃₂; ∄; _×_; _,_; map; proj₁; uncurry; <_,_>)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Sum.Properties using ([,]-map-commute; [,]-∘-distr)
open import Function.Base using (_∘_; id; _$_)
open import Function.Bundles using (_↔_; mk↔′)
open import Function.Definitions.Core2 using (Surjective)
open import Function.Equivalence using (_⇔_; equivalence)
open import Function.Injection using (_↣_)
open import Relation.Binary as B hiding (Decidable; _⇔_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable as Dec using (map′)
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary
  using (Reflects; ofʸ; ofⁿ; Dec; _because_; does; proof; yes; no; ¬_)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary as U
  using (U; Pred; Decidable; _⊆_; Satisfiable; Universal)
open import Relation.Unary.Properties using (U?)

------------------------------------------------------------------------
-- Fin
------------------------------------------------------------------------

¬Fin0 : ¬ Fin 0
¬Fin0 ()

------------------------------------------------------------------------
-- Bundles

Fin0↔⊥ : Fin 0 ↔ ⊥
Fin0↔⊥ = mk↔′ ¬Fin0 (λ ()) (λ ()) (λ ())

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

suc-injective : ∀ {o} {m n : Fin o} → Fin.suc m ≡ suc n → m ≡ n
suc-injective refl = refl

infix 4 _≟_

_≟_ : ∀ {n} → B.Decidable {A = Fin n} _≡_
zero  ≟ zero  = yes refl
zero  ≟ suc y = no λ()
suc x ≟ zero  = no λ()
suc x ≟ suc y = map′ (cong suc) suc-injective (x ≟ y)

------------------------------------------------------------------------
-- Structures

≡-isDecEquivalence : ∀ {n} → IsDecEquivalence (_≡_ {A = Fin n})
≡-isDecEquivalence = record
  { isEquivalence = P.isEquivalence
  ; _≟_           = _≟_
  }

------------------------------------------------------------------------
-- Bundles

≡-preorder : ℕ → Preorder _ _ _
≡-preorder n = P.preorder (Fin n)

≡-setoid : ℕ → Setoid _ _
≡-setoid n = P.setoid (Fin n)

≡-decSetoid : ℕ → DecSetoid _ _
≡-decSetoid n = record
  { isDecEquivalence = ≡-isDecEquivalence {n}
  }

------------------------------------------------------------------------
-- toℕ
------------------------------------------------------------------------

toℕ-injective : ∀ {n} {i j : Fin n} → toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {zero}  {}      {}      _
toℕ-injective {suc n} {zero}  {zero}  eq = refl
toℕ-injective {suc n} {suc i} {suc j} eq =
  cong suc (toℕ-injective (cong ℕ.pred eq))

toℕ-strengthen : ∀ {n} (i : Fin n) → toℕ (strengthen i) ≡ toℕ i
toℕ-strengthen zero    = refl
toℕ-strengthen (suc i) = cong suc (toℕ-strengthen i)

toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n ℕ.+ toℕ i
toℕ-raise zero    i = refl
toℕ-raise (suc n) i = cong suc (toℕ-raise n i)

toℕ<n : ∀ {n} (i : Fin n) → toℕ i ℕ.< n
toℕ<n zero    = s≤s z≤n
toℕ<n (suc i) = s≤s (toℕ<n i)

toℕ≤n : ∀ {n} → (i : Fin n) → toℕ i ℕ.≤ n
toℕ≤n = ℕₚ.<⇒≤ ∘ toℕ<n

toℕ≤pred[n] : ∀ {n} (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n] zero                 = z≤n
toℕ≤pred[n] (suc {n = suc n} i)  = s≤s (toℕ≤pred[n] i)

-- A simpler implementation of toℕ≤pred[n],
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of toℕ≤pred[n],
-- it can be removed in favor of toℕ≤pred[n]′.
toℕ≤pred[n]′ : ∀ {n} (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n]′ i = ℕₚ.<⇒≤pred (toℕ<n i)

------------------------------------------------------------------------
-- fromℕ
------------------------------------------------------------------------

toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = cong suc (toℕ-fromℕ n)

fromℕ-toℕ : ∀ {n} (i : Fin n) → fromℕ (toℕ i) ≡ strengthen i
fromℕ-toℕ zero    = refl
fromℕ-toℕ (suc i) = cong suc (fromℕ-toℕ i)

≤fromℕ : ∀ {n} → (i : Fin (ℕ.suc n)) → i ≤ fromℕ n
≤fromℕ {n} i = subst (toℕ i ℕ.≤_) (sym (toℕ-fromℕ n)) (ℕₚ.≤-pred (toℕ<n i))

------------------------------------------------------------------------
-- fromℕ<
------------------------------------------------------------------------

fromℕ<-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i ℕ.< m) → fromℕ< i<m ≡ i
fromℕ<-toℕ zero    (s≤s z≤n)       = refl
fromℕ<-toℕ (suc i) (s≤s (s≤s m≤n)) = cong suc (fromℕ<-toℕ i (s≤s m≤n))

toℕ-fromℕ< : ∀ {m n} (m<n : m ℕ.< n) → toℕ (fromℕ< m<n) ≡ m
toℕ-fromℕ< (s≤s z≤n)       = refl
toℕ-fromℕ< (s≤s (s≤s m<n)) = cong suc (toℕ-fromℕ< (s≤s m<n))

-- fromℕ is a special case of fromℕ<.
fromℕ-def : ∀ n → fromℕ n ≡ fromℕ< ℕₚ.≤-refl
fromℕ-def zero    = refl
fromℕ-def (suc n) = cong suc (fromℕ-def n)

fromℕ<-cong : ∀ m n {o} → m ≡ n →
              (m<o : m ℕ.< o) →
              (n<o : n ℕ.< o) →
              fromℕ< m<o ≡ fromℕ< n<o
fromℕ<-cong 0       0       r (s≤s z≤n)     (s≤s z≤n)     = refl
fromℕ<-cong (suc _) (suc _) r (s≤s (s≤s p)) (s≤s (s≤s q))
  = cong suc (fromℕ<-cong _ _ (ℕₚ.suc-injective r) (s≤s p) (s≤s q))

fromℕ<-injective : ∀ m n {o} →
                   (m<o : m ℕ.< o) →
                   (n<o : n ℕ.< o) →
                   fromℕ< m<o ≡ fromℕ< n<o →
                   m ≡ n
fromℕ<-injective 0 0 (s≤s z≤n) (s≤s z≤n) r = refl
fromℕ<-injective (suc _) (suc _) (s≤s (s≤s p)) (s≤s (s≤s q)) r
  = cong suc (fromℕ<-injective _ _ (s≤s p) (s≤s q) (suc-injective r))

------------------------------------------------------------------------
-- fromℕ<″
------------------------------------------------------------------------

fromℕ<≡fromℕ<″ : ∀ {m n} (m<n : m ℕ.< n) (m<″n : m ℕ.<″ n) →
                 fromℕ< m<n ≡ fromℕ<″ m m<″n
fromℕ<≡fromℕ<″ (s≤s z≤n)       (ℕ.less-than-or-equal refl) = refl
fromℕ<≡fromℕ<″ (s≤s (s≤s m<n)) (ℕ.less-than-or-equal refl) =
  cong suc (fromℕ<≡fromℕ<″ (s≤s m<n) (ℕ.less-than-or-equal refl))

toℕ-fromℕ<″ : ∀ {m n} (m<n : m ℕ.<″ n) → toℕ (fromℕ<″ m m<n) ≡ m
toℕ-fromℕ<″ {m} {n} m<n = begin
  toℕ (fromℕ<″ m m<n)  ≡⟨ cong toℕ (sym (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ m<n) m<n)) ⟩
  toℕ (fromℕ< _)       ≡⟨ toℕ-fromℕ< (ℕₚ.≤″⇒≤ m<n) ⟩
  m ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- cast
------------------------------------------------------------------------

toℕ-cast : ∀ {m n} .(eq : m ≡ n) (k : Fin m) → toℕ (cast eq k) ≡ toℕ k
toℕ-cast {n = suc n} eq zero    = refl
toℕ-cast {n = suc n} eq (suc k) = cong suc (toℕ-cast (cong ℕ.pred eq) k)

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------
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

≤-irrelevant : ∀ {n} → Irrelevant (_≤_ {n})
≤-irrelevant = ℕₚ.≤-irrelevant

infix 4 _≤?_ _<?_

_≤?_ : ∀ {n} → B.Decidable (_≤_ {n})
a ≤? b = toℕ a ℕₚ.≤? toℕ b

_<?_ : ∀ {n} → B.Decidable (_<_ {n})
m <? n = suc (toℕ m) ℕₚ.≤? toℕ n

------------------------------------------------------------------------
-- Structures

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

≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

------------------------------------------------------------------------
-- Bundles

≤-preorder : ℕ → Preorder _ _ _
≤-preorder n = record
  { isPreorder = ≤-isPreorder {n}
  }

≤-poset : ℕ → Poset _ _ _
≤-poset n = record
  { isPartialOrder = ≤-isPartialOrder {n}
  }

≤-totalOrder : ℕ → TotalOrder _ _ _
≤-totalOrder n = record
  { isTotalOrder = ≤-isTotalOrder {n}
  }

≤-decTotalOrder : ℕ → DecTotalOrder _ _ _
≤-decTotalOrder n = record
  { isDecTotalOrder = ≤-isDecTotalOrder {n}
  }

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------
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
... | tri< i<j i≢j j≮i = tri< (s≤s i<j)         (i≢j ∘ suc-injective) (j≮i ∘ ℕₚ.≤-pred)
... | tri> i≮j i≢j j<i = tri> (i≮j ∘ ℕₚ.≤-pred) (i≢j ∘ suc-injective) (s≤s j<i)
... | tri≈ i≮j i≡j j≮i = tri≈ (i≮j ∘ ℕₚ.≤-pred) (cong suc i≡j)        (j≮i ∘ ℕₚ.≤-pred)

<-respˡ-≡ : ∀ {n} → (_<_ {n}) Respectsˡ _≡_
<-respˡ-≡ refl x≤y = x≤y

<-respʳ-≡ : ∀ {n} → (_<_ {n}) Respectsʳ _≡_
<-respʳ-≡ refl x≤y = x≤y

<-resp₂-≡ : ∀ {n} → (_<_ {n}) Respects₂ _≡_
<-resp₂-≡ = <-respʳ-≡ , <-respˡ-≡

<-irrelevant : ∀ {n} → Irrelevant (_<_ {n})
<-irrelevant = ℕₚ.<-irrelevant

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder : ∀ {n} → IsStrictPartialOrder _≡_ (_<_ {n})
<-isStrictPartialOrder = record
  { isEquivalence = P.isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp₂-≡
  }

<-isStrictTotalOrder : ∀ {n} → IsStrictTotalOrder _≡_ (_<_ {n})
<-isStrictTotalOrder = record
  { isEquivalence = P.isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

------------------------------------------------------------------------
-- Bundles

<-strictPartialOrder : ℕ → StrictPartialOrder _ _ _
<-strictPartialOrder n = record
  { isStrictPartialOrder = <-isStrictPartialOrder {n}
  }

<-strictTotalOrder : ℕ → StrictTotalOrder _ _ _
<-strictTotalOrder n = record
  { isStrictTotalOrder = <-isStrictTotalOrder {n}
  }

------------------------------------------------------------------------
-- Other properties

<⇒≢ : ∀ {n} {i j : Fin n} → i < j → i ≢ j
<⇒≢ i<i refl = ℕₚ.n≮n _ i<i

≤∧≢⇒< : ∀ {n} {i j : Fin n} → i ≤ j → i ≢ j → i < j
≤∧≢⇒< {i = zero}  {zero}  _         0≢0     = contradiction refl 0≢0
≤∧≢⇒< {i = zero}  {suc j} _         _       = s≤s z≤n
≤∧≢⇒< {i = suc i} {suc j} (s≤s i≤j) 1+i≢1+j =
  s≤s (≤∧≢⇒< i≤j (1+i≢1+j ∘ (cong suc)))

------------------------------------------------------------------------
-- inject
------------------------------------------------------------------------

toℕ-inject : ∀ {n} {i : Fin n} (j : Fin′ i) →
             toℕ (inject j) ≡ toℕ j
toℕ-inject {i = suc i} zero    = refl
toℕ-inject {i = suc i} (suc j) = cong suc (toℕ-inject j)

------------------------------------------------------------------------
-- inject+
------------------------------------------------------------------------

toℕ-inject+ : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (inject+ n i)
toℕ-inject+ n zero    = refl
toℕ-inject+ n (suc i) = cong suc (toℕ-inject+ n i)

------------------------------------------------------------------------
-- inject₁
------------------------------------------------------------------------

inject₁-injective : ∀ {n} {i j : Fin n} → inject₁ i ≡ inject₁ j → i ≡ j
inject₁-injective {i = zero}  {zero}  i≡j = refl
inject₁-injective {i = suc i} {suc j} i≡j =
  cong suc (inject₁-injective (suc-injective i≡j))

toℕ-inject₁ : ∀ {n} (i : Fin n) → toℕ (inject₁ i) ≡ toℕ i
toℕ-inject₁ zero    = refl
toℕ-inject₁ (suc i) = cong suc (toℕ-inject₁ i)

toℕ-inject₁-≢ : ∀ {n}(i : Fin n) → n ≢ toℕ (inject₁ i)
toℕ-inject₁-≢ (suc i) = toℕ-inject₁-≢ i ∘ ℕₚ.suc-injective

inject₁ℕ< : ∀ {n} → (i : Fin n) → toℕ (inject₁ i) ℕ.< n
inject₁ℕ< {n} i = subst (ℕ._< n) (sym (toℕ-inject₁ i)) (toℕ<n i)

inject₁ℕ≤ : ∀ {n} → (i : Fin n) → toℕ (inject₁ i) ℕ.≤ n
inject₁ℕ≤ = ℕₚ.<⇒≤ ∘ inject₁ℕ<

≤̄⇒inject₁< : ∀ {n} → {i j : Fin n} → j ≤ i → inject₁ j < suc i
≤̄⇒inject₁< {i = i} {j} p = subst (ℕ._< toℕ (suc i)) (sym (toℕ-inject₁ j)) (s≤s p)

ℕ<⇒inject₁< : ∀ {n} → {i : Fin (ℕ.suc n)} → {j : Fin n} →
              toℕ j ℕ.< toℕ i → inject₁ j < i
ℕ<⇒inject₁< {i = suc i} (s≤s p) = ≤̄⇒inject₁< p

------------------------------------------------------------------------
-- lower₁
------------------------------------------------------------------------

toℕ-lower₁ : ∀ {m} x → (p : m ≢ toℕ x) → toℕ (lower₁ x p) ≡ toℕ x
toℕ-lower₁ {ℕ.zero} zero p     = contradiction refl p
toℕ-lower₁ {ℕ.suc m} zero p    = refl
toℕ-lower₁ {ℕ.suc m} (suc x) p = cong ℕ.suc (toℕ-lower₁ x (p ∘ cong ℕ.suc))

------------------------------------------------------------------------
-- inject₁ and lower₁

inject₁-lower₁ : ∀ {n} (i : Fin (suc n)) (n≢i : n ≢ toℕ i) →
                 inject₁ (lower₁ i n≢i) ≡ i
inject₁-lower₁ {zero}  zero     0≢0     = contradiction refl 0≢0
inject₁-lower₁ {suc n} zero     _       = refl
inject₁-lower₁ {suc n} (suc i)  n+1≢i+1 =
  cong suc (inject₁-lower₁ i  (n+1≢i+1 ∘ cong suc))

lower₁-inject₁′ : ∀ {n} (i : Fin n) (n≢i : n ≢ toℕ (inject₁ i)) →
                  lower₁ (inject₁ i) n≢i ≡ i
lower₁-inject₁′ zero    _       = refl
lower₁-inject₁′ (suc i) n+1≢i+1 =
  cong suc (lower₁-inject₁′ i (n+1≢i+1 ∘ cong suc))

lower₁-inject₁ : ∀ {n} (i : Fin n) →
                 lower₁ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
lower₁-inject₁ i = lower₁-inject₁′ i (toℕ-inject₁-≢ i)

lower₁-irrelevant : ∀ {n} (i : Fin (suc n)) n≢i₁ n≢i₂ →
             lower₁ {n} i n≢i₁ ≡ lower₁ {n} i n≢i₂
lower₁-irrelevant {zero}  zero     0≢0 _ = contradiction refl 0≢0
lower₁-irrelevant {suc n} zero     _   _ = refl
lower₁-irrelevant {suc n} (suc i)  _   _ =
  cong suc (lower₁-irrelevant i _ _)

inject₁≡⇒lower₁≡ : ∀ {n} → {i : Fin n} →
                  {j : Fin (ℕ.suc n)} →
                  (≢p : n ≢ (toℕ j)) →
                  inject₁ i ≡ j →
                  lower₁ j ≢p ≡ i
inject₁≡⇒lower₁≡ ≢p ≡p = inject₁-injective (trans (inject₁-lower₁ _ ≢p) (sym ≡p))

------------------------------------------------------------------------
-- inject≤
------------------------------------------------------------------------

toℕ-inject≤ : ∀ {m n} (i : Fin m) (le : m ℕ.≤ n) →
                toℕ (inject≤ i le) ≡ toℕ i
toℕ-inject≤ {_} {suc n} zero    _  = refl
toℕ-inject≤ {_} {suc n} (suc i) le = cong suc (toℕ-inject≤ i (ℕₚ.≤-pred le))

inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ.≤ n) → inject≤ i n≤n ≡ i
inject≤-refl {suc n} zero    _   = refl
inject≤-refl {suc n} (suc i) n≤n = cong suc (inject≤-refl i (ℕₚ.≤-pred n≤n))

inject≤-idempotent : ∀ {m n k} (i : Fin m)
                     (m≤n : m ℕ.≤ n) (n≤k : n ℕ.≤ k) (m≤k : m ℕ.≤ k) →
                     inject≤ (inject≤ i m≤n) n≤k ≡ inject≤ i m≤k
inject≤-idempotent {_} {suc n} {suc k} zero    _   _   _ = refl
inject≤-idempotent {_} {suc n} {suc k} (suc i) m≤n n≤k _ =
  cong suc (inject≤-idempotent i (ℕₚ.≤-pred m≤n) (ℕₚ.≤-pred n≤k) _)

inject≤-injective : ∀ {n m} (n≤m n≤m′ : n ℕ.≤ m) x y → inject≤ x n≤m ≡ inject≤ y n≤m′ → x ≡ y
inject≤-injective (s≤s p) (s≤s q) zero zero eq = refl
inject≤-injective (s≤s p) (s≤s q) (suc x) (suc y) eq =
  cong suc (inject≤-injective p q x y (suc-injective eq))

------------------------------------------------------------------------
-- pred
------------------------------------------------------------------------

pred< : ∀ {n} → (i : Fin (ℕ.suc n)) → i ≢ zero → pred i < i
pred< zero p = contradiction refl p
pred< (suc i) p = ≤̄⇒inject₁< ℕₚ.≤-refl

------------------------------------------------------------------------
-- splitAt
------------------------------------------------------------------------

-- Fin (m + n) ↔ Fin m ⊎ Fin n

splitAt-inject+ : ∀ m n i → splitAt m (inject+ n i) ≡ inj₁ i
splitAt-inject+ (suc m) n zero = refl
splitAt-inject+ (suc m) n (suc i) rewrite splitAt-inject+ m n i = refl

splitAt-raise : ∀ m n i → splitAt m (raise {n} m i) ≡ inj₂ i
splitAt-raise zero    n i = refl
splitAt-raise (suc m) n i rewrite splitAt-raise m n i = refl

splitAt-join : ∀ m n i → splitAt m (join m n i) ≡ i
splitAt-join m n (inj₁ x) = splitAt-inject+ m n x
splitAt-join m n (inj₂ y) = splitAt-raise m n y

join-splitAt : ∀ m n i → join m n (splitAt m i) ≡ i
join-splitAt zero    n i       = refl
join-splitAt (suc m) n zero    = refl
join-splitAt (suc m) n (suc i) = begin
  [ inject+ n , raise {n} (suc m) ]′ (splitAt (suc m) (suc i))  ≡⟨ [,]-map-commute (splitAt m i) ⟩
  [ suc ∘ (inject+ n) , suc ∘ (raise {n} m) ]′ (splitAt m i)    ≡˘⟨ [,]-∘-distr suc (splitAt m i) ⟩
  suc ([ inject+ n , raise {n} m ]′ (splitAt m i))              ≡⟨ cong suc (join-splitAt m n i) ⟩
  suc i                                                         ∎
  where open ≡-Reasoning

-- splitAt "m" "i" ≡ inj₁ "i" if i < m

splitAt-< : ∀ m {n} i → (i<m : toℕ i ℕ.< m) → splitAt m {n} i ≡ inj₁ (fromℕ< i<m)
splitAt-< (suc m) zero    _         = refl
splitAt-< (suc m) (suc i) (s≤s i<m) = cong (Sum.map suc id) (splitAt-< m i i<m)

-- splitAt "m" "i" ≡ inj₂ "i - m" if i ≥ m

splitAt-≥ : ∀ m {n} i → (i≥m : toℕ i ℕ.≥ m) → splitAt m {n} i ≡ inj₂ (reduce≥ i i≥m)
splitAt-≥ zero    i       _         = refl
splitAt-≥ (suc m) (suc i) (s≤s i≥m) = cong (Sum.map suc id) (splitAt-≥ m i i≥m)

------------------------------------------------------------------------
-- Bundles

+↔⊎ : ∀ {m n} → Fin (m ℕ.+ n) ↔ (Fin m ⊎ Fin n)
+↔⊎ {m} {n} = mk↔′ (splitAt m {n}) (join m n) (splitAt-join m n) (join-splitAt m n)

------------------------------------------------------------------------
-- remQuot
------------------------------------------------------------------------

-- Fin (m * n) ↔ Fin m × Fin n

remQuot-combine : ∀ {n k} (x : Fin n) y → remQuot k (combine x y) ≡ (x , y)
remQuot-combine {suc n} {k} 0F y rewrite splitAt-inject+ k (n ℕ.* k) y = refl
remQuot-combine {suc n} {k} (suc x) y rewrite splitAt-raise k (n ℕ.* k) (combine x y) = cong (Data.Product.map₁ suc) (remQuot-combine x y)

combine-remQuot : ∀ {n} k (i : Fin (n ℕ.* k)) → uncurry combine (remQuot {n} k i) ≡ i
combine-remQuot {suc n} k i with splitAt k i | P.inspect (splitAt k) i
... | inj₁ j | P.[ eq ] = begin
  join k (n ℕ.* k) (inj₁ j)      ≡˘⟨ cong (join k (n ℕ.* k)) eq ⟩
  join k (n ℕ.* k) (splitAt k i) ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                              ∎
  where open ≡-Reasoning
... | inj₂ j | P.[ eq ] = begin
  raise {n ℕ.* k} k (uncurry combine (remQuot {n} k j)) ≡⟨ cong (raise k) (combine-remQuot {n} k j) ⟩
  join k (n ℕ.* k) (inj₂ j)                             ≡˘⟨ cong (join k (n ℕ.* k)) eq ⟩
  join k (n ℕ.* k) (splitAt k i)                        ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                                                     ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Bundles
*↔× : ∀ {m n} → Fin (m ℕ.* n) ↔ (Fin m × Fin n)
*↔× {m} {n} = mk↔′ (remQuot {m} n) (uncurry combine) (uncurry remQuot-combine) (combine-remQuot {m} n)

------------------------------------------------------------------------
-- lift
------------------------------------------------------------------------

lift-injective : ∀ {m n} (f : Fin m → Fin n) →
                 (∀ {x y} → f x ≡ f y → x ≡ y) →
                 ∀ k {x y} → lift k f x ≡ lift k f y → x ≡ y
lift-injective f inj zero                    eq = inj eq
lift-injective f inj (suc k) {0F} {0F}       eq = refl
lift-injective f inj (suc k) {suc i} {suc y} eq = cong suc (lift-injective f inj k (suc-injective eq))


------------------------------------------------------------------------
-- _≺_
------------------------------------------------------------------------

≺⇒<′ : _≺_ ⇒ ℕ._<′_
≺⇒<′ (n ≻toℕ i) = ℕₚ.≤⇒≤′ (toℕ<n i)

<′⇒≺ : ℕ._<′_ ⇒ _≺_
<′⇒≺ {n} ℕ.≤′-refl = subst (_≺ suc n) (toℕ-fromℕ n)
                              (suc n ≻toℕ fromℕ n)
<′⇒≺ (ℕ.≤′-step m≤′n) with <′⇒≺ m≤′n
... | n ≻toℕ i = subst (_≺ suc n) (toℕ-inject₁ i) (suc n ≻toℕ _)

------------------------------------------------------------------------
-- pred
------------------------------------------------------------------------

<⇒≤pred : ∀ {n} {i j : Fin n} → j < i → j ≤ pred i
<⇒≤pred {i = suc i} {zero}  j<i       = z≤n
<⇒≤pred {i = suc i} {suc j} (s≤s j<i) =
  subst (_ ℕ.≤_) (sym (toℕ-inject₁ i)) j<i

------------------------------------------------------------------------
-- _ℕ-_
------------------------------------------------------------------------

toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
toℕ‿ℕ- n       zero     = toℕ-fromℕ n
toℕ‿ℕ- (suc n) (suc i)  = toℕ‿ℕ- n i

------------------------------------------------------------------------
-- _ℕ-ℕ_
------------------------------------------------------------------------

nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ.≤ n
nℕ-ℕi≤n n       zero     = ℕₚ.≤-refl
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i  ≤⟨ nℕ-ℕi≤n n i ⟩
  n        ≤⟨ ℕₚ.n≤1+n n ⟩
  suc n    ∎
  where open ℕₚ.≤-Reasoning

------------------------------------------------------------------------
-- punchIn
------------------------------------------------------------------------

punchIn-injective : ∀ {m} i (j k : Fin m) →
                    punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective zero    _       _       refl      = refl
punchIn-injective (suc i) zero    zero    _         = refl
punchIn-injective (suc i) (suc j) (suc k) ↑j+1≡↑k+1 =
  cong suc (punchIn-injective i j k (suc-injective ↑j+1≡↑k+1))

punchInᵢ≢i : ∀ {m} i (j : Fin m) → punchIn i j ≢ i
punchInᵢ≢i (suc i) (suc j) = punchInᵢ≢i i j ∘ suc-injective

------------------------------------------------------------------------
-- punchOut
------------------------------------------------------------------------

-- A version of 'cong' for 'punchOut' in which the inequality argument can be
-- changed out arbitrarily (reflecting the proof-irrelevance of that argument).

punchOut-cong : ∀ {n} (i : Fin (suc n)) {j k} {i≢j : i ≢ j} {i≢k : i ≢ k} → j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong zero {zero} {i≢j = 0≢0} = contradiction refl 0≢0
punchOut-cong zero {suc j} {zero} {i≢k = 0≢0} = contradiction refl 0≢0
punchOut-cong zero {suc j} {suc k} = suc-injective
punchOut-cong {suc n} (suc i) {zero} {zero} _ = refl
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
punchOut-injective {suc n} {suc i}  {zero}  {zero}  _   _    _    = refl
punchOut-injective {suc n} {suc i}  {suc j} {suc k} i≢j i≢k pⱼ≡pₖ =
  cong suc (punchOut-injective (i≢j ∘ cong suc) (i≢k ∘ cong suc) (suc-injective pⱼ≡pₖ))

punchIn-punchOut : ∀ {m} {i j : Fin (suc m)} (i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut {_}     {zero}   {zero}  0≢0 = contradiction refl 0≢0
punchIn-punchOut {_}     {zero}   {suc j} _   = refl
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
-- pinch
------------------------------------------------------------------------

pinch-surjective : ∀ {m} (i : Fin m) → Surjective _≡_ (pinch i)
pinch-surjective _       zero    = zero , refl
pinch-surjective zero    (suc j) = suc (suc j) , refl
pinch-surjective (suc i) (suc j) = map suc (cong suc) (pinch-surjective i j)

pinch-mono-≤ : ∀ {m} (i : Fin m) → (pinch i) Preserves _≤_ ⟶ _≤_
pinch-mono-≤ 0F      {0F}    {k}     0≤n       = z≤n
pinch-mono-≤ 0F      {suc j} {suc k} (s≤s j≤k) = j≤k
pinch-mono-≤ (suc i) {0F}    {k}     0≤n       = z≤n
pinch-mono-≤ (suc i) {suc j} {suc k} (s≤s j≤k) = s≤s (pinch-mono-≤ i j≤k)

------------------------------------------------------------------------
-- Quantification
------------------------------------------------------------------------

module _ {n p} {P : Pred (Fin (suc n)) p} where

  ∀-cons : P zero → Π[ P ∘ suc ] → Π[ P ]
  ∀-cons z s zero    = z
  ∀-cons z s (suc i) = s i

  ∀-cons-⇔ : (P zero × Π[ P ∘ suc ]) ⇔ Π[ P ]
  ∀-cons-⇔ = equivalence (uncurry ∀-cons) < _$ zero , _∘ suc >

  ∃-here : P zero → ∃⟨ P ⟩
  ∃-here = zero ,_

  ∃-there : ∃⟨ P ∘ suc ⟩ → ∃⟨ P ⟩
  ∃-there = map suc id

  ∃-toSum : ∃⟨ P ⟩ → P zero ⊎ ∃⟨ P ∘ suc ⟩
  ∃-toSum ( zero , P₀ ) = inj₁ P₀
  ∃-toSum (suc f , P₁₊) = inj₂ (f , P₁₊)

  ⊎⇔∃ : (P zero ⊎ ∃⟨ P ∘ suc ⟩) ⇔ ∃⟨ P ⟩
  ⊎⇔∃ = equivalence [ ∃-here , ∃-there ] ∃-toSum

decFinSubset : ∀ {n p q} {P : Pred (Fin n) p} {Q : Pred (Fin n) q} →
               Decidable Q → (∀ {f} → Q f → Dec (P f)) → Dec (Q ⊆ P)
decFinSubset {zero} Q? P? = yes λ {}
decFinSubset {suc n} {P = P} {Q} Q? P?
  with Q? zero | ∀-cons {P = λ x → Q x → P x}
... | false because [¬Q0] | cons =
  map′ (λ f {x} → cons (⊥-elim ∘ invert [¬Q0]) (λ x → f {x}) x)
       (λ f {x} → f {suc x})
       (decFinSubset (Q? ∘ suc) P?)
... | true  because  [Q0] | cons =
  map′ (uncurry λ P0 rec {x} → cons (λ _ → P0) (λ x → rec {x}) x)
       < _$ invert [Q0] , (λ f {x} → f {suc x}) >
       (P? (invert [Q0]) ×-dec decFinSubset (Q? ∘ suc) P?)

any? : ∀ {n p} {P : Fin n → Set p} → Decidable P → Dec (∃ P)
any? {zero}  {P = _} P? = no λ { (() , _) }
any? {suc n} {P = P} P? = Dec.map ⊎⇔∃ (P? zero ⊎-dec any? (P? ∘ suc))

all? : ∀ {n p} {P : Pred (Fin n) p} →
       Decidable P → Dec (∀ f → P f)
all? P? = map′ (λ ∀p f → ∀p tt) (λ ∀p {x} _ → ∀p x)
               (decFinSubset U? (λ {f} _ → P? f))

private
  -- A nice computational property of `all?`:
  -- The boolean component of the result is exactly the
  -- obvious fold of boolean tests (`foldr _∧_ true`).
  note : ∀ {p} {P : Pred (Fin 3) p} (P? : Decidable P) →
         ∃ λ z → does (all? P?) ≡ z
  note P? = does (P? 0F) ∧ does (P? 1F) ∧ does (P? 2F) ∧ true
          , refl

-- If a decidable predicate P over a finite set is sometimes false,
-- then we can find the smallest value for which this is the case.

¬∀⟶∃¬-smallest : ∀ n {p} (P : Pred (Fin n) p) → Decidable P →
                 ¬ (∀ i → P i) → ∃ λ i → ¬ P i × ((j : Fin′ i) → P (inject j))
¬∀⟶∃¬-smallest zero    P P? ¬∀P = contradiction (λ()) ¬∀P
¬∀⟶∃¬-smallest (suc n) P P? ¬∀P with P? zero
... | false because [¬P₀] = (zero , invert [¬P₀] , λ ())
... |  true because  [P₀] = map suc (map id (∀-cons (invert [P₀])))
  (¬∀⟶∃¬-smallest n (P ∘ suc) (P? ∘ suc) (¬∀P ∘ (∀-cons (invert [P₀]))))

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
------------------------------------------------------------------------

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

-- Version 0.15

cmp              = <-cmp
{-# WARNING_ON_USAGE cmp
"Warning: cmp was deprecated in v0.15.
Please use <-cmp instead."
#-}
strictTotalOrder = <-strictTotalOrder
{-# WARNING_ON_USAGE strictTotalOrder
"Warning: strictTotalOrder was deprecated in v0.15.
Please use <-strictTotalOrder instead."
#-}

-- Version 0.16

to-from = toℕ-fromℕ
{-# WARNING_ON_USAGE to-from
"Warning: to-from was deprecated in v0.16.
Please use toℕ-fromℕ instead."
#-}
from-to          = fromℕ-toℕ
{-# WARNING_ON_USAGE from-to
"Warning: from-to was deprecated in v0.16.
Please use fromℕ-toℕ instead."
#-}
bounded = toℕ<n
{-# WARNING_ON_USAGE bounded
"Warning: bounded was deprecated in v0.16.
Please use toℕ<n instead."
#-}
prop-toℕ-≤ = toℕ≤pred[n]
{-# WARNING_ON_USAGE prop-toℕ-≤
"Warning: prop-toℕ-≤ was deprecated in v0.16.
Please use toℕ≤pred[n] instead."
#-}
prop-toℕ-≤′ = toℕ≤pred[n]′
{-# WARNING_ON_USAGE prop-toℕ-≤′
"Warning: prop-toℕ-≤′ was deprecated in v0.16.
Please use toℕ≤pred[n]′ instead."
#-}
inject-lemma = toℕ-inject
{-# WARNING_ON_USAGE inject-lemma
"Warning: inject-lemma was deprecated in v0.16.
Please use toℕ-inject instead."
#-}
inject+-lemma = toℕ-inject+
{-# WARNING_ON_USAGE inject+-lemma
"Warning: inject+-lemma was deprecated in v0.16.
Please use toℕ-inject+ instead."
#-}
inject₁-lemma = toℕ-inject₁
{-# WARNING_ON_USAGE inject₁-lemma
"Warning: inject₁-lemma was deprecated in v0.16.
Please use toℕ-inject₁ instead."
#-}
inject≤-lemma = toℕ-inject≤
{-# WARNING_ON_USAGE inject≤-lemma
"Warning: inject≤-lemma was deprecated in v0.16.
Please use toℕ-inject≤ instead."
#-}

-- Version 0.17

≤+≢⇒< = ≤∧≢⇒<
{-# WARNING_ON_USAGE ≤+≢⇒<
"Warning: ≤+≢⇒< was deprecated in v0.17.
Please use ≤∧≢⇒< instead."
#-}

-- Version 1.0

≤-irrelevance = ≤-irrelevant
{-# WARNING_ON_USAGE ≤-irrelevance
"Warning: ≤-irrelevance was deprecated in v1.0.
Please use ≤-irrelevant instead."
#-}
<-irrelevance = <-irrelevant
{-# WARNING_ON_USAGE <-irrelevance
"Warning: <-irrelevance was deprecated in v1.0.
Please use <-irrelevant instead."
#-}

-- Version 1.1

infixl 6 _+′_
_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (ℕ.pred m ℕ.+ n)
i +′ j = inject≤ (i + j) (ℕₚ.+-monoˡ-≤ _ (toℕ≤pred[n] i))
{-# WARNING_ON_USAGE _+′_
"Warning: _+′_ was deprecated in v1.1.
Please use `raise` or `inject+` from `Data.Fin` instead."
#-}

-- Version 1.2

fromℕ≤-toℕ = fromℕ<-toℕ
{-# WARNING_ON_USAGE fromℕ≤-toℕ
"Warning: fromℕ≤-toℕ was deprecated in v1.2.
Please use fromℕ<-toℕ instead."
#-}
toℕ-fromℕ≤ = toℕ-fromℕ<
{-# WARNING_ON_USAGE toℕ-fromℕ≤
"Warning: toℕ-fromℕ≤ was deprecated in v1.2.
Please use toℕ-fromℕ< instead."
#-}
fromℕ≤≡fromℕ≤″ = fromℕ<≡fromℕ<″
{-# WARNING_ON_USAGE fromℕ≤≡fromℕ≤″
"Warning: fromℕ≤≡fromℕ≤″ was deprecated in v1.2.
Please use fromℕ<≡fromℕ<″ instead."
#-}
toℕ-fromℕ≤″ = toℕ-fromℕ<″
{-# WARNING_ON_USAGE toℕ-fromℕ≤″
"Warning: toℕ-fromℕ≤″ was deprecated in v1.2.
Please use toℕ-fromℕ<″ instead."
#-}
isDecEquivalence = ≡-isDecEquivalence
{-# WARNING_ON_USAGE isDecEquivalence
"Warning: isDecEquivalence was deprecated in v1.2.
Please use ≡-isDecEquivalence instead."
#-}
preorder = ≡-preorder
{-# WARNING_ON_USAGE preorder
"Warning: preorder was deprecated in v1.2.
Please use ≡-preorder instead."
#-}
setoid = ≡-setoid
{-# WARNING_ON_USAGE setoid
"Warning: setoid was deprecated in v1.2.
Please use ≡-setoid instead."
#-}
decSetoid = ≡-decSetoid
{-# WARNING_ON_USAGE decSetoid
"Warning: decSetoid was deprecated in v1.2.
Please use ≡-decSetoid instead."
#-}

-- Version 1.5

inject+-raise-splitAt = join-splitAt
{-# WARNING_ON_USAGE inject+-raise-splitAt
"Warning: decSetoid was deprecated in v1.5.
Please use join-splitAt instead."
#-}
