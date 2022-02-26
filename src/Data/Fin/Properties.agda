------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Properties where

open import Axiom.Extensionality.Propositional
open import Algebra.Definitions using (Involutive)
open import Category.Applicative using (RawApplicative)
open import Category.Functor using (RawFunctor)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s; z≤n; z<s; s<s; _∸_; _^_)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; ∃; ∃₂; ∄; _×_; _,_; map; proj₁; proj₂; uncurry; <_,_>)
open import Data.Product.Properties using (,-injective)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Sum.Properties using ([,]-map-commute; [,]-∘-distr)
open import Function.Base using (_∘_; id; _$_; flip)
open import Function.Bundles using (_↣_; _⇔_; _↔_; mk⇔; mk↔′)
open import Function.Definitions.Core2 using (Surjective)
open import Relation.Binary as B hiding (Decidable; _⇔_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_; module ≡-Reasoning)
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

0↔⊥ : Fin 0 ↔ ⊥
0↔⊥ = mk↔′ ¬Fin0 (λ ()) (λ ()) (λ ())

1↔⊤ : Fin 1 ↔ ⊤
1↔⊤ = mk↔′ (λ { 0F → tt }) (λ { tt → 0F }) (λ { tt → refl }) λ { 0F → refl }

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

------------------------------------------------------------------------
-- toℕ-↑ˡ: "i" ↑ˡ n = "i" in Fin (m + n)
------------------------------------------------------------------------

toℕ-↑ˡ : ∀ {m} (i : Fin m) n → toℕ (i ↑ˡ n) ≡ toℕ i
toℕ-↑ˡ zero    n = refl
toℕ-↑ˡ (suc i) n = cong suc (toℕ-↑ˡ i n)

↑ˡ-injective : ∀ {m} n (i j : Fin m) → i ↑ˡ n ≡ j ↑ˡ n → i ≡ j
↑ˡ-injective n zero zero refl = refl
↑ˡ-injective n (suc i) (suc j) eq =
  cong suc (↑ˡ-injective n i j (suc-injective eq))

------------------------------------------------------------------------
-- toℕ-↑ʳ: n ↑ʳ "i" = "n + i" in Fin (n + m)
------------------------------------------------------------------------

toℕ-↑ʳ : ∀ {m} n (i : Fin m) → toℕ (n ↑ʳ i) ≡ n ℕ.+ toℕ i
toℕ-↑ʳ zero    i = refl
toℕ-↑ʳ (suc n) i = cong suc (toℕ-↑ʳ n i)

↑ʳ-injective : ∀ {m} n (i j : Fin m) → n ↑ʳ i ≡ n ↑ʳ j → i ≡ j
↑ʳ-injective zero i i refl = refl
↑ʳ-injective (suc n) i j eq = ↑ʳ-injective n i j (suc-injective eq)

------------------------------------------------------------------------
-- toℕ and the ordering relations
------------------------------------------------------------------------

toℕ≤pred[n] : ∀ {n} (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n] zero                 = z≤n
toℕ≤pred[n] (suc {n = suc n} i)  = s≤s (toℕ≤pred[n] i)

toℕ≤n : ∀ {n} → (i : Fin n) → toℕ i ℕ.≤ n
toℕ≤n {suc n} i = ℕₚ.≤-step (toℕ≤pred[n] i)

toℕ<n : ∀ {n} (i : Fin n) → toℕ i ℕ.< n
toℕ<n {suc n} i = s≤s (toℕ≤pred[n] i)

-- A simpler implementation of toℕ≤pred[n],
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of toℕ≤pred[n],
-- it can be removed in favor of toℕ≤pred[n]′.
toℕ≤pred[n]′ : ∀ {n} (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n]′ i = ℕₚ.<⇒≤pred (toℕ<n i)

-- In view of the defintions now in Data.Fin.Base,
-- are these four lemmas not all the identity function?
toℕ-mono-< : ∀ {n} {i j : Fin n} → i < j → toℕ i ℕ.< toℕ j
toℕ-mono-< i<j = i<j

toℕ-mono-≤ : ∀ {n} {i j : Fin n} → i ≤ j → toℕ i ℕ.≤ toℕ j
toℕ-mono-≤ i≤j = i≤j

toℕ-cancel-≤ : ∀ {n} {i j : Fin n} → toℕ i ℕ.≤ toℕ j → i ≤ j
toℕ-cancel-≤ i≤j = i≤j

toℕ-cancel-< : ∀ {n} {i j : Fin n} → toℕ i ℕ.< toℕ j → i < j
toℕ-cancel-< i<j = i<j

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
≤fromℕ {n} i = subst (toℕ i ℕ.≤_) (sym (toℕ-fromℕ n)) (toℕ≤pred[n] i)

------------------------------------------------------------------------
-- fromℕ<
------------------------------------------------------------------------

fromℕ<-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i ℕ.< m) → fromℕ< i<m ≡ i
fromℕ<-toℕ zero    z<s       = refl
fromℕ<-toℕ (suc i) (s<s m<n) = cong suc (fromℕ<-toℕ i m<n)

toℕ-fromℕ< : ∀ {m n} (m<n : m ℕ.< n) → toℕ (fromℕ< m<n) ≡ m
toℕ-fromℕ< z<s               = refl
toℕ-fromℕ< (s<s m<n@(s≤s _)) = cong suc (toℕ-fromℕ< m<n)

-- fromℕ is a special case of fromℕ<.
fromℕ-def : ∀ n → fromℕ n ≡ fromℕ< ℕₚ.≤-refl
fromℕ-def zero    = refl
fromℕ-def (suc n) = cong suc (fromℕ-def n)

fromℕ<-cong : ∀ m n {o} → m ≡ n →
              (m<o : m ℕ.< o) →
              (n<o : n ℕ.< o) →
              fromℕ< m<o ≡ fromℕ< n<o
fromℕ<-cong 0       0       r z<s       z<s  = refl
fromℕ<-cong (suc _) (suc _) r (s<s m<n) (s<s n<o)
  = cong suc (fromℕ<-cong _ _ (ℕₚ.suc-injective r) m<n n<o)

fromℕ<-injective : ∀ m n {o} →
                   (m<o : m ℕ.< o) →
                   (n<o : n ℕ.< o) →
                   fromℕ< m<o ≡ fromℕ< n<o →
                   m ≡ n
fromℕ<-injective 0       0       z<s               z<s r = refl
fromℕ<-injective (suc _) (suc _) (s<s m<n@(s≤s _)) (s<s n<o@(s≤s _)) r
  = cong suc (fromℕ<-injective _ _ m<n n<o (suc-injective r))

------------------------------------------------------------------------
-- fromℕ<″
------------------------------------------------------------------------

fromℕ<≡fromℕ<″ : ∀ {m n} (m<n : m ℕ.< n) (m<″n : m ℕ.<″ n) →
                 fromℕ< m<n ≡ fromℕ<″ m m<″n
fromℕ<≡fromℕ<″ z<s               (ℕ.less-than-or-equal refl) = refl
fromℕ<≡fromℕ<″ (s<s m<n@(s≤s _)) (ℕ.less-than-or-equal refl) =
  cong suc (fromℕ<≡fromℕ<″ m<n (ℕ.less-than-or-equal refl))

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

≤-irrelevant : ∀ {m n} → Irrelevant (_≤_ {m} {n})
≤-irrelevant = ℕₚ.≤-irrelevant

infix 4 _≤?_ _<?_

_≤?_ : ∀ {m n} → B.Decidable (_≤_ {m} {n})
a ≤? b = toℕ a ℕₚ.≤? toℕ b

_<?_ : ∀ {m n} → B.Decidable (_<_ {m} {n})
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
<-cmp zero    zero    = tri≈ (λ()) refl  (λ())
<-cmp zero    (suc j) = tri< z<s   (λ()) (λ())
<-cmp (suc i) zero    = tri> (λ()) (λ()) z<s
<-cmp (suc i) (suc j) with <-cmp i j
... | tri< i<j i≢j j≮i = tri< (s<s i<j)         (i≢j ∘ suc-injective) (j≮i ∘ ℕₚ.≤-pred)
... | tri> i≮j i≢j j<i = tri> (i≮j ∘ ℕₚ.≤-pred) (i≢j ∘ suc-injective) (s<s j<i)
... | tri≈ i≮j i≡j j≮i = tri≈ (i≮j ∘ ℕₚ.≤-pred) (cong suc i≡j)        (j≮i ∘ ℕₚ.≤-pred)

<-respˡ-≡ : ∀ {m n} → (_<_ {m} {n}) Respectsˡ _≡_
<-respˡ-≡ refl x≤y = x≤y

<-respʳ-≡ : ∀ {m n} → (_<_ {m} {n}) Respectsʳ _≡_
<-respʳ-≡ refl x≤y = x≤y

<-resp₂-≡ : ∀ {n} → (_<_ {n}) Respects₂ _≡_
<-resp₂-≡ = <-respʳ-≡ , <-respˡ-≡

<-irrelevant : ∀ {m n} → Irrelevant (_<_ {m} {n})
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

i<1+i : ∀ {n} (i : Fin n) → i < suc i
i<1+i = ℕₚ.n<1+n ∘ toℕ

<⇒≢ : ∀ {n} {i j : Fin n} → i < j → i ≢ j
<⇒≢ i<i refl = ℕₚ.n≮n _ i<i

≤∧≢⇒< : ∀ {n} {i j : Fin n} → i ≤ j → i ≢ j → i < j
≤∧≢⇒< {i = zero}  {zero}  _         0≢0     = contradiction refl 0≢0
≤∧≢⇒< {i = zero}  {suc j} _         _       = z<s
≤∧≢⇒< {i = suc i} {suc j} (s≤s i≤j) 1+i≢1+j =
  s<s (≤∧≢⇒< i≤j (1+i≢1+j ∘ (cong suc)))

------------------------------------------------------------------------
-- inject
------------------------------------------------------------------------

toℕ-inject : ∀ {n} {i : Fin n} (j : Fin′ i) →
             toℕ (inject j) ≡ toℕ j
toℕ-inject {i = suc i} zero    = refl
toℕ-inject {i = suc i} (suc j) = cong suc (toℕ-inject j)

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
≤̄⇒inject₁< {i = i} {j} p = subst (ℕ._< toℕ (suc i)) (sym (toℕ-inject₁ j)) (s<s p)

ℕ<⇒inject₁< : ∀ {n} → {i : Fin (ℕ.suc n)} → {j : Fin n} →
              toℕ j ℕ.< toℕ i → inject₁ j < i
ℕ<⇒inject₁< {i = suc i} (s≤s j≤i) = ≤̄⇒inject₁< j≤i

------------------------------------------------------------------------
-- lower₁
------------------------------------------------------------------------

toℕ-lower₁ : ∀ {m} x → (p : m ≢ toℕ x) → toℕ (lower₁ x p) ≡ toℕ x
toℕ-lower₁ {ℕ.zero} zero p     = contradiction refl p
toℕ-lower₁ {ℕ.suc m} zero p    = refl
toℕ-lower₁ {ℕ.suc m} (suc x) p = cong ℕ.suc (toℕ-lower₁ x (p ∘ cong ℕ.suc))

lower₁-injective : ∀ {n} {i j} {n≢i : n ≢ toℕ i} {n≢j : n ≢ toℕ j} →
                   lower₁ i n≢i ≡ lower₁ j n≢j → i ≡ j
lower₁-injective {zero}  {zero}  {_}     {n≢i} {_}   _ = ⊥-elim (n≢i refl)
lower₁-injective {zero}  {_}     {zero}  {_}   {n≢j} _ = ⊥-elim (n≢j refl)
lower₁-injective {suc n} {0F}    {0F}    {_}   {_}   refl = refl
lower₁-injective {suc n} {suc i} {suc j} {n≢i} {n≢j} eq =
  cong suc (lower₁-injective (suc-injective eq))

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

toℕ-inject≤ : ∀ {m n} (i : Fin m) (m≤n : m ℕ.≤ n) →
                toℕ (inject≤ i m≤n) ≡ toℕ i
toℕ-inject≤ {_} {suc n} zero    _         = refl
toℕ-inject≤ {_} {suc n} (suc i) (s≤s m≤n) = cong suc (toℕ-inject≤ i m≤n)

inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ.≤ n) → inject≤ i n≤n ≡ i
inject≤-refl {suc n} zero    _   = refl
inject≤-refl {suc n} (suc i) (s≤s n≤n) = cong suc (inject≤-refl i n≤n)

inject≤-idempotent : ∀ {m n k} (i : Fin m)
                     (m≤n : m ℕ.≤ n) (n≤k : n ℕ.≤ k) (m≤k : m ℕ.≤ k) →
                     inject≤ (inject≤ i m≤n) n≤k ≡ inject≤ i m≤k
inject≤-idempotent {_} {suc n} {suc k} zero    _   _   _ = refl
inject≤-idempotent {_} {suc n} {suc k} (suc i) (s≤s m≤n) (s≤s n≤k) (s≤s m≤k) =
  cong suc (inject≤-idempotent i m≤n n≤k m≤k)

inject≤-injective : ∀ {n m} (n≤m n≤m′ : n ℕ.≤ m) x y → inject≤ x n≤m ≡ inject≤ y n≤m′ → x ≡ y
inject≤-injective (s≤s p) (s≤s q) zero zero eq = refl
inject≤-injective (s≤s p) (s≤s q) (suc x) (suc y) eq =
  cong suc (inject≤-injective p q x y (suc-injective eq))

------------------------------------------------------------------------
-- pred
------------------------------------------------------------------------

pred< : ∀ {n} → (i : Fin (suc n)) → i ≢ zero → pred i < i
pred< zero p = contradiction refl p
pred< (suc i) p = ≤̄⇒inject₁< ℕₚ.≤-refl

------------------------------------------------------------------------
-- splitAt
------------------------------------------------------------------------

-- Fin (m + n) ↔ Fin m ⊎ Fin n

splitAt-↑ˡ : ∀ m i n → splitAt m (i ↑ˡ n) ≡ inj₁ i
splitAt-↑ˡ (suc m) zero    n = refl
splitAt-↑ˡ (suc m) (suc i) n rewrite splitAt-↑ˡ m i n = refl

splitAt-↑ʳ : ∀ m n i → splitAt m (m ↑ʳ i) ≡ inj₂ {B = Fin n} i
splitAt-↑ʳ zero    n i = refl
splitAt-↑ʳ (suc m) n i rewrite splitAt-↑ʳ m n i = refl

splitAt-join : ∀ m n i → splitAt m (join m n i) ≡ i
splitAt-join m n (inj₁ x) = splitAt-↑ˡ m x n
splitAt-join m n (inj₂ y) = splitAt-↑ʳ m n y

join-splitAt : ∀ m n i → join m n (splitAt m i) ≡ i
join-splitAt zero    n i       = refl
join-splitAt (suc m) n zero    = refl
join-splitAt (suc m) n (suc i) = begin
  [ _↑ˡ n , (suc m) ↑ʳ_ ]′ (splitAt (suc m) (suc i)) ≡⟨ [,]-map-commute (splitAt m i) ⟩
  [ suc ∘ (_↑ˡ n) , suc ∘ (m ↑ʳ_) ]′ (splitAt m i)   ≡˘⟨ [,]-∘-distr suc (splitAt m i) ⟩
  suc ([ _↑ˡ n , m ↑ʳ_ ]′ (splitAt m i))             ≡⟨ cong suc (join-splitAt m n i) ⟩
  suc i                                                         ∎
  where open ≡-Reasoning

-- splitAt "m" "i" ≡ inj₁ "i" if i < m

splitAt-< : ∀ m {n} i → (i<m : toℕ i ℕ.< m) → splitAt m {n} i ≡ inj₁ (fromℕ< i<m)
splitAt-< (suc m) zero    z<s               = refl
splitAt-< (suc m) (suc i) (s<s i<m) = cong (Sum.map suc id) (splitAt-< m i i<m)

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

remQuot-combine : ∀ {n k} (i : Fin n) j → remQuot k (combine i j) ≡ (i , j)
remQuot-combine {suc n} {k} 0F j rewrite splitAt-↑ˡ k j (n ℕ.* k) = refl
remQuot-combine {suc n} {k} (suc i) j rewrite splitAt-↑ʳ k (n ℕ.* k) (combine i j) = cong (Data.Product.map₁ suc) (remQuot-combine i j)

combine-remQuot : ∀ {n} k (i : Fin (n ℕ.* k)) → uncurry combine (remQuot {n} k i) ≡ i
combine-remQuot {suc n} k i with splitAt k i | P.inspect (splitAt k) i
... | inj₁ j | P.[ eq ] = begin
  join k (n ℕ.* k) (inj₁ j)      ≡˘⟨ cong (join k (n ℕ.* k)) eq ⟩
  join k (n ℕ.* k) (splitAt k i) ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                              ∎
  where open ≡-Reasoning
... | inj₂ j | P.[ eq ] = begin
  k ↑ʳ (uncurry combine (remQuot {n} k j)) ≡⟨ cong (k ↑ʳ_) (combine-remQuot {n} k j) ⟩
  join k (n ℕ.* k) (inj₂ j)                ≡˘⟨ cong (join k (n ℕ.* k)) eq ⟩
  join k (n ℕ.* k) (splitAt k i)           ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                                        ∎
  where open ≡-Reasoning

toℕ-combine : ∀ {n m} (i : Fin n) (j : Fin m) → toℕ (combine i j) ≡ m ℕ.* toℕ i ℕ.+ toℕ j
toℕ-combine {n = suc n} {m} i@0F j = begin
  toℕ (combine i j)          ≡⟨⟩
  toℕ (j ↑ˡ (n ℕ.* m))       ≡⟨ toℕ-↑ˡ j (n ℕ.* m) ⟩
  toℕ j                      ≡⟨⟩
  0 ℕ.+ toℕ j                ≡˘⟨ cong (ℕ._+ toℕ j) (ℕₚ.*-zeroʳ m) ⟩
  m ℕ.* toℕ i ℕ.+ toℕ j      ∎
  where open ≡-Reasoning
toℕ-combine {n = suc n} {m} (suc i) j = begin
  toℕ (combine (suc i) j)        ≡⟨⟩
  toℕ (m ↑ʳ combine i j)         ≡⟨ toℕ-↑ʳ m (combine i j) ⟩
  m ℕ.+ toℕ (combine i j)        ≡⟨ cong (m ℕ.+_) (toℕ-combine i j) ⟩
  m ℕ.+ (m ℕ.* toℕ i ℕ.+ toℕ j)  ≡⟨ solve 3 (λ m i j → m :+ (m :* i :+ j) := m :* (con 1 :+ i) :+ j) refl m (toℕ i) (toℕ j) ⟩
  m ℕ.* toℕ (suc i) ℕ.+ toℕ j    ∎
  where
    open ≡-Reasoning
    open +-*-Solver

combine-injectiveˡ : ∀ {n m} (i j : Fin n) (k : Fin m) → combine i k ≡ combine j k → i ≡ j
combine-injectiveˡ {n} {m@(suc _)} i j k combine[i,k]≡combine[j,k] =
  toℕ-injective (ℕₚ.*-cancelˡ-≡ m (ℕₚ.+-cancelʳ-≡ (m ℕ.* toℕ i) (m ℕ.* toℕ j) (begin
    m ℕ.* toℕ i ℕ.+ toℕ k      ≡˘⟨ toℕ-combine i k ⟩
    toℕ (combine i k)          ≡⟨ cong toℕ combine[i,k]≡combine[j,k] ⟩
    toℕ (combine j k)          ≡⟨ toℕ-combine j k ⟩
    m ℕ.* toℕ j ℕ.+ toℕ k      ∎)))
  where open ≡-Reasoning

combine-injectiveʳ : ∀ {n m} (i : Fin n) (j k : Fin m) → combine i j ≡ combine i k → j ≡ k
combine-injectiveʳ {n} {m} i j k combine[i,k]≡combine[j,k] = toℕ-injective (ℕₚ.+-cancelˡ-≡ (m ℕ.* toℕ i) (begin
  m ℕ.* toℕ i ℕ.+ toℕ j ≡˘⟨ toℕ-combine i j ⟩
  toℕ (combine i j)     ≡⟨ cong toℕ combine[i,k]≡combine[j,k] ⟩
  toℕ (combine i k)     ≡⟨ toℕ-combine i k ⟩
  m ℕ.* toℕ i ℕ.+ toℕ k ∎))
  where open ≡-Reasoning

combine-injective : ∀ {n m} (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) → combine i j ≡ combine k l → i ≡ k × j ≡ l
combine-injective i j k l combine[i,j]≡combine[k,l] =
  lemma₂ i j k l combine[i,j]≡combine[k,l] , lemma₃ i j k l combine[i,j]≡combine[k,l]
  where
    lemma₁ : ∀ {n m} (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) → i < k → combine i j < combine k l
    lemma₁ {n} {m} i j k l i<k = begin-strict
      toℕ (combine i j)      ≡⟨ toℕ-combine i j ⟩
      m ℕ.* toℕ i ℕ.+ toℕ j  <⟨ ℕₚ.+-monoʳ-< (m ℕ.* toℕ i) (toℕ<n j) ⟩
      m ℕ.* toℕ i ℕ.+ m      ≡⟨ ℕₚ.+-comm _ m ⟩
      m ℕ.+ m ℕ.* toℕ i      ≡⟨ cong (m ℕ.+_) (ℕₚ.*-comm m _) ⟩
      m ℕ.+ toℕ i ℕ.* m      ≡⟨ ℕₚ.*-comm (suc (toℕ i)) m ⟩
      m ℕ.* suc (toℕ i)      ≤⟨ ℕₚ.*-monoʳ-≤ m (toℕ-mono-< i<k) ⟩
      m ℕ.* toℕ k            ≤⟨ ℕₚ.m≤m+n (m ℕ.* toℕ k) (toℕ l) ⟩
      m ℕ.* toℕ k ℕ.+ toℕ l  ≡˘⟨ toℕ-combine k l ⟩
      toℕ (combine k l)      ∎
      where
        open ℕₚ.≤-Reasoning
        open +-*-Solver

    lemma₂ : ∀ {n m} (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) → combine i j ≡ combine k l → i ≡ k
    lemma₂ i j k l combine[i,j]≡combine[k,l] with <-cmp i k
    ... | tri< i<k _ _ = contradiction combine[i,j]≡combine[k,l] (<⇒≢ (lemma₁ i j k l i<k))
    ... | tri≈ _ i≡k _ = i≡k
    ... | tri> _ _ i>k = contradiction (sym combine[i,j]≡combine[k,l]) (<⇒≢ (lemma₁ k l i j i>k))

    lemma₃ : ∀ {n m} (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) → combine i j ≡ combine k l → j ≡ l
    lemma₃ i j k l combine[i,j]≡combine[k,l] = combine-injectiveʳ i j l (begin
      combine i j ≡⟨ combine[i,j]≡combine[k,l] ⟩
      combine k l ≡˘⟨ cong (λ h → combine h l) (lemma₂ i j k l combine[i,j]≡combine[k,l]) ⟩
      combine i l ∎)
      where open ≡-Reasoning

combine-surjective : ∀ {n m} (i : Fin (n ℕ.* m)) → Σ[ j ∈ Fin n ] Σ[ k ∈ Fin m ] combine j k ≡ i
combine-surjective {n} {m} i with remQuot {n} m i | P.inspect (remQuot {n} m) i
... | j , k | P.[ eq ] = j , k , (begin
  combine j k                       ≡˘⟨ uncurry (cong₂ combine) (,-injective eq) ⟩
  uncurry combine (remQuot {n} m i) ≡⟨ combine-remQuot {n} m i ⟩
  i                                 ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Bundles

*↔× : ∀ {m n} → Fin (m ℕ.* n) ↔ (Fin m × Fin n)
*↔× {m} {n} = mk↔′ (remQuot {m} n) (uncurry combine)
  (uncurry remQuot-combine)
  (combine-remQuot {m} n)

------------------------------------------------------------------------
-- fin→fun
------------------------------------------------------------------------

funToFin-finToFin : ∀ {m n} → funToFin {m} {n} ∘ finToFun ≗ id
funToFin-finToFin {zero}  {n} zero = refl
funToFin-finToFin {suc m} {n} k =
  begin
    combine (finToFun {suc m} {n} k zero) (funToFin (finToFun {suc m} {n} k ∘ suc))
  ≡⟨⟩
    combine (quotient {n} (n ^ m) k)
      (funToFin (finToFun {m} (remainder {n} (n ^ m) k)))
  ≡⟨ cong (combine (quotient {n} (n ^ m) k))
       (funToFin-finToFin {m} (remainder {n} (n ^ m) k)) ⟩
    combine (quotient {n} (n ^ m) k) (remainder {n} (n ^ m) k)
  ≡⟨⟩
    uncurry combine (remQuot {n} (n ^ m) k)
  ≡⟨ combine-remQuot {n = n} (n ^ m) k ⟩
    k
  ∎ where open ≡-Reasoning

finToFun-funToFin : ∀ {m n} (f : Fin m → Fin n) → finToFun (funToFin f) ≗ f
finToFun-funToFin {suc m} {n} f  zero   =
  begin
    quotient (n ^ m) (combine (f zero) (funToFin (f ∘ suc)))
  ≡⟨ cong proj₁ (remQuot-combine _ _) ⟩
    proj₁ (f zero , funToFin (f ∘ suc))
  ≡⟨⟩
    f zero
  ∎ where open ≡-Reasoning
finToFun-funToFin {suc m} {n} f (suc i) =
  begin
    finToFun (remainder {n} (n ^ m) (combine (f zero) (funToFin (f ∘ suc)))) i
  ≡⟨ cong (λ rq → finToFun (proj₂ rq) i) (remQuot-combine {n} _ _) ⟩
    finToFun (proj₂ (f zero , funToFin (f ∘ suc))) i
  ≡⟨⟩
    finToFun (funToFin (f ∘ suc)) i
  ≡⟨ finToFun-funToFin (f ∘ suc) i ⟩
    (f ∘ suc) i
  ≡⟨⟩
    f (suc i)
  ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Bundles

^↔→ : ∀ {m n} → Extensionality _ _ → Fin (n ^ m) ↔ (Fin m → Fin n)
^↔→ {m} {n} ext = mk↔′ finToFun funToFin
  (ext ∘ finToFun-funToFin)
  (funToFin-finToFin {m} {n})

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
<⇒≤pred {i = suc i} {zero}  z<s       = z≤n
<⇒≤pred {i = suc i} {suc j} (s<s j<i) =
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
  ∀-cons-⇔ = mk⇔ (uncurry ∀-cons) < _$ zero , _∘ suc >

  ∃-here : P zero → ∃⟨ P ⟩
  ∃-here = zero ,_

  ∃-there : ∃⟨ P ∘ suc ⟩ → ∃⟨ P ⟩
  ∃-there = map suc id

  ∃-toSum : ∃⟨ P ⟩ → P zero ⊎ ∃⟨ P ∘ suc ⟩
  ∃-toSum ( zero , P₀ ) = inj₁ P₀
  ∃-toSum (suc f , P₁₊) = inj₂ (f , P₁₊)

  ⊎⇔∃ : (P zero ⊎ ∃⟨ P ∘ suc ⟩) ⇔ ∃⟨ P ⟩
  ⊎⇔∃ = mk⇔ [ ∃-here , ∃-there ] ∃-toSum

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
pigeonhole z<s       f = contradiction (f zero) λ()
pigeonhole (s<s m<n@(s≤s _)) f with any? (λ k → f zero ≟ f (suc k))
... | yes (j , f₀≡fⱼ) = zero , suc j , (λ()) , f₀≡fⱼ
... | no  f₀≢fₖ with pigeonhole m<n (λ j → punchOut (f₀≢fₖ ∘ (j ,_ )))
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
-- Opposite
------------------------------------------------------------------------

opposite-prop : ∀ {n} → (i : Fin n) → toℕ (opposite i) ≡ n ∸ suc (toℕ i)
opposite-prop {suc n} zero = toℕ-fromℕ n
opposite-prop {suc n} (suc i) = begin
  toℕ (inject₁ (opposite i)) ≡⟨ toℕ-inject₁ (opposite i) ⟩
  toℕ (opposite i)           ≡⟨ opposite-prop i ⟩
  n ∸ suc (toℕ i)            ∎
  where open ≡-Reasoning

opposite-involutive : ∀ {n} → Involutive {A = Fin n} _≡_ opposite
opposite-involutive {suc n} i = toℕ-injective (begin
  toℕ (opposite (opposite i)) ≡⟨ opposite-prop (opposite i) ⟩
  n ∸ (toℕ (opposite i))     ≡⟨ cong (n ∸_) (opposite-prop i) ⟩
  n ∸ (n ∸ (toℕ i))         ≡⟨ ℕₚ.m∸[m∸n]≡n (toℕ≤pred[n] i) ⟩
  toℕ i                     ∎)
  where open ≡-Reasoning

opposite-suc : ∀ {n} {i : Fin n} → toℕ (opposite (suc i)) ≡ toℕ (opposite i)
opposite-suc {n} {i} = begin
  toℕ (opposite (suc i))      ≡⟨ opposite-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ sym (opposite-prop i) ⟩
  toℕ (opposite i)            ∎
  where open ≡-Reasoning


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.5

inject+-raise-splitAt = join-splitAt
{-# WARNING_ON_USAGE inject+-raise-splitAt
"Warning: inject+-raise-splitAt was deprecated in v1.5.
Please use join-splitAt instead."
#-}

-- Version 2.0

toℕ-raise = toℕ-↑ʳ
{-# WARNING_ON_USAGE toℕ-raise
"Warning: toℕ-raise was deprecated in v2.0.
Please use toℕ-↑ʳ instead."
#-}
toℕ-inject+ : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (i ↑ˡ n)
toℕ-inject+ n i = sym (toℕ-↑ˡ i n)
{-# WARNING_ON_USAGE toℕ-inject+
"Warning: toℕ-inject+ was deprecated in v2.0.
Please use toℕ-↑ˡ instead.
NB argument order has been flipped:
the left-hand argument is the Fin m
the right-hand is the Nat index increment."
#-}
splitAt-inject+ : ∀ m n i → splitAt m (i ↑ˡ n) ≡ inj₁ i
splitAt-inject+ m n i = splitAt-↑ˡ m i n
{-# WARNING_ON_USAGE splitAt-inject+
"Warning: splitAt-inject+ was deprecated in v2.0.
Please use splitAt-↑ˡ instead.
NB argument order has been flipped."
#-}
splitAt-raise : ∀ m n i → splitAt m (m ↑ʳ i) ≡ inj₂ {B = Fin n} i
splitAt-raise = splitAt-↑ʳ
{-# WARNING_ON_USAGE splitAt-raise
"Warning: splitAt-raise was deprecated in v2.0.
Please use splitAt-↑ʳ instead."
#-}
Fin0↔⊥ : Fin 0 ↔ ⊥
Fin0↔⊥ = 0↔⊥
{-# WARNING_ON_USAGE Fin0↔⊥
"Warning: Fin0↔⊥ was deprecated in v2.0.
Please use 0↔⊥ instead."
#-}

