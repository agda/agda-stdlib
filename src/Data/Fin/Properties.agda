------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-} -- for deprecated _≺_ and _≻toℕ_ (issue #1726)

module Data.Fin.Properties where

open import Axiom.Extensionality.Propositional
open import Algebra.Definitions using (Involutive)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; s≤s; z≤n; z<s; s<s; s<s⁻¹; _∸_; _^_)
import Data.Nat.Properties as ℕ
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base as Product
  using (∃; ∃-syntax; ∃₂; _×_; _,_; map; proj₁; proj₂; uncurry; <_,_>)
open import Data.Product.Properties using (,-injective)
open import Data.Product.Algebra using (×-cong)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Sum.Properties using ([,]-map; [,]-∘)
open import Function.Base using (_∘_; id; _$_; flip; const; _$-; λ-)
open import Function.Bundles using (Injection; _↣_; _⇔_; _↔_; mk⇔; mk↔ₛ′)
open import Function.Definitions using (Injective; Surjective)
open import Function.Consequences.Propositional using (contraInjective)
import Function.Construct.Composition as Comp
open import Level using (Level)
open import Relation.Binary.Definitions
open import Relation.Binary.Core using (_⇒_; _Preserves_⟶_)
open import Relation.Binary.Bundles
  using (Preorder; Setoid; DecSetoid; Poset; TotalOrder; DecTotalOrder; StrictPartialOrder; StrictTotalOrder)
open import Relation.Binary.Structures
  using (IsDecEquivalence; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder; IsStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_)
open import Relation.Binary.PropositionalEquality.Properties as ≡
  using (module ≡-Reasoning)
open import Relation.Nullary.Decidable as Dec
  using (Dec; yes; no; map′)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)


private
  variable
    a : Level
    A : Set a
    m n o : ℕ
    i j : Fin n


------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

0≢1+n : zero ≢ suc i
0≢1+n ()

suc-injective : suc i ≡ suc j → i ≡ j
suc-injective refl = refl

infix 4 _≟_

_≟_ : DecidableEquality (Fin n)
zero  ≟ zero  = yes refl
zero  ≟ suc y = no λ()
suc x ≟ zero  = no λ()
suc x ≟ suc y = map′ (cong suc) suc-injective (x ≟ y)

------------------------------------------------------------------------
-- Structures

≡-isDecEquivalence : IsDecEquivalence {A = Fin n} _≡_
≡-isDecEquivalence = record
  { isEquivalence = ≡.isEquivalence
  ; _≟_           = _≟_
  }

------------------------------------------------------------------------
-- Bundles

≡-preorder : ℕ → Preorder _ _ _
≡-preorder n = ≡.preorder (Fin n)

≡-setoid : ℕ → Setoid _ _
≡-setoid n = ≡.setoid (Fin n)

≡-decSetoid : ℕ → DecSetoid _ _
≡-decSetoid n = record
  { isDecEquivalence = ≡-isDecEquivalence {n}
  }

------------------------------------------------------------------------
-- Reexport properties of Unary predicates on Fin
------------------------------------------------------------------------

open import Data.Fin.Relation.Unary.Base public
open import Data.Fin.Relation.Unary.Decidable public

------------------------------------------------------------------------
-- Fin
------------------------------------------------------------------------

¬Fin0 : ¬ Fin 0
¬Fin0 ()

nonZeroIndex : Fin n → ℕ.NonZero n
nonZeroIndex {n = suc _} _ = _

------------------------------------------------------------------------
-- Bundles

0↔⊥ : Fin 0 ↔ ⊥
0↔⊥ = mk↔ₛ′ ¬Fin0 (λ ()) (λ ()) (λ ())

1↔⊤ : Fin 1 ↔ ⊤
1↔⊤ = mk↔ₛ′ (λ { 0F → tt }) (λ { tt → 0F }) (λ { tt → refl }) λ { 0F → refl }

2↔Bool : Fin 2 ↔ Bool
2↔Bool = mk↔ₛ′ (λ { 0F → false; 1F → true }) (λ { false → 0F ; true → 1F })
  (λ { false → refl ; true → refl }) (λ { 0F → refl ; 1F → refl })

------------------------------------------------------------------------
-- toℕ
------------------------------------------------------------------------

toℕ-injective : toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {zero}  {}      {}      _
toℕ-injective {suc n} {zero}  {zero}  eq = refl
toℕ-injective {suc n} {suc i} {suc j} eq =
  cong suc (toℕ-injective (cong ℕ.pred eq))

toℕ-strengthen : ∀ (i : Fin n) → toℕ (strengthen i) ≡ toℕ i
toℕ-strengthen zero    = refl
toℕ-strengthen (suc i) = cong suc (toℕ-strengthen i)

------------------------------------------------------------------------
-- toℕ-↑ˡ: "i" ↑ˡ n = "i" in Fin (m + n)
------------------------------------------------------------------------

toℕ-↑ˡ : ∀ (i : Fin m) n → toℕ (i ↑ˡ n) ≡ toℕ i
toℕ-↑ˡ zero    n = refl
toℕ-↑ˡ (suc i) n = cong suc (toℕ-↑ˡ i n)

↑ˡ-injective : ∀ n (i j : Fin m) → i ↑ˡ n ≡ j ↑ˡ n → i ≡ j
↑ˡ-injective n zero zero refl = refl
↑ˡ-injective n (suc i) (suc j) eq =
  cong suc (↑ˡ-injective n i j (suc-injective eq))

------------------------------------------------------------------------
-- toℕ-↑ʳ: n ↑ʳ "i" = "n + i" in Fin (n + m)
------------------------------------------------------------------------

toℕ-↑ʳ : ∀ n (i : Fin m) → toℕ (n ↑ʳ i) ≡ n ℕ.+ toℕ i
toℕ-↑ʳ zero    i = refl
toℕ-↑ʳ (suc n) i = cong suc (toℕ-↑ʳ n i)

↑ʳ-injective : ∀ n (i j : Fin m) → n ↑ʳ i ≡ n ↑ʳ j → i ≡ j
↑ʳ-injective zero i i refl = refl
↑ʳ-injective (suc n) i j eq = ↑ʳ-injective n i j (suc-injective eq)

------------------------------------------------------------------------
-- toℕ and the ordering relations
------------------------------------------------------------------------

toℕ<n : ∀ (i : Fin n) → toℕ i ℕ.< n
toℕ<n {n = suc _} zero    = z<s
toℕ<n {n = suc _} (suc i) = s<s (toℕ<n i)

toℕ≤pred[n] : ∀ (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n] zero                 = z≤n
toℕ≤pred[n] (suc {n = suc n} i)  = s≤s (toℕ≤pred[n] i)

toℕ≤n : ∀ (i : Fin n) → toℕ i ℕ.≤ n
toℕ≤n {suc n} i = ℕ.m≤n⇒m≤1+n (toℕ≤pred[n] i)

-- A simpler implementation of toℕ≤pred[n],
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of toℕ≤pred[n],
-- it can be removed in favor of toℕ≤pred[n]′.
toℕ≤pred[n]′ : ∀ (i : Fin n) → toℕ i ℕ.≤ ℕ.pred n
toℕ≤pred[n]′ i = ℕ.<⇒≤pred (toℕ<n i)

toℕ-mono-< : i < j → toℕ i ℕ.< toℕ j
toℕ-mono-< i<j = i<j

toℕ-mono-≤ : i ≤ j → toℕ i ℕ.≤ toℕ j
toℕ-mono-≤ i≤j = i≤j

toℕ-cancel-≤ : toℕ i ℕ.≤ toℕ j → i ≤ j
toℕ-cancel-≤ i≤j = i≤j

toℕ-cancel-< : toℕ i ℕ.< toℕ j → i < j
toℕ-cancel-< i<j = i<j

------------------------------------------------------------------------
-- fromℕ
------------------------------------------------------------------------

toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = cong suc (toℕ-fromℕ n)

fromℕ-toℕ : ∀ (i : Fin n) → fromℕ (toℕ i) ≡ strengthen i
fromℕ-toℕ zero    = refl
fromℕ-toℕ (suc i) = cong suc (fromℕ-toℕ i)

≤fromℕ : ∀ (i : Fin (suc n)) → i ≤ fromℕ n
≤fromℕ {n = n} i rewrite toℕ-fromℕ n = ℕ.s≤s⁻¹ (toℕ<n i)

------------------------------------------------------------------------
-- fromℕ<
------------------------------------------------------------------------

fromℕ<-toℕ : ∀ (i : Fin n) .(i<n : toℕ i ℕ.< n) → fromℕ< i<n ≡ i
fromℕ<-toℕ zero    _   = refl
fromℕ<-toℕ (suc i) i<n = cong suc (fromℕ<-toℕ i (ℕ.s<s⁻¹ i<n))

toℕ-fromℕ< : ∀ .(m<n : m ℕ.< n) → toℕ (fromℕ< m<n) ≡ m
toℕ-fromℕ< {m = zero}  {n = suc _} _   = refl
toℕ-fromℕ< {m = suc m} {n = suc _} m<n = cong suc (toℕ-fromℕ< (ℕ.s<s⁻¹ m<n))

-- fromℕ is a special case of fromℕ<.
fromℕ-def : ∀ n → fromℕ n ≡ fromℕ< ℕ.≤-refl
fromℕ-def zero    = refl
fromℕ-def (suc n) = cong suc (fromℕ-def n)

fromℕ<-cong : ∀ m n {o} → m ≡ n → .(m<o : m ℕ.< o) .(n<o : n ℕ.< o) →
              fromℕ< m<o ≡ fromℕ< n<o
fromℕ<-cong 0       0                   _ _   _   = refl
fromℕ<-cong (suc _) (suc _) {o = suc _} r m<n n<o
  = cong suc (fromℕ<-cong _ _ (ℕ.suc-injective r) (ℕ.s<s⁻¹ m<n) (ℕ.s<s⁻¹ n<o))

fromℕ<-injective : ∀ m n {o} → .(m<o : m ℕ.< o) .(n<o : n ℕ.< o) →
                   fromℕ< m<o ≡ fromℕ< n<o → m ≡ n
fromℕ<-injective 0       0                   _   _   _  = refl
fromℕ<-injective 0       (suc _) {o = suc _} _ _ ()
fromℕ<-injective (suc _) (suc _) {o = suc _} m<n n<o r
  = cong suc (fromℕ<-injective _ _ (ℕ.s<s⁻¹ m<n) (ℕ.s<s⁻¹ n<o) (suc-injective r))

------------------------------------------------------------------------
-- fromℕ<″
------------------------------------------------------------------------

fromℕ<≡fromℕ<″ : ∀ (m<n : m ℕ.< n) (m<″n : m ℕ.<″ n) →
                 fromℕ< m<n ≡ fromℕ<″ m m<″n
fromℕ<≡fromℕ<″ {m = zero}  {n = suc _} _ _ = refl
fromℕ<≡fromℕ<″ {m = suc m} {n = suc _} m<n m<″n
  = cong suc (fromℕ<≡fromℕ<″ (ℕ.s<s⁻¹ m<n) (ℕ.s<″s⁻¹ m<″n))

toℕ-fromℕ<″ : ∀ (m<n : m ℕ.<″ n) → toℕ (fromℕ<″ m m<n) ≡ m
toℕ-fromℕ<″ {m} {n} m<n = begin
  toℕ (fromℕ<″ m m<n)  ≡⟨ cong toℕ (sym (fromℕ<≡fromℕ<″ (ℕ.≤″⇒≤ m<n) m<n)) ⟩
  toℕ (fromℕ< _)       ≡⟨ toℕ-fromℕ< (ℕ.≤″⇒≤ m<n) ⟩
  m                    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of cast
------------------------------------------------------------------------

toℕ-cast : ∀ .(eq : m ≡ n) (k : Fin m) → toℕ (cast eq k) ≡ toℕ k
toℕ-cast {n = suc n} eq zero    = refl
toℕ-cast {n = suc n} eq (suc k) = cong suc (toℕ-cast (cong ℕ.pred eq) k)

cast-is-id : .(eq : m ≡ m) (k : Fin m) → cast eq k ≡ k
cast-is-id eq zero    = refl
cast-is-id eq (suc k) = cong suc (cast-is-id (ℕ.suc-injective eq) k)

subst-is-cast : (eq : m ≡ n) (k : Fin m) → subst Fin eq k ≡ cast eq k
subst-is-cast refl k = sym (cast-is-id refl k)

cast-trans : .(eq₁ : m ≡ n) .(eq₂ : n ≡ o) (k : Fin m) →
             cast eq₂ (cast eq₁ k) ≡ cast (trans eq₁ eq₂) k
cast-trans {m = suc _} {n = suc _} {o = suc _} eq₁ eq₂ zero = refl
cast-trans {m = suc _} {n = suc _} {o = suc _} eq₁ eq₂ (suc k) =
  cong suc (cast-trans (ℕ.suc-injective eq₁) (ℕ.suc-injective eq₂) k)

cast-involutive : .(eq₁ : m ≡ n) .(eq₂ : n ≡ m) →
                  ∀ k → cast eq₁ (cast eq₂ k) ≡ k
cast-involutive eq₁ eq₂ k = trans (cast-trans eq₂ eq₁ k) (cast-is-id refl k)

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------
-- Relational properties

≤-reflexive : _≡_ ⇒ (_≤_ {n})
≤-reflexive refl = ℕ.≤-refl

≤-refl : Reflexive (_≤_ {n})
≤-refl = ≤-reflexive refl

≤-trans : Transitive (_≤_ {n})
≤-trans = ℕ.≤-trans

≤-antisym : Antisymmetric _≡_ (_≤_ {n})
≤-antisym x≤y y≤x = toℕ-injective (ℕ.≤-antisym x≤y y≤x)

≤-total : Total (_≤_ {n})
≤-total x y = ℕ.≤-total (toℕ x) (toℕ y)

≤-irrelevant : Irrelevant (_≤_ {m} {n})
≤-irrelevant = ℕ.≤-irrelevant

infix 4 _≤?_ _<?_

_≤?_ : Decidable (_≤_ {m} {n})
a ≤? b = toℕ a ℕ.≤? toℕ b

_<?_ : Decidable (_<_ {m} {n})
m <? n = suc (toℕ m) ℕ.≤? toℕ n

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder {A = Fin n} _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder {A = Fin n} _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder {A = Fin n} _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder {A = Fin n} _≡_ _≤_
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

<-irrefl : Irreflexive _≡_ (_<_ {n})
<-irrefl refl = ℕ.<-irrefl refl

<-asym : Asymmetric (_<_ {n})
<-asym = ℕ.<-asym

<-trans : Transitive (_<_ {n})
<-trans = ℕ.<-trans

<-cmp : Trichotomous _≡_ (_<_ {n})
<-cmp zero    zero    = tri≈ (λ()) refl  (λ())
<-cmp zero    (suc j) = tri< z<s   (λ()) (λ())
<-cmp (suc i) zero    = tri> (λ()) (λ()) z<s
<-cmp (suc i) (suc j) with <-cmp i j
... | tri< i<j i≢j j≮i = tri< (s<s i<j)     (i≢j ∘ suc-injective) (j≮i ∘ s<s⁻¹)
... | tri> i≮j i≢j j<i = tri> (i≮j ∘ s<s⁻¹) (i≢j ∘ suc-injective) (s<s j<i)
... | tri≈ i≮j i≡j j≮i = tri≈ (i≮j ∘ s<s⁻¹) (cong suc i≡j)        (j≮i ∘ s<s⁻¹)

<-respˡ-≡ : (_<_ {m} {n}) Respectsˡ _≡_
<-respˡ-≡ refl x≤y = x≤y

<-respʳ-≡ : (_<_ {m} {n}) Respectsʳ _≡_
<-respʳ-≡ refl x≤y = x≤y

<-resp₂-≡ : (_<_ {n}) Respects₂ _≡_
<-resp₂-≡ = <-respʳ-≡ , <-respˡ-≡

<-irrelevant : Irrelevant (_<_ {m} {n})
<-irrelevant = ℕ.<-irrelevant

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder : IsStrictPartialOrder {A = Fin n} _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≡.isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp₂-≡
  }

<-isStrictTotalOrder : IsStrictTotalOrder {A = Fin n} _≡_ _<_
<-isStrictTotalOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
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

i<1+i : ∀ (i : Fin n) → i < suc i
i<1+i = ℕ.n<1+n ∘ toℕ

<⇒≢ : i < j → i ≢ j
<⇒≢ i<i refl = ℕ.n≮n _ i<i

≤∧≢⇒< : i ≤ j → i ≢ j → i < j
≤∧≢⇒< {i = zero}  {zero}  _         0≢0   = contradiction refl 0≢0
≤∧≢⇒< {i = zero}  {suc j} _         _     = z<s
≤∧≢⇒< {i = suc i} {suc j} 1+i≤1+j 1+i≢1+j =
  s<s (≤∧≢⇒< (ℕ.s≤s⁻¹ 1+i≤1+j) (1+i≢1+j ∘ (cong suc)))

------------------------------------------------------------------------
-- inject
------------------------------------------------------------------------

toℕ-inject : ∀ {i : Fin n} (j : Fin′ i) → toℕ (inject j) ≡ toℕ j
toℕ-inject {i = suc i} zero    = refl
toℕ-inject {i = suc i} (suc j) = cong suc (toℕ-inject j)

------------------------------------------------------------------------
-- inject₁
------------------------------------------------------------------------

fromℕ≢inject₁ : fromℕ n ≢ inject₁ i
fromℕ≢inject₁ {i = suc i} eq = fromℕ≢inject₁ {i = i} (suc-injective eq)

inject₁-injective : inject₁ i ≡ inject₁ j → i ≡ j
inject₁-injective {i = zero}  {zero}  i≡j = refl
inject₁-injective {i = suc i} {suc j} i≡j =
  cong suc (inject₁-injective (suc-injective i≡j))

toℕ-inject₁ : ∀ (i : Fin n) → toℕ (inject₁ i) ≡ toℕ i
toℕ-inject₁ zero    = refl
toℕ-inject₁ (suc i) = cong suc (toℕ-inject₁ i)

toℕ-inject₁-≢ : ∀ (i : Fin n) → n ≢ toℕ (inject₁ i)
toℕ-inject₁-≢ (suc i) = toℕ-inject₁-≢ i ∘ ℕ.suc-injective

inject₁ℕ< : ∀ (i : Fin n) → toℕ (inject₁ i) ℕ.< n
inject₁ℕ< i rewrite toℕ-inject₁ i = toℕ<n i

inject₁ℕ≤ : ∀ (i : Fin n) → toℕ (inject₁ i) ℕ.≤ n
inject₁ℕ≤ = ℕ.<⇒≤ ∘ inject₁ℕ<

≤̄⇒inject₁< : i ≤ j → inject₁ i < suc j
≤̄⇒inject₁< {i = i} i≤j rewrite sym (toℕ-inject₁ i) = s<s i≤j

ℕ<⇒inject₁< : ∀ {i : Fin (ℕ.suc n)} {j : Fin n} → j < i → inject₁ j < i
ℕ<⇒inject₁< {i = suc i} j≤i = ≤̄⇒inject₁< (ℕ.s≤s⁻¹ j≤i)

i≤inject₁[j]⇒i≤1+j : i ≤ inject₁ j → i ≤ suc j
i≤inject₁[j]⇒i≤1+j {i = zero}              _   = z≤n
i≤inject₁[j]⇒i≤1+j {i = suc i} {j = suc j} i≤j = s≤s (ℕ.m≤n⇒m≤1+n (subst (toℕ i ℕ.≤_) (toℕ-inject₁ j) (ℕ.s≤s⁻¹ i≤j)))

------------------------------------------------------------------------
-- lower₁
------------------------------------------------------------------------

toℕ-lower₁ : ∀ i (p : n ≢ toℕ i) → toℕ (lower₁ i p) ≡ toℕ i
toℕ-lower₁ {ℕ.zero}  zero    p = contradiction refl p
toℕ-lower₁ {ℕ.suc m} zero    p = refl
toℕ-lower₁ {ℕ.suc m} (suc i) p = cong ℕ.suc (toℕ-lower₁ i (p ∘ cong ℕ.suc))

lower₁-injective : ∀ {n≢i : n ≢ toℕ i} {n≢j : n ≢ toℕ j} →
                   lower₁ i n≢i ≡ lower₁ j n≢j → i ≡ j
lower₁-injective {zero}  {zero}  {_}     {n≢i} {_}   _    = contradiction refl n≢i
lower₁-injective {zero}  {_}     {zero}  {_}   {n≢j} _    = contradiction refl n≢j
lower₁-injective {suc n} {zero}  {zero}  {_}   {_}   refl = refl
lower₁-injective {suc n} {suc i} {suc j} {n≢i} {n≢j} eq   =
  cong suc (lower₁-injective (suc-injective eq))

------------------------------------------------------------------------
-- inject₁ and lower₁

inject₁-lower₁ : ∀ (i : Fin (suc n)) (n≢i : n ≢ toℕ i) →
                 inject₁ (lower₁ i n≢i) ≡ i
inject₁-lower₁ {zero}  zero     0≢0     = contradiction refl 0≢0
inject₁-lower₁ {suc n} zero     _       = refl
inject₁-lower₁ {suc n} (suc i)  n+1≢i+1 =
  cong suc (inject₁-lower₁ i  (n+1≢i+1 ∘ cong suc))

lower₁-inject₁′ : ∀ (i : Fin n) (n≢i : n ≢ toℕ (inject₁ i)) →
                  lower₁ (inject₁ i) n≢i ≡ i
lower₁-inject₁′ zero    _       = refl
lower₁-inject₁′ (suc i) n+1≢i+1 =
  cong suc (lower₁-inject₁′ i (n+1≢i+1 ∘ cong suc))

lower₁-inject₁ : ∀ (i : Fin n) →
                 lower₁ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
lower₁-inject₁ i = lower₁-inject₁′ i (toℕ-inject₁-≢ i)

lower₁-irrelevant : ∀ (i : Fin (suc n)) (n≢i₁ n≢i₂ : n ≢ toℕ i) →
                    lower₁ i n≢i₁ ≡ lower₁ i n≢i₂
lower₁-irrelevant {zero}  zero     0≢0 _ = contradiction refl 0≢0
lower₁-irrelevant {suc n} zero     _   _ = refl
lower₁-irrelevant {suc n} (suc i)  _   _ =
  cong suc (lower₁-irrelevant i _ _)

inject₁≡⇒lower₁≡ : ∀ {i : Fin n} {j : Fin (ℕ.suc n)} →
                  (n≢j : n ≢ toℕ j) → inject₁ i ≡ j → lower₁ j n≢j ≡ i
inject₁≡⇒lower₁≡ n≢j i≡j = inject₁-injective (trans (inject₁-lower₁ _ n≢j) (sym i≡j))

------------------------------------------------------------------------
-- inject≤
------------------------------------------------------------------------

toℕ-inject≤ : ∀ i .(m≤n : m ℕ.≤ n) → toℕ (inject≤ i m≤n) ≡ toℕ i
toℕ-inject≤ {_} {suc n} zero    _ = refl
toℕ-inject≤ {_} {suc n} (suc i) _ = cong suc (toℕ-inject≤ i _)

inject≤-refl : ∀ i .(n≤n : n ℕ.≤ n) → inject≤ i n≤n ≡ i
inject≤-refl {suc n} zero    _   = refl
inject≤-refl {suc n} (suc i) _ = cong suc (inject≤-refl i _)

inject≤-idempotent : ∀ (i : Fin m)
                     .(m≤n : m ℕ.≤ n) .(n≤o : n ℕ.≤ o) .(m≤o : m ℕ.≤ o) →
                     inject≤ (inject≤ i m≤n) n≤o ≡ inject≤ i m≤o
inject≤-idempotent {_} {suc n} {suc o} zero    _ _ _ = refl
inject≤-idempotent {_} {suc n} {suc o} (suc i) _ _ _ =
  cong suc (inject≤-idempotent i _ _ _)

inject≤-trans : ∀ (i : Fin m) .(m≤n : m ℕ.≤ n) .(n≤o : n ℕ.≤ o) →
                inject≤ (inject≤ i m≤n) n≤o ≡ inject≤ i (ℕ.≤-trans m≤n n≤o)
inject≤-trans i _ _ = inject≤-idempotent i _ _ _

inject≤-injective : ∀ .(m≤n m≤n′ : m ℕ.≤ n) i j →
                    inject≤ i m≤n ≡ inject≤ j m≤n′ → i ≡ j
inject≤-injective {n = suc _} _ _ zero    zero    eq = refl
inject≤-injective {n = suc _} _ _ (suc i) (suc j) eq =
  cong suc (inject≤-injective _ _ i j (suc-injective eq))

inject≤-irrelevant : ∀ .(m≤n m≤n′ : m ℕ.≤ n) i →
                    inject≤ i m≤n ≡ inject≤ i m≤n′
inject≤-irrelevant _ _ i = refl

------------------------------------------------------------------------
-- pred
------------------------------------------------------------------------

pred< : ∀ (i : Fin (suc n)) → i ≢ zero → pred i < i
pred< zero    i≢0 = contradiction refl i≢0
pred< (suc i) _   = ≤̄⇒inject₁< ℕ.≤-refl

------------------------------------------------------------------------
-- splitAt
------------------------------------------------------------------------

-- Fin (m + n) ↔ Fin m ⊎ Fin n

splitAt-↑ˡ : ∀ m i n → splitAt m (i ↑ˡ n) ≡ inj₁ i
splitAt-↑ˡ (suc m) zero    n = refl
splitAt-↑ˡ (suc m) (suc i) n rewrite splitAt-↑ˡ m i n = refl

splitAt⁻¹-↑ˡ : ∀ {m} {n} {i} {j} → splitAt m {n} i ≡ inj₁ j → j ↑ˡ n ≡ i
splitAt⁻¹-↑ˡ {suc m} {n} {0F} {.0F} refl = refl
splitAt⁻¹-↑ˡ {suc m} {n} {suc i} {j} eq
  with inj₁ k ← splitAt m i in splitAt[m][i]≡inj₁[j]
  with refl ← eq
  = cong suc (splitAt⁻¹-↑ˡ {i = i} {j = k} splitAt[m][i]≡inj₁[j])

splitAt-↑ʳ : ∀ m n i → splitAt m (m ↑ʳ i) ≡ inj₂ {B = Fin n} i
splitAt-↑ʳ zero    n i = refl
splitAt-↑ʳ (suc m) n i rewrite splitAt-↑ʳ m n i = refl

splitAt⁻¹-↑ʳ : ∀ {m} {n} {i} {j} → splitAt m {n} i ≡ inj₂ j → m ↑ʳ j ≡ i
splitAt⁻¹-↑ʳ {zero}  {n} {i} {j} refl = refl
splitAt⁻¹-↑ʳ {suc m} {n} {suc i} {j} eq
  with inj₂ k ← splitAt m i in splitAt[m][i]≡inj₂[k]
  with refl ← eq
  = cong suc (splitAt⁻¹-↑ʳ {i = i} {j = k} splitAt[m][i]≡inj₂[k])

splitAt-join : ∀ m n i → splitAt m (join m n i) ≡ i
splitAt-join m n (inj₁ x) = splitAt-↑ˡ m x n
splitAt-join m n (inj₂ y) = splitAt-↑ʳ m n y

join-splitAt : ∀ m n i → join m n (splitAt m i) ≡ i
join-splitAt zero    n i       = refl
join-splitAt (suc m) n zero    = refl
join-splitAt (suc m) n (suc i) = begin
  [ _↑ˡ n , (suc m) ↑ʳ_ ]′ (splitAt (suc m) (suc i)) ≡⟨ [,]-map (splitAt m i) ⟩
  [ suc ∘ (_↑ˡ n) , suc ∘ (m ↑ʳ_) ]′ (splitAt m i)   ≡⟨ [,]-∘ suc (splitAt m i) ⟨
  suc ([ _↑ˡ n , m ↑ʳ_ ]′ (splitAt m i))             ≡⟨ cong suc (join-splitAt m n i) ⟩
  suc i                                                         ∎
  where open ≡-Reasoning

-- splitAt "m" "i" ≡ inj₁ "i" if i < m

splitAt-< : ∀ m {n} (i : Fin (m ℕ.+ n)) .(i<m : toℕ i ℕ.< m) →
            splitAt m i ≡ inj₁ (fromℕ< i<m)
splitAt-< (suc m) zero    _   = refl
splitAt-< (suc m) (suc i) i<m = cong (Sum.map suc id) (splitAt-< m i (ℕ.s<s⁻¹ i<m))

-- splitAt "m" "i" ≡ inj₂ "i - m" if i ≥ m

splitAt-≥ : ∀ m {n} (i : Fin (m ℕ.+ n)) .(i≥m : toℕ i ℕ.≥ m) →
            splitAt m i ≡ inj₂ (reduce≥ i i≥m)
splitAt-≥ zero    i       _   = refl
splitAt-≥ (suc m) (suc i) i≥m = cong (Sum.map suc id) (splitAt-≥ m i (ℕ.s≤s⁻¹ i≥m))

------------------------------------------------------------------------
-- Bundles

+↔⊎ : Fin (m ℕ.+ n) ↔ (Fin m ⊎ Fin n)
+↔⊎ {m} {n} = mk↔ₛ′ (splitAt m {n}) (join m n) (splitAt-join m n) (join-splitAt m n)

------------------------------------------------------------------------
-- remQuot
------------------------------------------------------------------------

-- Fin (m * n) ↔ Fin m × Fin n

remQuot-combine : ∀ {n k} (i : Fin n) j → remQuot k (combine i j) ≡ (i , j)
remQuot-combine {suc n} {k} zero    j rewrite splitAt-↑ˡ k j (n ℕ.* k) = refl
remQuot-combine {suc n} {k} (suc i) j rewrite splitAt-↑ʳ k   (n ℕ.* k) (combine i j) =
  cong (Product.map₁ suc) (remQuot-combine i j)

combine-remQuot : ∀ {n} k (i : Fin (n ℕ.* k)) → uncurry combine (remQuot {n} k i) ≡ i
combine-remQuot {suc n} k i with splitAt k i in eq
... | inj₁ j = begin
  join k (n ℕ.* k) (inj₁ j)      ≡⟨ cong (join k (n ℕ.* k)) eq ⟨
  join k (n ℕ.* k) (splitAt k i) ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                              ∎
  where open ≡-Reasoning
... | inj₂ j = begin
  k ↑ʳ (uncurry combine (remQuot {n} k j)) ≡⟨ cong (k ↑ʳ_) (combine-remQuot {n} k j) ⟩
  join k (n ℕ.* k) (inj₂ j)                ≡⟨ cong (join k (n ℕ.* k)) eq ⟨
  join k (n ℕ.* k) (splitAt k i)           ≡⟨ join-splitAt k (n ℕ.* k) i ⟩
  i                                        ∎
  where open ≡-Reasoning

toℕ-combine : ∀ (i : Fin m) (j : Fin n) → toℕ (combine i j) ≡ n ℕ.* toℕ i ℕ.+ toℕ j
toℕ-combine {suc m} {n} i@0F j = begin
  toℕ (combine i j)          ≡⟨⟩
  toℕ (j ↑ˡ (m ℕ.* n))       ≡⟨ toℕ-↑ˡ j (m ℕ.* n) ⟩
  toℕ j                      ≡⟨⟩
  0 ℕ.+ toℕ j                ≡⟨ cong (ℕ._+ toℕ j) (ℕ.*-zeroʳ n) ⟨
  n ℕ.* toℕ i ℕ.+ toℕ j      ∎
  where open ≡-Reasoning
toℕ-combine {suc m} {n} (suc i) j = begin
  toℕ (combine (suc i) j)            ≡⟨⟩
  toℕ (n ↑ʳ combine i j)             ≡⟨ toℕ-↑ʳ n (combine i j) ⟩
  n ℕ.+ toℕ (combine i j)            ≡⟨ cong (n ℕ.+_) (toℕ-combine i j) ⟩
  n ℕ.+ (n ℕ.* toℕ i ℕ.+ toℕ j)     ≡⟨ ℕ.+-assoc n _ (toℕ j) ⟨
  n ℕ.+ n ℕ.* toℕ i ℕ.+ toℕ j       ≡⟨ cong (λ z → z ℕ.+ n ℕ.* toℕ i ℕ.+ toℕ j) (ℕ.*-identityʳ n) ⟨
  n ℕ.* 1 ℕ.+ n ℕ.* toℕ i ℕ.+ toℕ j ≡⟨ cong (ℕ._+ toℕ j) (ℕ.*-distribˡ-+ n 1 (toℕ i) ) ⟨
  n ℕ.* toℕ (suc i) ℕ.+ toℕ j       ∎
  where open ≡-Reasoning

combine-monoˡ-< : ∀ {i j : Fin m} (k l : Fin n) →
                  i < j → combine i k < combine j l
combine-monoˡ-< {m} {n} {i} {j} k l i<j = begin-strict
  toℕ (combine i k)      ≡⟨ toℕ-combine i k ⟩
  n ℕ.* toℕ i ℕ.+ toℕ k  <⟨ ℕ.+-monoʳ-< (n ℕ.* toℕ i) (toℕ<n k) ⟩
  n ℕ.* toℕ i ℕ.+ n      ≡⟨ ℕ.+-comm _ n ⟩
  n ℕ.+ n ℕ.* toℕ i      ≡⟨ cong (n ℕ.+_) (ℕ.*-comm n _) ⟩
  n ℕ.+ toℕ i ℕ.* n      ≡⟨ ℕ.*-comm (suc (toℕ i)) n ⟩
  n ℕ.* suc (toℕ i)      ≤⟨ ℕ.*-monoʳ-≤ n (toℕ-mono-< i<j) ⟩
  n ℕ.* toℕ j            ≤⟨ ℕ.m≤m+n (n ℕ.* toℕ j) (toℕ l) ⟩
  n ℕ.* toℕ j ℕ.+ toℕ l  ≡⟨ toℕ-combine j l ⟨
  toℕ (combine j l)      ∎
  where open ℕ.≤-Reasoning

combine-injectiveˡ : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) →
                     combine i j ≡ combine k l → i ≡ k
combine-injectiveˡ i j k l cᵢⱼ≡cₖₗ with <-cmp i k
... | tri< i<k _ _ = contradiction cᵢⱼ≡cₖₗ (<⇒≢ (combine-monoˡ-< j l i<k))
... | tri≈ _ i≡k _ = i≡k
... | tri> _ _ i>k = contradiction (sym cᵢⱼ≡cₖₗ) (<⇒≢ (combine-monoˡ-< l j i>k))

combine-injectiveʳ : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) →
                     combine i j ≡ combine k l → j ≡ l
combine-injectiveʳ {m} {n} i j k l cᵢⱼ≡cₖₗ
  with refl ← combine-injectiveˡ i j k l cᵢⱼ≡cₖₗ
  = toℕ-injective (ℕ.+-cancelˡ-≡ (n ℕ.* toℕ i) _ _ (begin
  n ℕ.* toℕ i ℕ.+ toℕ j ≡⟨ toℕ-combine i j ⟨
  toℕ (combine i j)     ≡⟨ cong toℕ cᵢⱼ≡cₖₗ ⟩
  toℕ (combine i l)     ≡⟨ toℕ-combine i l ⟩
  n ℕ.* toℕ i ℕ.+ toℕ l ∎))
  where open ≡-Reasoning

combine-injective : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) →
                    combine i j ≡ combine k l → i ≡ k × j ≡ l
combine-injective i j k l cᵢⱼ≡cₖₗ =
  combine-injectiveˡ i j k l cᵢⱼ≡cₖₗ ,
  combine-injectiveʳ i j k l cᵢⱼ≡cₖₗ

combine-surjective : ∀ (i : Fin (m ℕ.* n)) → ∃₂ λ j k → combine j k ≡ i
combine-surjective {m} {n} i with j , k ← remQuot {m} n i in eq
  = j , k , (begin
  combine j k                       ≡⟨ uncurry (cong₂ combine) (,-injective eq) ⟨
  uncurry combine (remQuot {m} n i) ≡⟨ combine-remQuot {m} n i ⟩
  i                                 ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Bundles

*↔× : Fin (m ℕ.* n) ↔ (Fin m × Fin n)
*↔× {m} {n} = mk↔ₛ′ (remQuot {m} n) (uncurry combine)
  (uncurry remQuot-combine)
  (combine-remQuot {m} n)

------------------------------------------------------------------------
-- fin→fun
------------------------------------------------------------------------

funToFin-finToFin : funToFin {m} {n} ∘ finToFun ≗ id
funToFin-finToFin {zero}  {n} zero = refl
funToFin-finToFin {suc m} {n} k    =
  begin
    combine (finToFun {n} {suc m} k zero) (funToFin (finToFun {n} {suc m} k ∘ suc))
  ≡⟨⟩
    combine (quotient {n} (n ^ m) k)
      (funToFin (finToFun {n} {m} (remainder {n} (n ^ m) k)))
  ≡⟨ cong (combine (quotient {n} (n ^ m) k))
       (funToFin-finToFin {m} (remainder {n} (n ^ m) k)) ⟩
    combine (quotient {n} (n ^ m) k) (remainder {n} (n ^ m) k)
  ≡⟨⟩
    uncurry combine (remQuot {n} (n ^ m) k)
  ≡⟨ combine-remQuot {n = n} (n ^ m) k ⟩
    k
  ∎ where open ≡-Reasoning

finToFun-funToFin : (f : Fin m → Fin n) → finToFun (funToFin f) ≗ f
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

^↔→ : Extensionality _ _ → Fin (m ^ n) ↔ (Fin n → Fin m)
^↔→ {m} {n} ext = mk↔ₛ′ finToFun funToFin
  (ext ∘ finToFun-funToFin)
  (funToFin-finToFin {n} {m})

------------------------------------------------------------------------
-- lift
------------------------------------------------------------------------

lift-injective : ∀ (f : Fin m → Fin n) → Injective _≡_ _≡_ f →
                 ∀ k → Injective _≡_ _≡_ (lift k f)
lift-injective f inj zero    {_}     {_}     eq = inj eq
lift-injective f inj (suc k) {zero}  {zero}  eq = refl
lift-injective f inj (suc k) {suc _} {suc _} eq =
  cong suc (lift-injective f inj k (suc-injective eq))

------------------------------------------------------------------------
-- pred
------------------------------------------------------------------------

<⇒≤pred : i < j → i ≤ pred j
<⇒≤pred {i = zero}  {j = suc j} z<s       = z≤n
<⇒≤pred {i = suc i} {j = suc j} (s<s i<j) rewrite toℕ-inject₁ j = i<j

------------------------------------------------------------------------
-- _ℕ-_
------------------------------------------------------------------------

toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
toℕ‿ℕ- n       zero     = toℕ-fromℕ n
toℕ‿ℕ- (suc n) (suc i)  = toℕ‿ℕ- n i

------------------------------------------------------------------------
-- _ℕ-ℕ_
------------------------------------------------------------------------

ℕ-ℕ≡toℕ‿ℕ- : ∀ n i → n ℕ-ℕ i ≡ toℕ (n ℕ- i)
ℕ-ℕ≡toℕ‿ℕ- n       zero    = sym (toℕ-fromℕ n)
ℕ-ℕ≡toℕ‿ℕ- (suc n) (suc i) = ℕ-ℕ≡toℕ‿ℕ- n i

nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ.≤ n
nℕ-ℕi≤n n       zero     = ℕ.≤-refl
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i  ≤⟨ nℕ-ℕi≤n n i ⟩
  n        ≤⟨ ℕ.n≤1+n n ⟩
  suc n    ∎
  where open ℕ.≤-Reasoning

------------------------------------------------------------------------
-- punchIn
------------------------------------------------------------------------

punchIn-injective : ∀ i (j k : Fin n) →
                    punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective zero    _       _       refl      = refl
punchIn-injective (suc i) zero    zero    _         = refl
punchIn-injective (suc i) (suc j) (suc k) ↑j+1≡↑k+1 =
  cong suc (punchIn-injective i j k (suc-injective ↑j+1≡↑k+1))

punchInᵢ≢i : ∀ i (j : Fin n) → punchIn i j ≢ i
punchInᵢ≢i (suc i) (suc j) = punchInᵢ≢i i j ∘ suc-injective

------------------------------------------------------------------------
-- punchOut
------------------------------------------------------------------------

-- A version of 'cong' for 'punchOut' in which the inequality argument
-- can be changed out arbitrarily (reflecting the proof-irrelevance of
-- that argument).

punchOut-cong : ∀ (i : Fin (suc n)) {j k} {i≢j : i ≢ j} {i≢k : i ≢ k} →
                j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong {_}     zero    {zero}         {i≢j = 0≢0} = contradiction refl 0≢0
punchOut-cong {_}     zero    {suc j} {zero} {i≢k = 0≢0} = contradiction refl 0≢0
punchOut-cong {_}     zero    {suc j} {suc k}            = suc-injective
punchOut-cong {suc n} (suc i) {zero}  {zero}   _ = refl
punchOut-cong {suc n} (suc i) {suc j} {suc k}    = cong suc ∘ punchOut-cong i ∘ suc-injective

-- An alternative to 'punchOut-cong' in the which the new inequality
-- argument is specific. Useful for enabling the omission of that
-- argument during equational reasoning.

punchOut-cong′ : ∀ (i : Fin (suc n)) {j k} {p : i ≢ j} (q : j ≡ k) →
                 punchOut p ≡ punchOut (p ∘ sym ∘ trans q ∘ sym)
punchOut-cong′ i q = punchOut-cong i q

punchOut-injective : ∀ {i j k : Fin (suc n)}
                     (i≢j : i ≢ j) (i≢k : i ≢ k) →
                     punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-injective {_}     {zero}   {zero}  {_}     0≢0 _   _     = contradiction refl 0≢0
punchOut-injective {_}     {zero}   {_}     {zero}  _   0≢0 _     = contradiction refl 0≢0
punchOut-injective {_}     {zero}   {suc j} {suc k} _   _   pⱼ≡pₖ = cong suc pⱼ≡pₖ
punchOut-injective {suc n} {suc i}  {zero}  {zero}  _   _    _    = refl
punchOut-injective {suc n} {suc i}  {suc j} {suc k} i≢j i≢k pⱼ≡pₖ =
  cong suc (punchOut-injective (i≢j ∘ cong suc) (i≢k ∘ cong suc) (suc-injective pⱼ≡pₖ))

punchIn-punchOut : ∀ {i j : Fin (suc n)} (i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut {_}     {zero}   {zero}  0≢0 = contradiction refl 0≢0
punchIn-punchOut {_}     {zero}   {suc j} _   = refl
punchIn-punchOut {suc m} {suc i}  {zero}  i≢j = refl
punchIn-punchOut {suc m} {suc i}  {suc j} i≢j =
  cong suc (punchIn-punchOut (i≢j ∘ cong suc))

punchOut-punchIn : ∀ i {j : Fin n} → punchOut {i = i} {j = punchIn i j} (punchInᵢ≢i i j ∘ sym) ≡ j
punchOut-punchIn zero    {j}     = refl
punchOut-punchIn (suc i) {zero}  = refl
punchOut-punchIn (suc i) {suc j} = cong suc (begin
  punchOut (punchInᵢ≢i i j ∘ suc-injective ∘ sym ∘ cong suc)  ≡⟨ punchOut-cong i refl ⟩
  punchOut (punchInᵢ≢i i j ∘ sym)                             ≡⟨ punchOut-punchIn i ⟩
  j                                                           ∎)
  where open ≡-Reasoning


------------------------------------------------------------------------
-- pinch
------------------------------------------------------------------------

pinch-surjective : ∀ (i : Fin n) → Surjective _≡_ _≡_ (pinch i)
pinch-surjective _       zero    = zero , λ { refl → refl }
pinch-surjective zero    (suc j) = suc (suc j) , λ { refl → refl }
pinch-surjective (suc i) (suc j) = map suc (λ {f refl → cong suc (f refl)}) (pinch-surjective i j)

pinch-mono-≤ : ∀ (i : Fin n) → (pinch i) Preserves _≤_ ⟶ _≤_
pinch-mono-≤ 0F      {0F}    {k}     0≤n = z≤n
pinch-mono-≤ 0F      {suc j} {suc k} j≤k = ℕ.s≤s⁻¹ j≤k
pinch-mono-≤ (suc i) {0F}    {k}     0≤n = z≤n
pinch-mono-≤ (suc i) {suc j} {suc k} j≤k = s≤s (pinch-mono-≤ i (ℕ.s≤s⁻¹ j≤k))

pinch-injective : ∀ {i : Fin n} {j k : Fin (ℕ.suc n)} →
                  suc i ≢ j → suc i ≢ k → pinch i j ≡ pinch i k → j ≡ k
pinch-injective {i = i}     {zero}  {zero}  _     _     _  = refl
pinch-injective {i = zero}  {zero}  {suc k} _     1+i≢k eq =
  contradiction (cong suc eq) 1+i≢k
pinch-injective {i = zero}  {suc j} {zero}  1+i≢j _     eq =
  contradiction (cong suc (sym eq)) 1+i≢j
pinch-injective {i = zero}  {suc j} {suc k} _     _     eq =
  cong suc eq
pinch-injective {i = suc i} {suc j} {suc k} 1+i≢j 1+i≢k eq =
  cong suc
    (pinch-injective (1+i≢j ∘ cong suc) (1+i≢k ∘ cong suc)
      (suc-injective eq))

------------------------------------------------------------------------
-- Opposite
------------------------------------------------------------------------

opposite-prop : ∀ (i : Fin n) → toℕ (opposite i) ≡ n ∸ suc (toℕ i)
opposite-prop {suc n} zero    = toℕ-fromℕ n
opposite-prop {suc n} (suc i) = begin
  toℕ (inject₁ (opposite i)) ≡⟨ toℕ-inject₁ (opposite i) ⟩
  toℕ (opposite i)           ≡⟨ opposite-prop i ⟩
  n ∸ suc (toℕ i)            ∎
  where open ≡-Reasoning

opposite-involutive : Involutive {A = Fin n} _≡_ opposite
opposite-involutive {suc n} i = toℕ-injective (begin
  toℕ (opposite (opposite i)) ≡⟨ opposite-prop (opposite i) ⟩
  n ∸ (toℕ (opposite i))      ≡⟨ cong (n ∸_) (opposite-prop i) ⟩
  n ∸ (n ∸ (toℕ i))           ≡⟨ ℕ.m∸[m∸n]≡n (toℕ≤pred[n] i) ⟩
  toℕ i                       ∎)
  where open ≡-Reasoning

opposite-suc : ∀ (i : Fin n) → toℕ (opposite (suc i)) ≡ toℕ (opposite i)
opposite-suc {n} i = begin
  toℕ (opposite (suc i))     ≡⟨ opposite-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ opposite-prop i ⟨
  toℕ (opposite i)           ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of functions to and from Fin
------------------------------------------------------------------------

-- The pigeonhole principle.

pigeonhole : m ℕ.< n → (f : Fin n → Fin m) → ∃₂ λ i j → i < j × f i ≡ f j
pigeonhole z<s               f = contradiction (f zero) λ()
pigeonhole (s<s m<n@(s≤s _)) f with any? (λ k → f zero ≟ f (suc k))
... | yes (j , f₀≡fⱼ) = zero , suc j , z<s , f₀≡fⱼ
... | no  f₀≢fₖ       =
  let i , j , i<j , fᵢ≡fⱼ = pigeonhole m<n (λ j → punchOut (f₀≢fₖ ∘ (j ,_ )))
  in suc i , suc j , s<s i<j , punchOut-injective (f₀≢fₖ ∘ (i ,_)) _ fᵢ≡fⱼ

injective⇒≤ : ∀ {f : Fin m → Fin n} → Injective _≡_ _≡_ f → m ℕ.≤ n
injective⇒≤ {zero}  {_}     {f} _   = z≤n
injective⇒≤ {suc _} {zero}  {f} _   = contradiction (f zero) ¬Fin0
injective⇒≤ {suc _} {suc _} {f} inj = s≤s (injective⇒≤ (λ eq →
  suc-injective (inj (punchOut-injective
    (contraInjective inj 0≢1+n)
    (contraInjective inj 0≢1+n) eq))))

<⇒notInjective : ∀ {f : Fin m → Fin n} → n ℕ.< m → ¬ (Injective _≡_ _≡_ f)
<⇒notInjective n<m inj = ℕ.≤⇒≯ (injective⇒≤ inj) n<m

ℕ→Fin-notInjective : ∀ (f : ℕ → Fin n) → ¬ (Injective _≡_ _≡_ f)
ℕ→Fin-notInjective f inj = ℕ.<-irrefl refl
  (injective⇒≤ (Comp.injective _≡_ _≡_ _≡_ toℕ-injective inj))

-- Cantor-Schröder-Bernstein for finite sets

cantor-schröder-bernstein : ∀ {f : Fin m → Fin n} {g : Fin n → Fin m} →
                            Injective _≡_ _≡_ f → Injective _≡_ _≡_ g →
                            m ≡ n
cantor-schröder-bernstein f-inj g-inj = ℕ.≤-antisym
  (injective⇒≤ f-inj) (injective⇒≤ g-inj)

------------------------------------------------------------------------
-- If there is an injection from a type A to a finite set, then the type
-- has decidable equality.

module _ {ℓ} {S : Setoid a ℓ} (inj : Injection S (≡-setoid n)) where
  open Setoid S

  inj⇒≟ : Decidable _≈_
  inj⇒≟ = Dec.via-injection inj _≟_

  inj⇒decSetoid : DecSetoid a ℓ
  inj⇒decSetoid = record
    { isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = inj⇒≟
      }
    }


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
eq? : A ↣ Fin n → DecidableEquality A
eq? = inj⇒≟
{-# WARNING_ON_USAGE eq?
"Warning: eq? was deprecated in v2.0.
Please use inj⇒≟ instead."
#-}

private

  z≺s : ∀ {n} → zero ≺ suc n
  z≺s = _ ≻toℕ zero

  s≺s : ∀ {m n} → m ≺ n → suc m ≺ suc n
  s≺s (n ≻toℕ i) = (suc n) ≻toℕ (suc i)

  <⇒≺ : ℕ._<_ ⇒ _≺_
  <⇒≺ {zero}  z<s      = z≺s
  <⇒≺ {suc m} (s<s lt) = s≺s (<⇒≺ lt)

  ≺⇒< : _≺_ ⇒ ℕ._<_
  ≺⇒< (n ≻toℕ i) = toℕ<n i

≺⇒<′ : _≺_ ⇒ ℕ._<′_
≺⇒<′ lt = ℕ.<⇒<′ (≺⇒< lt)
{-# WARNING_ON_USAGE ≺⇒<′
"Warning: ≺⇒<′ was deprecated in v2.0.
Please use <⇒<′ instead."
#-}

<′⇒≺ : ℕ._<′_ ⇒ _≺_
<′⇒≺ lt = <⇒≺ (ℕ.<′⇒< lt)
{-# WARNING_ON_USAGE <′⇒≺
"Warning: <′⇒≺ was deprecated in v2.0.
Please use <′⇒< instead."
#-}
