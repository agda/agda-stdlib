-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unnormalized Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warning=noUserWarning #-} -- for +-rawMonoid, *-rawMonoid (issue #1865, #1844, #1755)

module Data.Rational.Unnormalised.Properties where

open import Algebra.Definitions
open import Algebra.Structures
  using (IsMagma; IsSemigroup; IsBand; IsSelectiveMagma; IsMonoid
        ; IsCommutativeMonoid; IsGroup; IsAbelianGroup; IsRing
        ; IsCommutativeRing)
open import Algebra.Bundles
open import Algebra.Apartness
  using (IsHeytingCommutativeRing; IsHeytingField
        ; HeytingCommutativeRing; HeytingField)
open import Algebra.Lattice
  using (IsLattice; IsDistributiveLattice; IsSemilattice
        ; Semilattice; Lattice; DistributiveLattice; RawLattice)
import Algebra.Consequences.Setoid as Consequences
open import Algebra.Consequences.Propositional
open import Algebra.Construct.NaturalChoice.Base
  using (MaxOperator; MinOperator)
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp as LatticeMinMaxOp
open import Data.Bool.Base using (T; true; false)
open import Data.Nat.Base as ℕ using (suc; pred)
import Data.Nat.Properties as ℕ
  using (≤-refl; +-comm; +-identityʳ; +-assoc
        ; *-identityʳ; *-comm; *-assoc; *-suc)
open import Data.Integer.Base as ℤ using (ℤ; +0; +[1+_]; -[1+_]; 0ℤ; 1ℤ; -1ℤ)
open import Data.Integer.DivMod using ([n/d]*d≤n; a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤ-solver)
import Data.Integer.Properties as ℤ
open import Data.Rational.Unnormalised.Base
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; [_,_]′; inj₁; inj₂)
import Data.Sign as Sign
open import Function.Base using (_on_; _$_; _∘_; flip)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable.Core as Dec using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Binary.Core using (_⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Bundles
  using (Setoid; DecSetoid; Preorder; TotalPreorder; Poset; TotalOrder
        ; DecTotalOrder; StrictPartialOrder; StrictTotalOrder; DenseLinearOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsDecEquivalence; IsApartnessRelation; IsTotalPreorder
        ; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder
        ; IsStrictPartialOrder; IsStrictTotalOrder; IsDenseLinearOrder)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; Cotransitive; Tight; Decidable
        ; Antisymmetric; Asymmetric; Dense; Total; Trans; Trichotomous
        ; Irreflexive; Irrelevant; _Respectsˡ_; _Respectsʳ_; _Respects₂_
        ; tri≈; tri<; tri>; Monotonic₁; LeftMonotonic; RightMonotonic; Monotonic₂)
import Relation.Binary.Consequences as BC
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Properties.Poset as PosetProperties
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Reasoning.Syntax

open import Algebra.Properties.CommutativeSemigroup ℤ.*-commutativeSemigroup

private
  variable
    p q r : ℚᵘ

------------------------------------------------------------------------
-- Properties of ↥_ and ↧_
------------------------------------------------------------------------

↥↧≡⇒≡ : ∀ {p q} → ↥ p ≡ ↥ q → ↧ₙ p ≡ ↧ₙ q → p ≡ q
↥↧≡⇒≡ {mkℚᵘ _ _} {mkℚᵘ _ _} refl refl = refl

------------------------------------------------------------------------
-- Properties of _/_
------------------------------------------------------------------------

/-cong : ∀ {n₁ d₁ n₂ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
         n₁ ≡ n₂ → d₁ ≡ d₂ → n₁ / d₁ ≡ n₂ / d₂
/-cong refl refl = refl

↥[n/d]≡n : ∀ n d .{{_ : ℕ.NonZero d}} → ↥ (n / d) ≡ n
↥[n/d]≡n n (suc d) = refl

↧[n/d]≡d : ∀ n d .{{_ : ℕ.NonZero d}} → ↧ (n / d) ≡ ℤ.+ d
↧[n/d]≡d n (suc d) = refl

------------------------------------------------------------------------
-- Properties of _≃_
------------------------------------------------------------------------

drop-*≡* : ∀ {p q} → p ≃ q → ↥ p ℤ.* ↧ q ≡ ↥ q ℤ.* ↧ p
drop-*≡* (*≡* eq) = eq

≃-refl : Reflexive _≃_
≃-refl = *≡* refl

≃-reflexive : _≡_ ⇒ _≃_
≃-reflexive refl = *≡* refl

≃-sym : Symmetric _≃_
≃-sym (*≡* eq) = *≡* (sym eq)

≃-trans : Transitive _≃_
≃-trans {x} {y} {z} (*≡* ad≡cb) (*≡* cf≡ed) =
  *≡* (ℤ.*-cancelʳ-≡ (↥ x ℤ.* ↧ z) (↥ z ℤ.* ↧ x) (↧ y) (begin
     ↥ x ℤ.* ↧ z ℤ.* ↧ y ≡⟨ xy∙z≈xz∙y (↥ x) _ _ ⟩
     ↥ x ℤ.* ↧ y ℤ.* ↧ z ≡⟨ cong (ℤ._* ↧ z) ad≡cb ⟩
     ↥ y ℤ.* ↧ x ℤ.* ↧ z ≡⟨ xy∙z≈xz∙y (↥ y) _ _ ⟩
     ↥ y ℤ.* ↧ z ℤ.* ↧ x ≡⟨ cong (ℤ._* ↧ x) cf≡ed ⟩
     ↥ z ℤ.* ↧ y ℤ.* ↧ x ≡⟨ xy∙z≈xz∙y (↥ z) _ _ ⟩
     ↥ z ℤ.* ↧ x ℤ.* ↧ y ∎))
  where open ≡-Reasoning

infix 4 _≃?_

_≃?_ : Decidable _≃_
p ≃? q = Dec.map′ *≡* drop-*≡* (↥ p ℤ.* ↧ q ℤ.≟ ↥ q ℤ.* ↧ p)

0≄1 : 0ℚᵘ ≄ 1ℚᵘ
0≄1 = Dec.from-no (0ℚᵘ ≃? 1ℚᵘ)

≃-≄-irreflexive : Irreflexive _≃_ _≄_
≃-≄-irreflexive x≃y x≄y = x≄y x≃y

≄-symmetric : Symmetric _≄_
≄-symmetric x≄y y≃x = x≄y (≃-sym y≃x)

≄-cotransitive : Cotransitive _≄_
≄-cotransitive {x} {y} x≄y z with x ≃? z | z ≃? y
... | no  x≄z | _       = inj₁ x≄z
... | yes _   | no z≄y  = inj₂ z≄y
... | yes x≃z | yes z≃y = contradiction (≃-trans x≃z z≃y) x≄y

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record
  { refl  = ≃-refl
  ; sym   = ≃-sym
  ; trans = ≃-trans
  }

≃-isDecEquivalence : IsDecEquivalence _≃_
≃-isDecEquivalence = record
  { isEquivalence = ≃-isEquivalence
  ; _≟_           = _≃?_
  }

≄-isApartnessRelation : IsApartnessRelation _≃_ _≄_
≄-isApartnessRelation = record
  { irrefl  = ≃-≄-irreflexive
  ; sym     = ≄-symmetric
  ; cotrans = ≄-cotransitive
  }

≄-tight : Tight _≃_ _≄_
proj₁ (≄-tight p q) ¬p≄q = Dec.decidable-stable (p ≃? q) ¬p≄q
proj₂ (≄-tight p q) p≃q p≄q = p≄q p≃q

≃-setoid : Setoid 0ℓ 0ℓ
≃-setoid = record
  { isEquivalence = ≃-isEquivalence
  }

≃-decSetoid : DecSetoid 0ℓ 0ℓ
≃-decSetoid = record
  { isDecEquivalence = ≃-isDecEquivalence
  }

module ≃-Reasoning = ≈-Reasoning ≃-setoid

↥p≡0⇒p≃0 : ∀ p → ↥ p ≡ 0ℤ → p ≃ 0ℚᵘ
↥p≡0⇒p≃0 p ↥p≡0 = *≡* (cong (ℤ._* (↧ 0ℚᵘ)) ↥p≡0)

p≃0⇒↥p≡0 : ∀ p → p ≃ 0ℚᵘ → ↥ p ≡ 0ℤ
p≃0⇒↥p≡0 p (*≡* eq) = begin
  ↥ p         ≡⟨ ℤ.*-identityʳ (↥ p) ⟨
  ↥ p ℤ.* 1ℤ  ≡⟨ eq ⟩
  0ℤ          ∎
  where open ≡-Reasoning

↥p≡↥q≡0⇒p≃q : ∀ p q → ↥ p ≡ 0ℤ → ↥ q ≡ 0ℤ → p ≃ q
↥p≡↥q≡0⇒p≃q p q ↥p≡0 ↥q≡0 = ≃-trans (↥p≡0⇒p≃0 p ↥p≡0) (≃-sym (↥p≡0⇒p≃0 _ ↥q≡0))


------------------------------------------------------------------------
-- Properties of -_
------------------------------------------------------------------------

neg-involutive-≡ : Involutive _≡_ (-_)
neg-involutive-≡ (mkℚᵘ n d) = cong (λ n → mkℚᵘ n d) (ℤ.neg-involutive n)

neg-involutive : Involutive _≃_ (-_)
neg-involutive p rewrite neg-involutive-≡ p = ≃-refl

-‿cong : Congruent₁ _≃_ (-_)
-‿cong {p@record{}} {q@record{}} (*≡* p≡q) = *≡* (begin
  ↥(- p) ℤ.* ↧ q            ≡⟨ ℤ.*-identityˡ (ℤ.- (↥ p) ℤ.* ↧ q) ⟨
  1ℤ ℤ.* (↥(- p) ℤ.* ↧ q)   ≡⟨ ℤ.*-assoc 1ℤ (↥ (- p)) (↧ q) ⟨
  (1ℤ ℤ.* ℤ.-(↥ p)) ℤ.* ↧ q ≡⟨ cong (ℤ._* ↧ q) (ℤ.neg-distribʳ-* 1ℤ (↥ p)) ⟨
  ℤ.-(1ℤ ℤ.* ↥ p) ℤ.* ↧ q   ≡⟨  cong (ℤ._* ↧ q) (ℤ.neg-distribˡ-* 1ℤ (↥ p)) ⟩
  (-1ℤ ℤ.* ↥ p) ℤ.* ↧ q     ≡⟨  ℤ.*-assoc ℤ.-1ℤ (↥ p) (↧ q) ⟩
  -1ℤ ℤ.* (↥ p ℤ.* ↧ q)     ≡⟨  cong (ℤ.-1ℤ ℤ.*_) p≡q ⟩
  -1ℤ ℤ.* (↥ q ℤ.* ↧ p)     ≡⟨ ℤ.*-assoc ℤ.-1ℤ (↥ q) (↧ p) ⟨
  (-1ℤ ℤ.* ↥ q) ℤ.* ↧ p     ≡⟨ cong (ℤ._* ↧ p) (ℤ.neg-distribˡ-* 1ℤ (↥ q)) ⟨
  ℤ.-(1ℤ ℤ.* ↥ q) ℤ.* ↧ p   ≡⟨  cong (ℤ._* ↧ p) (ℤ.neg-distribʳ-* 1ℤ (↥ q)) ⟩
  (1ℤ ℤ.* ↥(- q)) ℤ.* ↧ p   ≡⟨  ℤ.*-assoc 1ℤ (ℤ.- (↥ q)) (↧ p) ⟩
  1ℤ ℤ.* (↥(- q) ℤ.* ↧ p)   ≡⟨  ℤ.*-identityˡ (↥ (- q) ℤ.* ↧ p) ⟩
  ↥(- q) ℤ.* ↧ p            ∎)
  where open ≡-Reasoning

neg-mono-< : Monotonic₁  _<_ _>_ (-_)
neg-mono-< {p@record{}} {q@record{}} (*<* p<q) = *<* $ begin-strict
  ℤ.-  ↥ q ℤ.* ↧ p     ≡⟨ ℤ.neg-distribˡ-* (↥ q) (↧ p) ⟨
  ℤ.- (↥ q ℤ.* ↧ p)    <⟨ ℤ.neg-mono-< p<q ⟩
  ℤ.- (↥ p ℤ.* ↧ q)    ≡⟨ ℤ.neg-distribˡ-* (↥ p) (↧ q) ⟩
  ↥ (- p) ℤ.* ↧ (- q)  ∎
  where open ℤ.≤-Reasoning

neg-cancel-< : ∀ {p q} → - p < - q → q < p
neg-cancel-< {p@record{}} {q@record{}} (*<* -↥p↧q<-↥q↧p) = *<* $ begin-strict
  ↥ q ℤ.* ↧ p              ≡⟨ ℤ.neg-involutive (↥ q ℤ.* ↧ p) ⟨
  ℤ.- ℤ.- (↥ q ℤ.* ↧ p)    ≡⟨ cong ℤ.-_ (ℤ.neg-distribˡ-* (↥ q) (↧ p)) ⟩
  ℤ.- ((ℤ.- ↥ q) ℤ.* ↧ p)  <⟨ ℤ.neg-mono-< -↥p↧q<-↥q↧p ⟩
  ℤ.- ((ℤ.- ↥ p) ℤ.* ↧ q)  ≡⟨ cong ℤ.-_ (ℤ.neg-distribˡ-* (↥ p) (↧ q)) ⟨
  ℤ.- ℤ.- (↥ p ℤ.* ↧ q)    ≡⟨ ℤ.neg-involutive (↥ p ℤ.* ↧ q) ⟩
  ↥ p ℤ.* ↧ q              ∎
  where open ℤ.≤-Reasoning

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------
-- Relational properties

drop-*≤* : p ≤ q → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p)
drop-*≤* (*≤* pq≤qp) = pq≤qp

≤-reflexive : _≃_ ⇒ _≤_
≤-reflexive (*≡* eq) = *≤* (ℤ.≤-reflexive eq)

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive ≃-refl

≤-reflexive-≡ : _≡_ ⇒ _≤_
≤-reflexive-≡ refl = ≤-refl

≤-trans : Transitive _≤_
≤-trans {p} {q} {r} (*≤* eq₁) (*≤* eq₂)
  = let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r in *≤* $
  ℤ.*-cancelʳ-≤-pos (n₁ ℤ.* d₃) (n₃ ℤ.* d₁) d₂ $ begin
  (n₁  ℤ.* d₃) ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁   ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁   ℤ.* (d₂ ℤ.* d₃) ≡⟨ ℤ.*-assoc n₁ d₂ d₃ ⟨
  (n₁  ℤ.* d₂) ℤ.* d₃  ≤⟨ ℤ.*-monoʳ-≤-nonNeg d₃ eq₁ ⟩
  (n₂  ℤ.* d₁) ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  (d₁ ℤ.* n₂)  ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
  d₁  ℤ.* (n₂  ℤ.* d₃) ≤⟨ ℤ.*-monoˡ-≤-nonNeg d₁ eq₂ ⟩
  d₁  ℤ.* (n₃  ℤ.* d₂) ≡⟨ ℤ.*-assoc d₁ n₃ d₂ ⟨
  (d₁ ℤ.* n₃)  ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  (n₃  ℤ.* d₁) ℤ.* d₂  ∎ where open ℤ.≤-Reasoning

≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym (*≤* le₁) (*≤* le₂) = *≡* (ℤ.≤-antisym le₁ le₂)

≤-total : Total _≤_
≤-total p q = [ inj₁ ∘ *≤* , inj₂ ∘ *≤* ]′ (ℤ.≤-total
  (↥ p ℤ.* ↧ q)
  (↥ q ℤ.* ↧ p))

≤-respˡ-≃ : _≤_ Respectsˡ _≃_
≤-respˡ-≃ x≈y = ≤-trans (≤-reflexive (≃-sym x≈y))

≤-respʳ-≃ : _≤_ Respectsʳ _≃_
≤-respʳ-≃ x≈y z≤x = ≤-trans z≤x (≤-reflexive x≈y)

≤-resp₂-≃ : _≤_ Respects₂ _≃_
≤-resp₂-≃ = ≤-respʳ-≃ , ≤-respˡ-≃

infix 4 _≤?_ _≥?_

_≤?_ : Decidable _≤_
p ≤? q = Dec.map′ *≤* drop-*≤* (↥ p ℤ.* ↧ q ℤ.≤? ↥ q ℤ.* ↧ p)

_≥?_ : Decidable _≥_
_≥?_ = flip _≤?_

≤-irrelevant : Irrelevant _≤_
≤-irrelevant (*≤* p≤q₁) (*≤* p≤q₂) = cong *≤* (ℤ.≤-irrelevant p≤q₁ p≤q₂)

------------------------------------------------------------------------
-- Structures over _≃_

≤-isPreorder : IsPreorder _≃_ _≤_
≤-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isTotalPreorder : IsTotalPreorder _≃_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
  }

≤-isPartialOrder : IsPartialOrder _≃_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≃_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≃_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≃?_
  ; _≤?_         = _≤?_
  }

------------------------------------------------------------------------
-- Bundles over _≃_

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder = record
  { isTotalPreorder = ≤-isTotalPreorder
  }

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-totalOrder : TotalOrder 0ℓ 0ℓ 0ℓ
≤-totalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }

------------------------------------------------------------------------
-- Structures over _≡_

≤-isPreorder-≡ : IsPreorder _≡_ _≤_
≤-isPreorder-≡ = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive-≡
  ; trans         = ≤-trans
  }

≤-isTotalPreorder-≡ : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder-≡ = record
  { isPreorder = ≤-isPreorder-≡
  ; total      = ≤-total
  }

------------------------------------------------------------------------
-- Bundles over _≡_

≤-preorder-≡ : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder-≡ = record
  { isPreorder = ≤-isPreorder-≡
  }

≤-totalPreorder-≡ : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder-≡ = record
  { isTotalPreorder = ≤-isTotalPreorder-≡
  }

------------------------------------------------------------------------
-- Other properties of _≤_

mono⇒cong : ∀ {f} → Monotonic₁ _≤_ _≤_ f → Congruent₁ _≃_ f
mono⇒cong = BC.mono⇒cong _≃_ _≃_ ≃-sym ≤-reflexive ≤-antisym

antimono⇒cong : ∀ {f} → Monotonic₁ _≤_ _≥_ f → Congruent₁ _≃_ f
antimono⇒cong = BC.antimono⇒cong _≃_ _≃_ ≃-sym ≤-reflexive ≤-antisym

------------------------------------------------------------------------
-- Properties of _≤ᵇ_
------------------------------------------------------------------------

≤ᵇ⇒≤ : T (p ≤ᵇ q) → p ≤ q
≤ᵇ⇒≤ = *≤* ∘ ℤ.≤ᵇ⇒≤

≤⇒≤ᵇ : p ≤ q → T (p ≤ᵇ q)
≤⇒≤ᵇ = ℤ.≤⇒≤ᵇ ∘ drop-*≤*

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------

drop-*<* : p < q → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p)
drop-*<* (*<* pq<qp) = pq<qp

------------------------------------------------------------------------
-- Relationship between other operators

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤ.<⇒≤ p<q)

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ (*<* x<y) refl = ℤ.<⇒≢ x<y refl

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ (*<* x<y) = ℤ.<⇒≱ x<y ∘ drop-*≤*

≰⇒> : _≰_ ⇒ _>_
≰⇒> p≰q = *<* (ℤ.≰⇒> (p≰q ∘ *≤*))

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ p≮q = *≤* (ℤ.≮⇒≥ (p≮q ∘ *<*))

≰⇒≥ : _≰_ ⇒ _≥_
≰⇒≥ = <⇒≤ ∘ ≰⇒>

------------------------------------------------------------------------
-- Relational properties

<-irrefl-≡ : Irreflexive _≡_ _<_
<-irrefl-≡ refl (*<* x<x) = ℤ.<-irrefl refl x<x

<-irrefl : Irreflexive _≃_ _<_
<-irrefl (*≡* x≡y) (*<* x<y) = ℤ.<-irrefl x≡y x<y

<-asym : Asymmetric _<_
<-asym (*<* x<y) = ℤ.<-asym x<y ∘ drop-*<*

<-dense : Dense _<_
<-dense {p} {q} (*<* p<q) = m , p<m , m<q
  where
  open ℤ.≤-Reasoning
  m : ℚᵘ
  m = mkℚᵘ (↥ p ℤ.+ ↥ q) (pred (↧ₙ p ℕ.+ ↧ₙ q))

  p<m : p < m
  p<m = *<* (begin-strict
    ↥ p ℤ.* ↧ m
      ≡⟨⟩
    ↥ p ℤ.* (↧ p ℤ.+ ↧ q)
      ≡⟨ ℤ.*-distribˡ-+ (↥ p) (↧ p) (↧ q) ⟩
    ↥ p ℤ.* ↧ p ℤ.+ ↥ p ℤ.* ↧ q
      <⟨ ℤ.+-monoʳ-< (↥ p ℤ.* ↧ p) p<q ⟩
    ↥ p ℤ.* ↧ p ℤ.+ ↥ q ℤ.* ↧ p
      ≡⟨ ℤ.*-distribʳ-+ (↧ p) (↥ p) (↥ q) ⟨
    (↥ p ℤ.+ ↥ q) ℤ.* ↧ p
      ≡⟨⟩
    ↥ m ℤ.* ↧ p ∎)

  m<q : m < q
  m<q = *<* (begin-strict
    ↥ m ℤ.* ↧ q
      ≡⟨ ℤ.*-distribʳ-+ (↧ q) (↥ p) (↥ q) ⟩
    ↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ q
      <⟨ ℤ.+-monoˡ-< (↥ q ℤ.* ↧ q) p<q ⟩
    ↥ q ℤ.* ↧ p ℤ.+ ↥ q ℤ.* ↧ q
      ≡⟨ ℤ.*-distribˡ-+ (↥ q) (↧ p) (↧ q) ⟨
    ↥ q ℤ.* (↧ p ℤ.+ ↧ q)
      ≡⟨⟩
    ↥ q ℤ.* ↧ m ∎)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {p} {q} {r} (*≤* p≤q) (*<* q<r) = *<* $
  ℤ.*-cancelʳ-<-nonNeg _ $ begin-strict
  n₁ ℤ.*  d₃ ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁ ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁ ℤ.* (d₂ ℤ.* d₃) ≡⟨ ℤ.*-assoc n₁ d₂ d₃ ⟨
  n₁ ℤ.*  d₂ ℤ.* d₃  ≤⟨ ℤ.*-monoʳ-≤-nonNeg (↧ r) p≤q ⟩
  n₂ ℤ.*  d₁ ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  d₁ ℤ.*  n₂ ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
  d₁ ℤ.* (n₂ ℤ.* d₃) <⟨ ℤ.*-monoˡ-<-pos (↧ p) q<r ⟩
  d₁ ℤ.* (n₃ ℤ.* d₂) ≡⟨ ℤ.*-assoc d₁ n₃ d₂ ⟨
  d₁ ℤ.*  n₃ ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  n₃ ℤ.*  d₁ ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning
        n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {p} {q} {r} (*<* p<q) (*≤* q≤r) = *<* $
  ℤ.*-cancelʳ-<-nonNeg _ $ begin-strict
  n₁ ℤ.*  d₃ ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁ ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁ ℤ.* (d₂ ℤ.* d₃) ≡⟨ ℤ.*-assoc n₁ d₂ d₃ ⟨
  n₁ ℤ.*  d₂ ℤ.* d₃  <⟨ ℤ.*-monoʳ-<-pos (↧ r) p<q ⟩
  n₂ ℤ.*  d₁ ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  d₁ ℤ.*  n₂ ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
  d₁ ℤ.* (n₂ ℤ.* d₃) ≤⟨ ℤ.*-monoˡ-≤-nonNeg (↧ p) q≤r ⟩
  d₁ ℤ.* (n₃ ℤ.* d₂) ≡⟨ ℤ.*-assoc d₁ n₃ d₂ ⟨
  d₁ ℤ.*  n₃ ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  n₃ ℤ.*  d₁ ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning
        n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r

<-trans : Transitive _<_
<-trans = ≤-<-trans ∘ <⇒≤

<-cmp : Trichotomous _≃_ _<_
<-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
... | tri< x<y x≉y x≯y = tri< (*<* x<y) (x≉y ∘ drop-*≡*) (x≯y ∘ drop-*<*)
... | tri≈ x≮y x≈y x≯y = tri≈ (x≮y ∘ drop-*<*) (*≡* x≈y) (x≯y ∘ drop-*<*)
... | tri> x≮y x≉y x>y = tri> (x≮y ∘ drop-*<*) (x≉y ∘ drop-*≡*) (*<* x>y)

infix 4 _<?_ _>?_

_<?_ : Decidable _<_
p <? q = Dec.map′ *<* drop-*<* (↥ p ℤ.* ↧ q ℤ.<? ↥ q ℤ.* ↧ p)

_>?_ : Decidable _>_
_>?_ = flip _<?_

<-irrelevant : Irrelevant _<_
<-irrelevant (*<* p<q₁) (*<* p<q₂) = cong *<* (ℤ.<-irrelevant p<q₁ p<q₂)

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ {p} {q} {r} (*≡* q≡r) (*<* p<q) = *<* $
  ℤ.*-cancelʳ-<-nonNeg _ $ begin-strict
  n₁ ℤ.*  d₃ ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁ ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁ ℤ.* (d₂ ℤ.* d₃) ≡⟨ ℤ.*-assoc n₁ d₂ d₃ ⟨
  n₁ ℤ.*  d₂ ℤ.* d₃  <⟨ ℤ.*-monoʳ-<-pos (↧ r) p<q ⟩
  n₂ ℤ.*  d₁ ℤ.* d₃  ≡⟨ ℤ.*-assoc n₂ d₁ d₃ ⟩
  n₂ ℤ.* (d₁ ℤ.* d₃) ≡⟨ cong (n₂ ℤ.*_) (ℤ.*-comm d₁ d₃) ⟩
  n₂ ℤ.* (d₃ ℤ.* d₁) ≡⟨ ℤ.*-assoc n₂ d₃ d₁ ⟨
  n₂ ℤ.*  d₃ ℤ.* d₁  ≡⟨ cong (ℤ._* d₁) q≡r ⟩
  n₃ ℤ.*  d₂ ℤ.* d₁  ≡⟨ ℤ.*-assoc n₃ d₂ d₁ ⟩
  n₃ ℤ.* (d₂ ℤ.* d₁) ≡⟨ cong (n₃ ℤ.*_) (ℤ.*-comm d₂ d₁) ⟩
  n₃ ℤ.* (d₁ ℤ.* d₂) ≡⟨ ℤ.*-assoc n₃ d₁ d₂ ⟨
  n₃ ℤ.*  d₁ ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning
        n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r

<-respˡ-≃ : _<_ Respectsˡ _≃_
<-respˡ-≃ q≃r q<p
  = subst (_< _) (neg-involutive-≡ _)
  $ subst (_ <_) (neg-involutive-≡ _)
  $ neg-mono-< (<-respʳ-≃ (-‿cong q≃r) (neg-mono-< q<p))

<-resp-≃ : _<_ Respects₂ _≃_
<-resp-≃ = <-respʳ-≃ , <-respˡ-≃

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder-≡ : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder-≡ = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl-≡
  ; trans         = <-trans
  ; <-resp-≈      = subst (_ <_) , subst (_< _)
  }

<-isStrictPartialOrder : IsStrictPartialOrder _≃_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≃-isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp-≃
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≃_ _<_
<-isStrictTotalOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
  }

<-isDenseLinearOrder : IsDenseLinearOrder _≃_ _<_
<-isDenseLinearOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  ; dense              = <-dense
  }

------------------------------------------------------------------------
-- Bundles

<-strictPartialOrder-≡ : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder-≡ = record
  { isStrictPartialOrder = <-isStrictPartialOrder-≡
  }

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

<-denseLinearOrder : DenseLinearOrder 0ℓ 0ℓ 0ℓ
<-denseLinearOrder = record
  { isDenseLinearOrder = <-isDenseLinearOrder
  }

------------------------------------------------------------------------
-- A specialised module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-asym
    <-trans
    <-resp-≃
    <⇒≤
    <-≤-trans
    ≤-<-trans
    as Triple

  open Triple public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ≃-go)

  open ≃-syntax _IsRelatedTo_ _IsRelatedTo_ ≃-go ≃-sym public

------------------------------------------------------------------------
-- Properties of ↥_/↧_

≥0⇒↥≥0 : ∀ {n dm} → mkℚᵘ n dm ≥ 0ℚᵘ → n ℤ.≥ 0ℤ
≥0⇒↥≥0 {n} {dm} r≥0 = ℤ.≤-trans (drop-*≤* r≥0)
                                (ℤ.≤-reflexive $ ℤ.*-identityʳ n)

>0⇒↥>0 : ∀ {n dm} → mkℚᵘ n dm > 0ℚᵘ → n ℤ.> 0ℤ
>0⇒↥>0 {n} {dm} r>0 = ℤ.<-≤-trans (drop-*<* r>0)
                                  (ℤ.≤-reflexive $ ℤ.*-identityʳ n)

------------------------------------------------------------------------
-- Properties of sign predicates

positive⁻¹ : ∀ p → .{{Positive p}} → p > 0ℚᵘ
positive⁻¹ (mkℚᵘ +[1+ n ] _) = *<* (ℤ.+<+ ℕ.z<s)

nonNegative⁻¹ : ∀ p → .{{NonNegative p}} → p ≥ 0ℚᵘ
nonNegative⁻¹ (mkℚᵘ +0       _) = *≤* (ℤ.+≤+ ℕ.z≤n)
nonNegative⁻¹ (mkℚᵘ +[1+ n ] _) = *≤* (ℤ.+≤+ ℕ.z≤n)

negative⁻¹ : ∀ p → .{{Negative p}} → p < 0ℚᵘ
negative⁻¹ (mkℚᵘ -[1+ n ] _) = *<* ℤ.-<+

nonPositive⁻¹ : ∀ p → .{{NonPositive p}} → p ≤ 0ℚᵘ
nonPositive⁻¹ (mkℚᵘ +0       _) = *≤* (ℤ.+≤+ ℕ.z≤n)
nonPositive⁻¹ (mkℚᵘ -[1+ n ] _) = *≤* ℤ.-≤+

pos⇒nonNeg : ∀ p → .{{Positive p}} → NonNegative p
pos⇒nonNeg (mkℚᵘ +0       _) = _
pos⇒nonNeg (mkℚᵘ +[1+ n ] _) = _

neg⇒nonPos : ∀ p → .{{Negative p}} → NonPositive p
neg⇒nonPos (mkℚᵘ +0       _) = _
neg⇒nonPos (mkℚᵘ -[1+ n ] _) = _

neg<pos : ∀ p q → .{{Negative p}} → .{{Positive q}} → p < q
neg<pos p q = <-trans (negative⁻¹ p) (positive⁻¹ q)

pos⇒nonZero : ∀ p → .{{Positive p}} → NonZero p
pos⇒nonZero (mkℚᵘ (+[1+ _ ]) _) = _

nonNeg∧nonPos⇒0 : ∀ p → .{{NonNegative p}} → .{{NonPositive p}} → p ≃ 0ℚᵘ
nonNeg∧nonPos⇒0 (mkℚᵘ +0 _) = *≡* refl

nonNeg<⇒pos : ∀ {p q} .{{_ : NonNegative p}} → p < q → Positive q
nonNeg<⇒pos {p} p<q = positive (≤-<-trans (nonNegative⁻¹ p) p<q)

nonNeg≤⇒nonNeg : ∀ {p q} .{{_ : NonNegative p}} → p ≤ q → NonNegative q
nonNeg≤⇒nonNeg {p} p≤q = nonNegative (≤-trans (nonNegative⁻¹ p) p≤q)

neg⇒nonZero : ∀ p → .{{Negative p}} → NonZero p
neg⇒nonZero (mkℚᵘ (-[1+ _ ]) _) = _

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

-- Congruence

+-cong : Congruent₂ _≃_ _+_
+-cong {x@record{}} {y@record{}} {u@record{}} {v@record{}} (*≡* ab′∼a′b) (*≡* cd′∼c′d) = *≡* (begin
  (↥x ℤ.* ↧u ℤ.+ ↥u ℤ.* ↧x) ℤ.* (↧y ℤ.* ↧v)               ≡⟨ solve 6 (λ ↥x ↧x ↧y ↥u ↧u ↧v →
                                                             (↥x :* ↧u :+ ↥u :* ↧x) :* (↧y :* ↧v) :=
                                                             (↥x :* ↧y :* (↧u :* ↧v)) :+ ↥u :* ↧v :* (↧x :* ↧y))
                                                             refl (↥ x) (↧ x) (↧ y) (↥ u) (↧ u) (↧ v) ⟩
  ↥x ℤ.* ↧y ℤ.* (↧u ℤ.* ↧v) ℤ.+ ↥u ℤ.* ↧v ℤ.* (↧x ℤ.* ↧y) ≡⟨ cong₂ ℤ._+_ (cong (ℤ._* (↧u ℤ.* ↧v)) ab′∼a′b)
                                                                         (cong (ℤ._* (↧x ℤ.* ↧y)) cd′∼c′d) ⟩
  ↥y ℤ.* ↧x ℤ.* (↧u ℤ.* ↧v) ℤ.+ ↥v ℤ.* ↧u ℤ.* (↧x ℤ.* ↧y) ≡⟨ solve 6 (λ ↧x ↥y ↧y ↧u ↥v ↧v →
                                                             (↥y :* ↧x :* (↧u :* ↧v)) :+ ↥v :* ↧u :* (↧x :* ↧y) :=
                                                             (↥y :* ↧v :+ ↥v :* ↧y) :* (↧x :* ↧u))
                                                             refl (↧ x) (↥ y) (↧ y) (↧ u) (↥ v) (↧ v) ⟩
  (↥y ℤ.* ↧v ℤ.+ ↥v ℤ.* ↧y) ℤ.* (↧x ℤ.* ↧u)               ∎)
  where
  ↥x = ↥ x; ↧x = ↧ x; ↥y = ↥ y; ↧y = ↧ y; ↥u = ↥ u; ↧u = ↧ u; ↥v = ↥ v; ↧v = ↧ v
  open ≡-Reasoning
  open ℤ-solver

+-congʳ : ∀ p → q ≃ r → p + q ≃ p + r
+-congʳ p q≃r = +-cong (≃-refl {p}) q≃r

+-congˡ : ∀ p → q ≃ r → q + p ≃ r + p
+-congˡ p q≃r = +-cong q≃r (≃-refl {p})

-- Associativity

+-assoc-↥ : Associative (_≡_ on ↥_) _+_
+-assoc-↥ p@record{} q@record{} r@record{} = solve 6 (λ ↥p ↧p ↥q ↧q ↥r ↧r →
    (↥p :* ↧q :+ ↥q :* ↧p) :* ↧r :+ ↥r :* (↧p :* ↧q) :=
    ↥p :* (↧q :* ↧r) :+ (↥q :* ↧r :+ ↥r :* ↧q) :* ↧p)
  refl (↥ p) (↧ p) (↥ q) (↧ q) (↥ r) (↧ r)
  where open ℤ-solver

+-assoc-↧ : Associative (_≡_ on ↧ₙ_) _+_
+-assoc-↧ p@record{} q@record{} r@record{} = ℕ.*-assoc (↧ₙ p) (↧ₙ q) (↧ₙ r)

+-assoc-≡ : Associative _≡_ _+_
+-assoc-≡ p q r = ↥↧≡⇒≡ (+-assoc-↥ p q r) (+-assoc-↧ p q r)

+-assoc : Associative _≃_ _+_
+-assoc p q r = ≃-reflexive (+-assoc-≡ p q r)

-- Commutativity

+-comm-↥ : Commutative (_≡_ on ↥_) _+_
+-comm-↥ p@record{} q@record{} = ℤ.+-comm (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)

+-comm-↧ : Commutative (_≡_ on ↧ₙ_) _+_
+-comm-↧ p@record{} q@record{} = ℕ.*-comm (↧ₙ p) (↧ₙ q)

+-comm-≡ : Commutative _≡_ _+_
+-comm-≡ p q = ↥↧≡⇒≡ (+-comm-↥ p q) (+-comm-↧ p q)

+-comm : Commutative _≃_ _+_
+-comm p q = ≃-reflexive (+-comm-≡ p q)

-- Identities

+-identityˡ-↥ : LeftIdentity (_≡_ on ↥_) 0ℚᵘ _+_
+-identityˡ-↥ p@record{} = begin
  0ℤ ℤ.* ↧ p ℤ.+ ↥ p ℤ.* 1ℤ ≡⟨ cong₂ ℤ._+_ (ℤ.*-zeroˡ (↧ p)) (ℤ.*-identityʳ (↥ p)) ⟩
  0ℤ ℤ.+ ↥ p                ≡⟨ ℤ.+-identityˡ (↥ p) ⟩
  ↥ p                       ∎ where open ≡-Reasoning

+-identityˡ-↧ : LeftIdentity (_≡_ on ↧ₙ_) 0ℚᵘ _+_
+-identityˡ-↧ p@record{} = ℕ.+-identityʳ (↧ₙ p)

+-identityˡ-≡ : LeftIdentity _≡_ 0ℚᵘ _+_
+-identityˡ-≡ p = ↥↧≡⇒≡ (+-identityˡ-↥ p) (+-identityˡ-↧ p)

+-identityˡ : LeftIdentity _≃_ 0ℚᵘ _+_
+-identityˡ p = ≃-reflexive (+-identityˡ-≡ p)

+-identityʳ-≡ : RightIdentity _≡_ 0ℚᵘ _+_
+-identityʳ-≡ = comm∧idˡ⇒idʳ +-comm-≡ {e = 0ℚᵘ} +-identityˡ-≡

+-identityʳ : RightIdentity _≃_ 0ℚᵘ _+_
+-identityʳ p = ≃-reflexive (+-identityʳ-≡ p)

+-identity-≡ : Identity _≡_ 0ℚᵘ _+_
+-identity-≡ = +-identityˡ-≡ , +-identityʳ-≡

+-identity : Identity _≃_ 0ℚᵘ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseˡ : LeftInverse _≃_ 0ℚᵘ -_ _+_
+-inverseˡ p@record{} = *≡* let n = ↥ p; d = ↧ p in
  ((ℤ.- n) ℤ.* d ℤ.+ n ℤ.* d) ℤ.* 1ℤ ≡⟨ ℤ.*-identityʳ ((ℤ.- n) ℤ.* d ℤ.+ n ℤ.* d) ⟩
  (ℤ.- n) ℤ.* d ℤ.+ n ℤ.* d          ≡⟨ cong (ℤ._+ (n ℤ.* d)) (ℤ.neg-distribˡ-* n d) ⟨
  ℤ.- (n ℤ.* d) ℤ.+ n ℤ.* d          ≡⟨ ℤ.+-inverseˡ (n ℤ.* d) ⟩
  0ℤ                                 ∎ where open ≡-Reasoning

+-inverseʳ : RightInverse _≃_ 0ℚᵘ -_ _+_
+-inverseʳ p@record{} = *≡* let n = ↥ p; d = ↧ p in
  (n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d) ℤ.* 1ℤ ≡⟨ ℤ.*-identityʳ (n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d) ⟩
  n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d          ≡⟨ cong (λ n+d → n ℤ.* d ℤ.+ n+d) (ℤ.neg-distribˡ-* n d) ⟨
  n ℤ.* d ℤ.+ ℤ.- (n ℤ.* d)          ≡⟨ ℤ.+-inverseʳ (n ℤ.* d) ⟩
  0ℤ                                 ∎ where open ≡-Reasoning

+-inverse : Inverse _≃_ 0ℚᵘ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

+-cancelˡ : ∀ {r p q} → r + p ≃ r + q → p ≃ q
+-cancelˡ {r} {p} {q} r+p≃r+q = begin-equality
  p            ≃⟨ +-identityʳ p ⟨
  p + 0ℚᵘ      ≃⟨ +-congʳ p (+-inverseʳ r) ⟨
  p + (r - r)  ≃⟨ +-assoc p r (- r) ⟨
  (p + r) - r  ≃⟨ +-congˡ (- r) (+-comm p r) ⟩
  (r + p) - r  ≃⟨ +-congˡ (- r) r+p≃r+q ⟩
  (r + q) - r  ≃⟨ +-congˡ (- r) (+-comm r q) ⟩
  (q + r) - r  ≃⟨ +-assoc q r (- r) ⟩
  q + (r - r)  ≃⟨ +-congʳ q (+-inverseʳ r) ⟩
  q + 0ℚᵘ      ≃⟨ +-identityʳ q ⟩
  q            ∎ where open ≤-Reasoning

+-cancelʳ : ∀ {r p q} → p + r ≃ q + r → p ≃ q
+-cancelʳ {r} {p} {q} p+r≃q+r = +-cancelˡ {r} $ begin-equality
  r + p ≃⟨ +-comm r p ⟩
  p + r ≃⟨ p+r≃q+r ⟩
  q + r ≃⟨ +-comm q r ⟩
  r + q ∎ where open ≤-Reasoning

p+p≃0⇒p≃0 : ∀ p → p + p ≃ 0ℚᵘ → p ≃ 0ℚᵘ
p+p≃0⇒p≃0 (mkℚᵘ ℤ.+0 _) (*≡* _) = *≡* refl

------------------------------------------------------------------------
-- Properties of _+_ and -_

neg-distrib-+ : ∀ p q → - (p + q) ≡ (- p) + (- q)
neg-distrib-+ p@record{} q@record{} = ↥↧≡⇒≡ (begin
    ℤ.- (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p)       ≡⟨ ℤ.neg-distrib-+ (↥ p ℤ.* ↧ q) _ ⟩
    ℤ.- (↥ p ℤ.* ↧ q) ℤ.+ ℤ.- (↥ q ℤ.* ↧ p) ≡⟨ cong₂ ℤ._+_ (ℤ.neg-distribˡ-* (↥ p) _)
                                                           (ℤ.neg-distribˡ-* (↥ q) _) ⟩
    (ℤ.- ↥ p) ℤ.* ↧ q ℤ.+ (ℤ.- ↥ q) ℤ.* ↧ p ∎
  ) refl
  where open ≡-Reasoning

p≃-p⇒p≃0 : ∀ p → p ≃ - p → p ≃ 0ℚᵘ
p≃-p⇒p≃0 p p≃-p = p+p≃0⇒p≃0 p (begin-equality
  p + p  ≃⟨ +-congʳ p p≃-p ⟩
  p - p  ≃⟨ +-inverseʳ p ⟩
  0ℚᵘ    ∎)
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

private
  lemma : ∀ r p q → (↥ r ℤ.* ↧ p ℤ.+ ↥ p ℤ.* ↧ r) ℤ.* (↧ r ℤ.* ↧ q)
                    ≡ (↥ r ℤ.* ↧ r) ℤ.* (↧ p ℤ.* ↧ q) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ p ℤ.* ↧ q)
  lemma r p q = solve 5 (λ ↥r ↧r ↧p ↥p ↧q →
                          (↥r :* ↧p :+ ↥p :* ↧r) :* (↧r :* ↧q) :=
                          (↥r :* ↧r) :* (↧p :* ↧q) :+ (↧r :* ↧r) :* (↥p :* ↧q))
                      refl (↥ r) (↧ r) (↧ p) (↥ p) (↧ q)
    where open ℤ-solver

+-monoʳ-≤ : LeftMonotonic _≤_ _≤_ _+_
+-monoʳ-≤ r@record{} {p@record{}} {q@record{}} (*≤* x≤y) = *≤* $ begin
  ↥ (r + p) ℤ.* ↧ (r + q)                                  ≡⟨ lemma r p q ⟩
  r₂ ℤ.* (↧ p ℤ.* ↧ q) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ p ℤ.* ↧ q) ≤⟨ leq ⟩
  r₂ ℤ.* (↧ q ℤ.* ↧ p) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ q ℤ.* ↧ p) ≡⟨ sym $ lemma r q p ⟩
  ↥ (r + q) ℤ.* (↧ (r + p))                                ∎
  where
  open ℤ.≤-Reasoning; r₂ = ↥ r ℤ.* ↧ r
  leq = ℤ.+-mono-≤
    (ℤ.≤-reflexive $ cong (r₂ ℤ.*_) (ℤ.*-comm (↧ p) (↧ q)))
    (ℤ.*-monoˡ-≤-nonNeg (↧ r ℤ.* ↧ r) x≤y)

+-monoˡ-≤ : RightMonotonic _≤_ _≤_ _+_
+-monoˡ-≤ r {p} {q} rewrite +-comm-≡ p r | +-comm-≡ q r = +-monoʳ-≤ r

+-mono-≤ : Monotonic₂ _≤_ _≤_ _≤_ _+_
+-mono-≤ =
  BC.monoˡ∧monoʳ⇒mono₂ _≤_ _≤_ _≤_ ≤-trans +-monoʳ-≤ +-monoˡ-≤

p≤q⇒p≤r+q : ∀ r .{{_ : NonNegative r}} → p ≤ q → p ≤ r + q
p≤q⇒p≤r+q {p} {q} r p≤q = subst (_≤ r + q) (+-identityˡ-≡ p) (+-mono-≤ (nonNegative⁻¹ r) p≤q)

p≤q+p : ∀ p q .{{_ : NonNegative q}} → p ≤ q + p
p≤q+p p q = p≤q⇒p≤r+q q ≤-refl

p≤p+q : ∀ p q .{{_ : NonNegative q}} → p ≤ p + q
p≤p+q p q rewrite +-comm-≡ p q = p≤q+p p q

------------------------------------------------------------------------
-- Properties of _+_ and _<_

+-monoʳ-< : LeftMonotonic _<_ _<_ _+_
+-monoʳ-< r@record{} {p@record{}} {q@record{}} (*<* x<y) = *<* $ begin-strict
  ↥ (r + p) ℤ.* (↧ (r + q))                          ≡⟨ lemma r p q ⟩
  ↥r↧r ℤ.* (↧ p ℤ.* ↧ q) ℤ.+ ↧r↧r ℤ.* (↥ p ℤ.* ↧ q)  <⟨ leq ⟩
  ↥r↧r ℤ.* (↧ q ℤ.* ↧ p) ℤ.+ ↧r↧r ℤ.* (↥ q ℤ.* ↧ p)  ≡⟨ lemma r q p ⟨
  ↥ (r + q) ℤ.* (↧ (r + p))                          ∎
  where
  open ℤ.≤-Reasoning; ↥r↧r = ↥ r ℤ.* ↧ r; ↧r↧r = ↧ r ℤ.* ↧ r
  leq = ℤ.+-mono-≤-<
    (ℤ.≤-reflexive $ cong (↥r↧r ℤ.*_) (ℤ.*-comm (↧ p) (↧ q)))
    (ℤ.*-monoˡ-<-pos ↧r↧r x<y)

+-monoˡ-< : RightMonotonic _<_ _<_ _+_
+-monoˡ-< r {p} {q} rewrite +-comm-≡ p r | +-comm-≡ q r = +-monoʳ-< r

+-mono-< : Monotonic₂ _<_ _<_ _<_ _+_
+-mono-< {p} {q} {u} {v} p<q u<v = <-trans (+-monoˡ-< u p<q) (+-monoʳ-< q u<v)

+-mono-≤-< : Monotonic₂ _≤_ _<_ _<_ _+_
+-mono-≤-< {p} {q} {r} p≤q q<r = ≤-<-trans (+-monoˡ-≤ r p≤q) (+-monoʳ-< q q<r)

+-mono-<-≤ : Monotonic₂ _<_ _≤_ _<_ _+_
+-mono-<-≤ {p} {q} {r} p<q q≤r = <-≤-trans (+-monoˡ-< r p<q) (+-monoʳ-≤ q q≤r)

------------------------------------------------------------------------
-- Properties of _+_ and predicates

pos+pos⇒pos : ∀ p .{{_ : Positive p}} →
              ∀ q .{{_ : Positive q}} →
              Positive (p + q)
pos+pos⇒pos p q = positive (+-mono-< (positive⁻¹ p) (positive⁻¹ q))

nonNeg+nonNeg⇒nonNeg : ∀ p .{{_ : NonNegative p}} →
                       ∀ q .{{_ : NonNegative q}} →
                       NonNegative (p + q)
nonNeg+nonNeg⇒nonNeg p q = nonNegative
  (+-mono-≤ (nonNegative⁻¹ p) (nonNegative⁻¹ q))

------------------------------------------------------------------------
-- Properties of _-_

+-minus-telescope : ∀ p q r → (p - q) + (q - r) ≃ p - r
+-minus-telescope p q r = begin-equality
  (p - q) + (q - r)   ≃⟨ ≃-sym (+-assoc (p - q) q (- r)) ⟩
  (p - q) + q - r     ≃⟨ +-congˡ (- r) (+-assoc p (- q) q) ⟩
  (p + (- q + q)) - r ≃⟨ +-congˡ (- r) (+-congʳ p (+-inverseˡ q)) ⟩
  (p + 0ℚᵘ) - r       ≃⟨ +-congˡ (- r) (+-identityʳ p) ⟩
  p - r               ∎ where open ≤-Reasoning

p≃q⇒p-q≃0 : ∀ p q → p ≃ q → p - q ≃ 0ℚᵘ
p≃q⇒p-q≃0 p q p≃q = begin-equality
  p - q ≃⟨ +-congˡ (- q) p≃q ⟩
  q - q ≃⟨ +-inverseʳ q ⟩
  0ℚᵘ   ∎ where open ≤-Reasoning

p-q≃0⇒p≃q : ∀ p q → p - q ≃ 0ℚᵘ → p ≃ q
p-q≃0⇒p≃q p q p-q≃0 = begin-equality
  p             ≡⟨ +-identityʳ-≡ p ⟨
  p + 0ℚᵘ       ≃⟨ +-congʳ p (≃-sym (+-inverseˡ q)) ⟩
  p + (- q + q) ≡⟨ +-assoc-≡ p (- q) q ⟨
  (p - q) + q   ≃⟨ +-congˡ q p-q≃0 ⟩
  0ℚᵘ + q       ≡⟨ +-identityˡ-≡ q ⟩
  q             ∎ where open ≤-Reasoning

neg-mono-≤ : Monotonic₁ _≤_ _≥_ (-_)
neg-mono-≤ {p@record{}} {q@record{}} (*≤* p≤q) = *≤* $ begin
  ℤ.- ↥ q ℤ.* ↧ p   ≡⟨ ℤ.neg-distribˡ-* (↥ q) (↧ p) ⟨
  ℤ.- (↥ q ℤ.* ↧ p) ≤⟨ ℤ.neg-mono-≤ p≤q ⟩
  ℤ.- (↥ p ℤ.* ↧ q) ≡⟨ ℤ.neg-distribˡ-* (↥ p) (↧ q) ⟩
  ℤ.- ↥ p ℤ.* ↧ q   ∎ where open ℤ.≤-Reasoning

neg-cancel-≤ : ∀ {p q} → - p ≤ - q → q ≤ p
neg-cancel-≤ {p@record{}} {q@record{}} (*≤* -↥p↧q≤-↥q↧p) = *≤* $ begin
  ↥ q ℤ.* ↧ p             ≡⟨ ℤ.neg-involutive (↥ q ℤ.* ↧ p) ⟨
  ℤ.- ℤ.- (↥ q ℤ.* ↧ p)   ≡⟨ cong ℤ.-_ (ℤ.neg-distribˡ-* (↥ q) (↧ p)) ⟩
  ℤ.- ((ℤ.- ↥ q) ℤ.* ↧ p) ≤⟨ ℤ.neg-mono-≤ -↥p↧q≤-↥q↧p ⟩
  ℤ.- ((ℤ.- ↥ p) ℤ.* ↧ q) ≡⟨ cong ℤ.-_ (ℤ.neg-distribˡ-* (↥ p) (↧ q)) ⟨
  ℤ.- ℤ.- (↥ p ℤ.* ↧ q)   ≡⟨ ℤ.neg-involutive (↥ p ℤ.* ↧ q) ⟩
  ↥ p ℤ.* ↧ q             ∎
  where
    open ℤ.≤-Reasoning

p≤q⇒p-q≤0 : ∀ {p q} → p ≤ q → p - q ≤ 0ℚᵘ
p≤q⇒p-q≤0 {p} {q} p≤q = begin
  p - q ≤⟨ +-monoˡ-≤ (- q) p≤q ⟩
  q - q ≃⟨ +-inverseʳ q ⟩
  0ℚᵘ   ∎ where open ≤-Reasoning

p-q≤0⇒p≤q : ∀ {p q} → p - q ≤ 0ℚᵘ → p ≤ q
p-q≤0⇒p≤q {p} {q} p-q≤0 = begin
  p             ≡⟨ +-identityʳ-≡ p ⟨
  p + 0ℚᵘ       ≃⟨ +-congʳ p (≃-sym (+-inverseˡ q)) ⟩
  p + (- q + q) ≡⟨ +-assoc-≡ p (- q) q ⟨
  (p - q) + q   ≤⟨ +-monoˡ-≤ q p-q≤0 ⟩
  0ℚᵘ + q       ≡⟨ +-identityˡ-≡ q ⟩
  q             ∎ where open ≤-Reasoning

p≤q⇒0≤q-p : ∀ {p q} → p ≤ q → 0ℚᵘ ≤ q - p
p≤q⇒0≤q-p {p} {q} p≤q = begin
  0ℚᵘ   ≃⟨ ≃-sym (+-inverseʳ p) ⟩
  p - p ≤⟨ +-monoˡ-≤ (- p) p≤q ⟩
  q - p ∎ where open ≤-Reasoning

0≤q-p⇒p≤q : ∀ {p q} → 0ℚᵘ ≤ q - p → p ≤ q
0≤q-p⇒p≤q {p} {q} 0≤p-q = begin
  p             ≡⟨ +-identityˡ-≡ p ⟨
  0ℚᵘ + p       ≤⟨ +-monoˡ-≤ p 0≤p-q ⟩
  q - p + p     ≡⟨ +-assoc-≡ q (- p) p ⟩
  q + (- p + p) ≃⟨ +-congʳ q (+-inverseˡ p) ⟩
  q + 0ℚᵘ       ≡⟨ +-identityʳ-≡ q ⟩
  q             ∎ where open ≤-Reasoning

------------------------------------------------------------------------
-- Algebraic structures

+-isMagma : IsMagma _≃_ _+_
+-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong        = +-cong
  }

+-isSemigroup : IsSemigroup _≃_ _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-0-isMonoid : IsMonoid _≃_ _+_ 0ℚᵘ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≃_ _+_ 0ℚᵘ
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

+-0-isGroup : IsGroup _≃_ _+_ 0ℚᵘ (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = +-inverse
  ; ⁻¹-cong  = -‿cong
  }

+-0-isAbelianGroup : IsAbelianGroup _≃_ _+_ 0ℚᵘ (-_)
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
  }

------------------------------------------------------------------------
-- Algebraic bundles

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

*-cong : Congruent₂ _≃_ _*_
*-cong {x@record{}} {y@record{}} {u@record{}} {v@record{}} (*≡* ↥x↧y≡↥y↧x) (*≡* ↥u↧v≡↥v↧u) = *≡* (begin
  (↥ x ℤ.* ↥ u) ℤ.* (↧ y ℤ.* ↧ v) ≡⟨ solve 4 (λ ↥x ↥u ↧y ↧v →
                                       (↥x :* ↥u) :* (↧y :* ↧v) :=
                                       (↥u :* ↧v) :* (↥x :* ↧y))
                                       refl (↥ x) (↥ u) (↧ y) (↧ v) ⟩
  (↥ u ℤ.* ↧ v) ℤ.* (↥ x ℤ.* ↧ y) ≡⟨ cong₂ ℤ._*_ ↥u↧v≡↥v↧u ↥x↧y≡↥y↧x ⟩
  (↥ v ℤ.* ↧ u) ℤ.* (↥ y ℤ.* ↧ x) ≡⟨ solve 4 (λ ↥v ↧u ↥y ↧x →
                                       (↥v :* ↧u) :* (↥y :* ↧x) :=
                                       (↥y :* ↥v) :* (↧x :* ↧u))
                                       refl (↥ v) (↧ u) (↥ y) (↧ x) ⟩
  (↥ y ℤ.* ↥ v) ℤ.* (↧ x ℤ.* ↧ u) ∎)
  where open ≡-Reasoning; open ℤ-solver

*-congˡ : LeftCongruent _≃_ _*_
*-congˡ {p} q≃r = *-cong (≃-refl {p}) q≃r

*-congʳ : RightCongruent _≃_ _*_
*-congʳ {p} q≃r = *-cong q≃r (≃-refl {p})

-- Associativity

*-assoc-↥ : Associative (_≡_ on ↥_) _*_
*-assoc-↥ p@record{} q@record{} r@record{} = ℤ.*-assoc (↥ p) (↥ q) (↥ r)

*-assoc-↧ : Associative (_≡_ on ↧ₙ_) _*_
*-assoc-↧ p@record{} q@record{} r@record{} = ℕ.*-assoc (↧ₙ p) (↧ₙ q) (↧ₙ r)

*-assoc-≡ : Associative _≡_ _*_
*-assoc-≡ p q r = ↥↧≡⇒≡ (*-assoc-↥ p q r) (*-assoc-↧ p q r)

*-assoc : Associative _≃_ _*_
*-assoc p q r = ≃-reflexive (*-assoc-≡ p q r)

-- Commutativity

*-comm-↥ : Commutative (_≡_ on ↥_) _*_
*-comm-↥ p@record{} q@record{} = ℤ.*-comm (↥ p) (↥ q)

*-comm-↧ : Commutative (_≡_ on ↧ₙ_) _*_
*-comm-↧ p@record{} q@record{} = ℕ.*-comm (↧ₙ p) (↧ₙ q)

*-comm-≡ : Commutative _≡_ _*_
*-comm-≡ p q = ↥↧≡⇒≡ (*-comm-↥ p q) (*-comm-↧ p q)

*-comm : Commutative _≃_ _*_
*-comm p q = ≃-reflexive (*-comm-≡ p q)

-- Identities

*-identityˡ-≡ : LeftIdentity _≡_ 1ℚᵘ _*_
*-identityˡ-≡ p@record{} = ↥↧≡⇒≡ (ℤ.*-identityˡ (↥ p)) (ℕ.+-identityʳ (↧ₙ p))

*-identityʳ-≡ : RightIdentity _≡_ 1ℚᵘ _*_
*-identityʳ-≡ = comm∧idˡ⇒idʳ *-comm-≡ {e = 1ℚᵘ} *-identityˡ-≡

*-identity-≡ : Identity _≡_ 1ℚᵘ _*_
*-identity-≡ = *-identityˡ-≡ , *-identityʳ-≡

*-identityˡ : LeftIdentity _≃_ 1ℚᵘ _*_
*-identityˡ p = ≃-reflexive (*-identityˡ-≡ p)

*-identityʳ : RightIdentity _≃_ 1ℚᵘ _*_
*-identityʳ p = ≃-reflexive (*-identityʳ-≡ p)

*-identity : Identity _≃_ 1ℚᵘ _*_
*-identity = *-identityˡ , *-identityʳ

*-inverseˡ : ∀ p .{{_ : NonZero p}} → (1/ p) * p ≃ 1ℚᵘ
*-inverseˡ p@(mkℚᵘ -[1+ n ] d) = *-inverseˡ (mkℚᵘ +[1+ n ] d)
*-inverseˡ p@(mkℚᵘ +[1+ n ] d) = *≡* $ cong +[1+_] $ begin
  (n ℕ.+ d ℕ.* suc n) ℕ.* 1 ≡⟨ ℕ.*-identityʳ _ ⟩
  n ℕ.+ d ℕ.* suc n         ≡⟨ cong (n ℕ.+_) (ℕ.*-suc d n) ⟩
  n ℕ.+ (d ℕ.+ d ℕ.* n)     ≡⟨ trans (sym $ ℕ.+-assoc n d _) (trans
                                      (cong₂ ℕ._+_ (ℕ.+-comm n d) (ℕ.*-comm d n))
                                      (ℕ.+-assoc d n _)) ⟩
  d ℕ.+ (n ℕ.+ n ℕ.* d)     ≡⟨ cong (d ℕ.+_) (sym (ℕ.*-suc n d)) ⟩
  d ℕ.+ n ℕ.* suc d         ≡⟨ ℕ.+-identityʳ _ ⟨
  d ℕ.+ n ℕ.* suc d ℕ.+ 0   ∎
  where open ≡-Reasoning

*-inverseʳ : ∀ p .{{_ : NonZero p}} → p * 1/ p ≃ 1ℚᵘ
*-inverseʳ p = ≃-trans (*-comm p (1/ p)) (*-inverseˡ p)

≄⇒invertible : p ≄ q → Invertible _≃_ 1ℚᵘ _*_ (p - q)
≄⇒invertible {p} {q} p≄q = _ , *-inverseˡ (p - q) , *-inverseʳ (p - q)
  where instance
  _ : NonZero (p - q)
  _ = ≢-nonZero (p≄q ∘ p-q≃0⇒p≃q p q)

*-zeroˡ : LeftZero _≃_ 0ℚᵘ _*_
*-zeroˡ p@record{} = *≡* refl

*-zeroʳ : RightZero _≃_ 0ℚᵘ _*_
*-zeroʳ = Consequences.comm∧zeˡ⇒zeʳ ≃-setoid *-comm *-zeroˡ

*-zero : Zero _≃_ 0ℚᵘ _*_
*-zero = *-zeroˡ , *-zeroʳ

invertible⇒≄ : Invertible _≃_ 1ℚᵘ _*_ (p - q) → p ≄ q
invertible⇒≄ {p} {q} (1/p-q , 1/x*x≃1 , x*1/x≃1) p≃q = 0≄1 (begin
  0ℚᵘ             ≈⟨ *-zeroˡ 1/p-q ⟨
  0ℚᵘ * 1/p-q     ≈⟨ *-congʳ (p≃q⇒p-q≃0 p q p≃q) ⟨
  (p - q) * 1/p-q ≈⟨ x*1/x≃1 ⟩
  1ℚᵘ             ∎)
  where open ≃-Reasoning

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_
*-distribˡ-+ p@record{} q@record{} r@record{} =
  let ↥p = ↥ p; ↧p = ↧ p
      ↥q = ↥ q; ↧q = ↧ q
      ↥r = ↥ r; ↧r = ↧ r
      eq : (↥p ℤ.* (↥q ℤ.* ↧r ℤ.+ ↥r ℤ.* ↧q)) ℤ.* (↧p ℤ.* ↧q ℤ.* (↧p ℤ.* ↧r)) ≡
           (↥p ℤ.* ↥q ℤ.* (↧p ℤ.* ↧r) ℤ.+ ↥p ℤ.* ↥r ℤ.* (↧p ℤ.* ↧q)) ℤ.* (↧p ℤ.* (↧q ℤ.* ↧r))
      eq = solve 6 (λ ↥p ↧p ↥q d e f →
           (↥p :* (↥q :* f :+ e :* d)) :* (↧p :* d :* (↧p :* f)) :=
           (↥p :* ↥q :* (↧p :* f) :+ ↥p :* e :* (↧p :* d)) :* (↧p :* (d :* f)))
           refl ↥p ↧p ↥q ↧q ↥r ↧r
  in *≡* eq where open ℤ-solver

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ = Consequences.comm∧distrˡ⇒distrʳ ≃-setoid +-cong *-comm *-distribˡ-+

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

p*q≃0⇒p≃0∨q≃0 : p * q ≃ 0ℚᵘ → p ≃ 0ℚᵘ ⊎ q ≃ 0ℚᵘ
p*q≃0⇒p≃0∨q≃0 {p@record{}} {q@record{}} p*q≃0 =
  Sum.map (↥p≡0⇒p≃0 p) (↥p≡0⇒p≃0 q) (ℤ.i*j≡0⇒i≡0∨j≡0 _ (p≃0⇒↥p≡0 _ p*q≃0))

p*q≄0⇒p≄0 : (p * q) ≄ 0ℚᵘ → p ≄ 0ℚᵘ
p*q≄0⇒p≄0 {p} {q} pq≄0 p≃0 = pq≄0 $ begin-equality
  p * q   ≃⟨ *-congʳ {q} p≃0 ⟩
  0ℚᵘ * q ≃⟨ *-zeroˡ q ⟩
  0ℚᵘ     ∎
  where open ≤-Reasoning

p*q≢0⇒q≢0 : (p * q) ≄ 0ℚᵘ → q ≄ 0ℚᵘ
p*q≢0⇒q≢0 {p} {q} pq≄0 q≃0 = pq≄0 $ begin-equality
  p * q   ≃⟨ *-congˡ {p} q≃0 ⟩
  p * 0ℚᵘ ≃⟨ *-zeroʳ p ⟩
  0ℚᵘ     ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _*_ and -_

neg-distribˡ-* : ∀ p q → - (p * q) ≃ - p * q
neg-distribˡ-* p@record{} q@record{} =
  *≡* $ cong (ℤ._* (↧ p ℤ.* ↧ q)) $ ℤ.neg-distribˡ-* (↥ p) (↥ q)

neg-distribʳ-* : ∀ p q → - (p * q) ≃ p * - q
neg-distribʳ-* p@record{} q@record{} =
  *≡* $ cong (ℤ._* (↧ p ℤ.* ↧ q)) $ ℤ.neg-distribʳ-* (↥ p) (↥ q)

------------------------------------------------------------------------
-- Properties of _*_ and _/_

*-cancelˡ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (p ℕ.* r)}} →
              ((ℤ.+ p ℤ.* q) / (p ℕ.* r)) ≃ (q / r)
*-cancelˡ-/ p {q} {r} = *≡* (begin-equality
  (↥ ((ℤ.+ p ℤ.* q) / (p ℕ.* r))) ℤ.* (↧ (q / r)) ≡⟨  cong (ℤ._* ↧ (q / r)) (↥[n/d]≡n (ℤ.+ p ℤ.* q) (p ℕ.* r)) ⟩
  (ℤ.+ p ℤ.* q) ℤ.* (↧ (q / r))                   ≡⟨  cong ((ℤ.+ p ℤ.* q) ℤ.*_) (↧[n/d]≡d q r) ⟩
  (ℤ.+ p ℤ.* q) ℤ.* ℤ.+ r                         ≡⟨  xy∙z≈y∙xz (ℤ.+ p) q (ℤ.+ r) ⟩
  (q ℤ.* (ℤ.+ p ℤ.* ℤ.+ r))                       ≡⟨ cong (ℤ._* (ℤ.+ p ℤ.* ℤ.+ r)) (↥[n/d]≡n q r) ⟨
  (↥ (q / r)) ℤ.* (ℤ.+ p ℤ.* ℤ.+ r)               ≡⟨  cong (↥ (q / r) ℤ.*_) (ℤ.pos-* p r) ⟨
  (↥ (q / r)) ℤ.* (ℤ.+ (p ℕ.* r))                 ≡⟨ cong (↥ (q / r) ℤ.*_) (↧[n/d]≡d (ℤ.+ p ℤ.* q) (p ℕ.* r)) ⟨
  (↥ (q / r)) ℤ.* (↧ ((ℤ.+ p ℤ.* q) / (p ℕ.* r))) ∎)
  where open ℤ.≤-Reasoning

*-cancelʳ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (r ℕ.* p)}} →
              ((q ℤ.* ℤ.+ p) / (r ℕ.* p)) ≃ (q / r)
*-cancelʳ-/ p {q} {r} rewrite ℕ.*-comm r p | ℤ.*-comm q (ℤ.+ p) = *-cancelˡ-/ p

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

private
  reorder₁ : ∀ a b c d → a ℤ.* b ℤ.* (c ℤ.* d) ≡ a ℤ.* c ℤ.* b ℤ.* d
  reorder₁ = solve 4 (λ a b c d → (a :* b) :* (c :* d) := (a :* c) :* b :* d) refl
    where open ℤ-solver

  reorder₂ : ∀ a b c d → a ℤ.* b ℤ.* (c ℤ.* d) ≡ a ℤ.* c ℤ.* (b ℤ.* d)
  reorder₂ = solve 4 (λ a b c d → (a :* b) :* (c :* d) := (a :* c) :* (b :* d)) refl
    where open ℤ-solver

  +▹-nonNeg : ∀ n → ℤ.NonNegative (Sign.+ ℤ.◃ n)
  +▹-nonNeg 0       = _
  +▹-nonNeg (suc _) = _

*-cancelʳ-≤-pos : ∀ r .{{_ : Positive r}} → p * r ≤ q * r → p ≤ q
*-cancelʳ-≤-pos {p@record{}} {q@record{}} r@(mkℚᵘ +[1+ _ ] _) (*≤* x≤y) =
 *≤* $ ℤ.*-cancelʳ-≤-pos _ _ (↥ r ℤ.* ↧ r) $ begin
    (↥ p ℤ.* ↧ q) ℤ.* (↥ r ℤ.* ↧ r)  ≡⟨ reorder₂ (↥ p) _ _ (↧ r) ⟩
    (↥ p ℤ.* ↥ r) ℤ.* (↧ q ℤ.* ↧ r)  ≤⟨ x≤y ⟩
    (↥ q ℤ.* ↥ r) ℤ.* (↧ p ℤ.* ↧ r)  ≡⟨ reorder₂ (↥ q) _ _ (↧ r) ⟩
    (↥ q ℤ.* ↧ p) ℤ.* (↥ r ℤ.* ↧ r)  ∎ where open ℤ.≤-Reasoning

*-cancelˡ-≤-pos : ∀ r .{{_ : Positive r}} → r * p ≤ r * q → p ≤ q
*-cancelˡ-≤-pos {p} {q} r rewrite *-comm-≡ r p | *-comm-≡ r q = *-cancelʳ-≤-pos r

*-cancelʳ-≤-neg : ∀ r .{{_ : Negative r}} → p * r ≤ q * r → q ≤ p
*-cancelʳ-≤-neg {p} {q} r@(mkℚᵘ -[1+ _ ] _) pr≤qr = neg-cancel-≤ (*-cancelʳ-≤-pos (- r) (begin
  - p * - r    ≃⟨ neg-distribˡ-* p (- r) ⟨
  - (p * - r)  ≃⟨ -‿cong (neg-distribʳ-* p r) ⟨
  - - (p * r)  ≃⟨ neg-involutive (p * r) ⟩
  p * r        ≤⟨ pr≤qr ⟩
  q * r        ≃⟨ neg-involutive (q * r) ⟨
  - - (q * r)  ≃⟨ -‿cong (neg-distribʳ-* q r) ⟩
  - (q * - r)  ≃⟨ neg-distribˡ-* q (- r) ⟩
  - q * - r    ∎))
  where open ≤-Reasoning

*-cancelˡ-≤-neg : ∀ r .{{_ : Negative r}} → r * p ≤ r * q → q ≤ p
*-cancelˡ-≤-neg {p} {q} r rewrite *-comm-≡ r p | *-comm-≡ r q = *-cancelʳ-≤-neg r

*-monoˡ-≤-nonNeg : ∀ r .{{_ : NonNegative r}} → Monotonic₁ _≤_ _≤_ (_* r)
*-monoˡ-≤-nonNeg r@(mkℚᵘ (ℤ.+ n) _) {p@record{}} {q@record{}} (*≤* x<y) = *≤* $ begin
  ↥ p ℤ.* ↥ r ℤ.* (↧ q   ℤ.* ↧ r)  ≡⟨  reorder₂ (↥ p) _ _ _ ⟩
  l₁          ℤ.* (ℤ.+ n ℤ.* ↧ r)  ≡⟨  cong (l₁ ℤ.*_) (ℤ.pos-* n _) ⟨
  l₁          ℤ.* ℤ.+ (n ℕ.* ↧ₙ r) ≤⟨  ℤ.*-monoʳ-≤-nonNeg (ℤ.+ (n ℕ.* ↧ₙ r)) x<y ⟩
  l₂          ℤ.* ℤ.+ (n ℕ.* ↧ₙ r) ≡⟨ cong (l₂ ℤ.*_) (ℤ.pos-* n _) ⟩
  l₂          ℤ.* (ℤ.+ n ℤ.* ↧ r)  ≡⟨  reorder₂ (↥ q) _ _ _ ⟩
  ↥ q ℤ.* ↥ r ℤ.* (↧ p   ℤ.* ↧ r)  ∎
  where open ℤ.≤-Reasoning; l₁ = ↥ p ℤ.* ↧ q ; l₂ = ↥ q ℤ.* ↧ p

*-monoʳ-≤-nonNeg : ∀ r .{{_ :  NonNegative r}} → Monotonic₁ _≤_ _≤_ (r *_)
*-monoʳ-≤-nonNeg r {p} {q} rewrite *-comm-≡ r p | *-comm-≡ r q = *-monoˡ-≤-nonNeg r

*-mono-≤-nonNeg : ∀ {p q r s} .{{_ : NonNegative p}} .{{_ : NonNegative r}} →
                  p ≤ q → r ≤ s → p * r ≤ q * s
*-mono-≤-nonNeg {p} {q} {r} {s} p≤q r≤s = begin
  p * r ≤⟨ *-monoˡ-≤-nonNeg r p≤q ⟩
  q * r ≤⟨ *-monoʳ-≤-nonNeg q {{nonNeg≤⇒nonNeg p≤q}} r≤s ⟩
  q * s ∎
  where open ≤-Reasoning

*-monoˡ-≤-nonPos : ∀ r .{{_ : NonPositive r}} → Monotonic₁ _≤_ _≥_ (_* r)
*-monoˡ-≤-nonPos r {p} {q} p≤q = begin
  q * r        ≃⟨ neg-involutive (q * r) ⟨
  - - (q * r)  ≃⟨  -‿cong (neg-distribʳ-* q r) ⟩
  - (q * - r)  ≤⟨  neg-mono-≤ (*-monoˡ-≤-nonNeg (- r) {{ -r≥0}} p≤q) ⟩
  - (p * - r)  ≃⟨ -‿cong (neg-distribʳ-* p r) ⟨
  - - (p * r)  ≃⟨  neg-involutive (p * r) ⟩
  p * r        ∎
  where open ≤-Reasoning; -r≥0 = nonNegative (neg-mono-≤ (nonPositive⁻¹ r))

*-monoʳ-≤-nonPos : ∀ r .{{_ :  NonPositive r}} → Monotonic₁ _≤_ _≥_ (r *_)
*-monoʳ-≤-nonPos r {p} {q} rewrite *-comm-≡ r q | *-comm-≡ r p = *-monoˡ-≤-nonPos r

------------------------------------------------------------------------
-- Properties of _*_ and _<_

*-monoˡ-<-pos : ∀ r .{{_ : Positive r}} → Monotonic₁ _<_ _<_ (_* r)
*-monoˡ-<-pos r@record{} {p@record{}} {q@record{}} (*<* x<y) = *<* $ begin-strict
  ↥ p ℤ.*  ↥ r ℤ.* (↧ q  ℤ.* ↧ r) ≡⟨ reorder₁ (↥ p) _ _ _ ⟩
  ↥ p ℤ.*  ↧ q ℤ.*  ↥ r  ℤ.* ↧ r  <⟨ ℤ.*-monoʳ-<-pos (↧ r) (ℤ.*-monoʳ-<-pos (↥ r) x<y) ⟩
  ↥ q ℤ.*  ↧ p ℤ.*  ↥ r  ℤ.* ↧ r  ≡⟨ reorder₁ (↥ q) _ _ _ ⟨
  ↥ q ℤ.*  ↥ r ℤ.* (↧ p  ℤ.* ↧ r) ∎ where open ℤ.≤-Reasoning

*-monoʳ-<-pos : ∀ r .{{_ : Positive r}} → Monotonic₁ _<_ _<_ (r *_)
*-monoʳ-<-pos r {p} {q} rewrite *-comm-≡ r p | *-comm-≡ r q = *-monoˡ-<-pos r

*-mono-<-nonNeg : ∀ {p q r s} .{{_ : NonNegative p}} .{{_ : NonNegative r}} →
                  p < q → r < s → p * r < q * s
*-mono-<-nonNeg {p} {q} {r} {s} p<q r<s = begin-strict
  p * r ≤⟨ *-monoˡ-≤-nonNeg r (<⇒≤ p<q) ⟩
  q * r <⟨ *-monoʳ-<-pos q {{nonNeg<⇒pos p<q}} r<s ⟩
  q * s ∎
  where open ≤-Reasoning

*-cancelʳ-<-nonNeg : ∀ r .{{_ : NonNegative r}} → p * r < q * r → p < q
*-cancelʳ-<-nonNeg {p@record{}} {q@record{}} r@(mkℚᵘ (ℤ.+ _) _) (*<* x<y) =
  *<* $ ℤ.*-cancelʳ-<-nonNeg (↥ r ℤ.* ↧ r) {{+▹-nonNeg _}} $ begin-strict
    (↥ p ℤ.* ↧ q) ℤ.* (↥ r ℤ.* ↧ r)  ≡⟨ reorder₂ (↥ p) _ _ (↧ r) ⟩
    (↥ p ℤ.* ↥ r) ℤ.* (↧ q ℤ.* ↧ r)  <⟨ x<y ⟩
    (↥ q ℤ.* ↥ r) ℤ.* (↧ p ℤ.* ↧ r)  ≡⟨ reorder₂ (↥ q) _ _ (↧ r) ⟩
    (↥ q ℤ.* ↧ p) ℤ.* (↥ r ℤ.* ↧ r)  ∎ where open ℤ.≤-Reasoning

*-cancelˡ-<-nonNeg : ∀ r .{{_ : NonNegative r}} → r * p < r * q → p < q
*-cancelˡ-<-nonNeg {p} {q} r rewrite *-comm-≡ r p | *-comm-≡ r q = *-cancelʳ-<-nonNeg r

*-monoˡ-<-neg : ∀ r .{{_ :  Negative r}} → Monotonic₁ _<_ _>_ (_* r)
*-monoˡ-<-neg r {p} {q} p<q = begin-strict
  q * r        ≃⟨ neg-involutive (q * r) ⟨
  - - (q * r)  ≃⟨ -‿cong (neg-distribʳ-* q r) ⟩
  - (q * - r)  <⟨ neg-mono-< (*-monoˡ-<-pos (- r) {{ -r>0}} p<q) ⟩
  - (p * - r)  ≃⟨ -‿cong (neg-distribʳ-* p r) ⟨
  - - (p * r)  ≃⟨ neg-involutive (p * r) ⟩
  p * r        ∎
  where open ≤-Reasoning; -r>0 = positive (neg-mono-< (negative⁻¹ r))

*-monoʳ-<-neg : ∀ r .{{_ : Negative r}} → Monotonic₁ _<_ _>_ (r *_)
*-monoʳ-<-neg r {p} {q} rewrite *-comm-≡ r q | *-comm-≡ r p = *-monoˡ-<-neg r

*-cancelˡ-<-nonPos : ∀ r .{{_ : NonPositive r}} → r * p < r * q → q < p
*-cancelˡ-<-nonPos {p} {q} r rp<rq =
  *-cancelˡ-<-nonNeg (- r) {{ -r≥0}} $ begin-strict
    - r * q    ≃⟨ neg-distribˡ-* r q ⟨
    - (r * q)  <⟨ neg-mono-< rp<rq ⟩
    - (r * p)  ≃⟨ neg-distribˡ-* r p ⟩
    - r * p    ∎
  where open ≤-Reasoning; -r≥0 = nonNegative (neg-mono-≤ (nonPositive⁻¹ r))

*-cancelʳ-<-nonPos : ∀ r .{{_ : NonPositive r}} → p * r < q * r → q < p
*-cancelʳ-<-nonPos {p} {q} r rewrite *-comm-≡ p r | *-comm-≡ q r = *-cancelˡ-<-nonPos r

------------------------------------------------------------------------
-- Properties of _*_ and predicates

pos*pos⇒pos : ∀ p .{{_ : Positive p}} →
              ∀ q .{{_ : Positive q}} →
              Positive (p * q)
pos*pos⇒pos p q = positive
  (*-mono-<-nonNeg (positive⁻¹ p) (positive⁻¹ q))

nonNeg*nonNeg⇒nonNeg : ∀ p .{{_ : NonNegative p}} →
                       ∀ q .{{_ : NonNegative q}} →
                       NonNegative (p * q)
nonNeg*nonNeg⇒nonNeg p q = nonNegative
  (*-mono-≤-nonNeg (nonNegative⁻¹ p) (nonNegative⁻¹ q))

------------------------------------------------------------------------
-- Algebraic structures

*-isMagma : IsMagma _≃_ _*_
*-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong        = *-cong
  }

*-isSemigroup : IsSemigroup _≃_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-1-isMonoid : IsMonoid _≃_ _*_ 1ℚᵘ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≃_ _*_ 1ℚᵘ
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }

+-*-isRing : IsRing _≃_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = *-cong
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }

+-*-isCommutativeRing : IsCommutativeRing _≃_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

+-*-isHeytingCommutativeRing : IsHeytingCommutativeRing _≃_ _≄_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
+-*-isHeytingCommutativeRing = record
  { isCommutativeRing   = +-*-isCommutativeRing
  ; isApartnessRelation = ≄-isApartnessRelation
  ; #⇒invertible        = ≄⇒invertible
  ; invertible⇒#        = invertible⇒≄
  }

+-*-isHeytingField : IsHeytingField _≃_ _≄_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
+-*-isHeytingField = record
  { isHeytingCommutativeRing = +-*-isHeytingCommutativeRing
  ; tight                    = ≄-tight
  }

------------------------------------------------------------------------
-- Algebraic bundles

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

+-*-heytingCommutativeRing : HeytingCommutativeRing 0ℓ 0ℓ 0ℓ
+-*-heytingCommutativeRing = record
  { isHeytingCommutativeRing = +-*-isHeytingCommutativeRing
  }

+-*-heytingField : HeytingField 0ℓ 0ℓ 0ℓ
+-*-heytingField = record
  { isHeytingField = +-*-isHeytingField
  }

------------------------------------------------------------------------
-- Properties of 1/_
------------------------------------------------------------------------

private
  p>1⇒p≢0 : p > 1ℚᵘ → NonZero p
  p>1⇒p≢0 {p} p>1 = pos⇒nonZero p {{positive (<-trans (*<* (ℤ.+<+ ℕ.≤-refl)) p>1)}}

1/nonZero⇒nonZero : ∀ p .{{_ : NonZero p}} → NonZero (1/ p)
1/nonZero⇒nonZero (mkℚᵘ (+[1+ _ ]) _) = _
1/nonZero⇒nonZero (mkℚᵘ (-[1+ _ ]) _) = _

1/-involutive-≡ : ∀ p .{{_ : NonZero p}} →
                  (1/ (1/ p)) {{1/nonZero⇒nonZero p}} ≡ p
1/-involutive-≡ (mkℚᵘ +[1+ n ] d-1) = refl
1/-involutive-≡ (mkℚᵘ -[1+ n ] d-1) = refl

1/-involutive : ∀ p .{{_ : NonZero p}} →
                (1/ (1/ p)) {{1/nonZero⇒nonZero p}} ≃ p
1/-involutive p = ≃-reflexive (1/-involutive-≡ p)

1/pos⇒pos : ∀ p .{{p>0 : Positive p}} → Positive ((1/ p) {{pos⇒nonZero p}})
1/pos⇒pos (mkℚᵘ +[1+ n ] d-1) = _

1/neg⇒neg : ∀ p .{{p<0 : Negative p}} → Negative ((1/ p) {{neg⇒nonZero p}})
1/neg⇒neg (mkℚᵘ -[1+ n ] d-1) = _

p>1⇒1/p<1 : ∀ {p} → (p>1 : p > 1ℚᵘ) → (1/ p) {{p>1⇒p≢0 p>1}} < 1ℚᵘ
p>1⇒1/p<1 {p} p>1 = lemma′ p (p>1⇒p≢0 p>1) p>1
  where
  lemma′ : ∀ p p≢0 → p > 1ℚᵘ → (1/ p) {{p≢0}} < 1ℚᵘ
  lemma′ (mkℚᵘ n@(+[1+ _ ]) d-1) _ (*<* ↥p1>1↧p) = *<* (begin-strict
    ↥ (1/ mkℚᵘ n d-1) ℤ.* 1ℤ         ≡⟨⟩
    +[1+ d-1 ] ℤ.* 1ℤ                ≡⟨ ℤ.*-comm +[1+ d-1 ] 1ℤ ⟩
    1ℤ ℤ.* +[1+ d-1 ]                <⟨ ↥p1>1↧p ⟩
    n  ℤ.* 1ℤ                        ≡⟨ ℤ.*-comm n 1ℤ ⟩
    1ℤ ℤ.* n                         ≡⟨⟩
    (↥ 1ℚᵘ) ℤ.* (↧ (1/ mkℚᵘ n d-1))  ∎)
    where open ℤ.≤-Reasoning

1/-antimono-≤-pos : ∀ {p q} .{{_ : Positive p}} .{{_ : Positive q}} →
                    p ≤ q → (1/ q) {{pos⇒nonZero q}} ≤ (1/ p) {{pos⇒nonZero p}}
1/-antimono-≤-pos {p} {q} p≤q = begin
  1/q              ≃⟨ *-identityˡ 1/q ⟨
  1ℚᵘ * 1/q        ≃⟨ *-congʳ (*-inverseˡ p) ⟨
  (1/p * p) * 1/q  ≤⟨  *-monoˡ-≤-nonNeg 1/q (*-monoʳ-≤-nonNeg 1/p p≤q) ⟩
  (1/p * q) * 1/q  ≃⟨  *-assoc 1/p q 1/q ⟩
  1/p * (q * 1/q)  ≃⟨  *-congˡ {1/p} (*-inverseʳ q) ⟩
  1/p * 1ℚᵘ        ≃⟨  *-identityʳ (1/p) ⟩
  1/p              ∎
  where
  open ≤-Reasoning
  instance
    _ = pos⇒nonZero p
    _ = pos⇒nonZero q
  1/p = 1/ p
  1/q = 1/ q
  instance
    1/p≥0 : NonNegative 1/p
    1/p≥0 = pos⇒nonNeg 1/p {{1/pos⇒pos p}}

    1/q≥0 : NonNegative 1/q
    1/q≥0 = pos⇒nonNeg 1/q {{1/pos⇒pos q}}

------------------------------------------------------------------------
-- Properties of _⊓_ and _⊔_
------------------------------------------------------------------------
-- Basic specification in terms of _≤_

p≤q⇒p⊔q≃q : p ≤ q → p ⊔ q ≃ q
p≤q⇒p⊔q≃q {p@record{}} {q@record{}} p≤q with p ≤ᵇ q in eq
... | true  = ≃-refl
... | false = contradiction (≤⇒≤ᵇ p≤q) (subst (¬_ ∘ T) (sym eq) λ())

p≥q⇒p⊔q≃p : p ≥ q → p ⊔ q ≃ p
p≥q⇒p⊔q≃p {p@record{}} {q@record{}} p≥q with p ≤ᵇ q in eq
... | true  = ≤-antisym p≥q (≤ᵇ⇒≤ (subst T (sym eq) _))
... | false = ≃-refl

p≤q⇒p⊓q≃p : p ≤ q → p ⊓ q ≃ p
p≤q⇒p⊓q≃p {p@record{}} {q@record{}} p≤q with p ≤ᵇ q in eq
... | true  = ≃-refl
... | false = contradiction (≤⇒≤ᵇ p≤q) (subst (¬_ ∘ T) (sym eq) λ())

p≥q⇒p⊓q≃q : p ≥ q → p ⊓ q ≃ q
p≥q⇒p⊓q≃q {p@record{}} {q@record{}} p≥q with p ≤ᵇ q in eq
... | true  = ≤-antisym (≤ᵇ⇒≤ (subst T (sym eq) _)) p≥q
... | false = ≃-refl

⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = p≤q⇒p⊓q≃p
  ; x≥y⇒x⊓y≈y = p≥q⇒p⊓q≃q
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = p≤q⇒p⊔q≃q
  ; x≥y⇒x⊔y≈x = p≥q⇒p⊔q≃p
  }

------------------------------------------------------------------------
-- Derived properties of _⊓_ and _⊔_

private
  module ⊓-⊔-properties        = MinMaxOp        ⊓-operator ⊔-operator
  module ⊓-⊔-latticeProperties = LatticeMinMaxOp ⊓-operator ⊔-operator

open ⊓-⊔-properties public
  using
  ( ⊓-congˡ                   -- : LeftCongruent _≃_ _⊓_
  ; ⊓-congʳ                   -- : RightCongruent _≃_ _⊓_
  ; ⊓-cong                    -- : Congruent₂ _≃_ _⊓_
  ; ⊓-idem                    -- : Idempotent _≃_ _⊓_
  ; ⊓-sel                     -- : Selective _≃_ _⊓_
  ; ⊓-assoc                   -- : Associative _≃_ _⊓_
  ; ⊓-comm                    -- : Commutative _≃_ _⊓_

  ; ⊔-congˡ                   -- : LeftCongruent _≃_ _⊔_
  ; ⊔-congʳ                   -- : RightCongruent _≃_ _⊔_
  ; ⊔-cong                    -- : Congruent₂ _≃_ _⊔_
  ; ⊔-idem                    -- : Idempotent _≃_ _⊔_
  ; ⊔-sel                     -- : Selective _≃_ _⊔_
  ; ⊔-assoc                   -- : Associative _≃_ _⊔_
  ; ⊔-comm                    -- : Commutative _≃_ _⊔_

  ; ⊓-distribˡ-⊔              -- : _DistributesOverˡ_ _≃_ _⊓_ _⊔_
  ; ⊓-distribʳ-⊔              -- : _DistributesOverʳ_ _≃_ _⊓_ _⊔_
  ; ⊓-distrib-⊔               -- : _DistributesOver_  _≃_ _⊓_ _⊔_
  ; ⊔-distribˡ-⊓              -- : _DistributesOverˡ_ _≃_ _⊔_ _⊓_
  ; ⊔-distribʳ-⊓              -- : _DistributesOverʳ_ _≃_ _⊔_ _⊓_
  ; ⊔-distrib-⊓               -- : _DistributesOver_  _≃_ _⊔_ _⊓_
  ; ⊓-absorbs-⊔               -- : _Absorbs_ _≃_ _⊓_ _⊔_
  ; ⊔-absorbs-⊓               -- : _Absorbs_ _≃_ _⊔_ _⊓_
  ; ⊔-⊓-absorptive            -- : Absorptive _≃_ _⊔_ _⊓_
  ; ⊓-⊔-absorptive            -- : Absorptive _≃_ _⊓_ _⊔_

  ; ⊓-isMagma                 -- : IsMagma _≃_ _⊓_
  ; ⊓-isSemigroup             -- : IsSemigroup _≃_ _⊓_
  ; ⊓-isCommutativeSemigroup  -- : IsCommutativeSemigroup _≃_ _⊓_
  ; ⊓-isBand                  -- : IsBand _≃_ _⊓_
  ; ⊓-isSelectiveMagma        -- : IsSelectiveMagma _≃_ _⊓_

  ; ⊔-isMagma                 -- : IsMagma _≃_ _⊔_
  ; ⊔-isSemigroup             -- : IsSemigroup _≃_ _⊔_
  ; ⊔-isCommutativeSemigroup  -- : IsCommutativeSemigroup _≃_ _⊔_
  ; ⊔-isBand                  -- : IsBand _≃_ _⊔_
  ; ⊔-isSelectiveMagma        -- : IsSelectiveMagma _≃_ _⊔_

  ; ⊓-magma                   -- : Magma _ _
  ; ⊓-semigroup               -- : Semigroup _ _
  ; ⊓-band                    -- : Band _ _
  ; ⊓-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊓-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-magma                   -- : Magma _ _
  ; ⊔-semigroup               -- : Semigroup _ _
  ; ⊔-band                    -- : Band _ _
  ; ⊔-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊔-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊓-triangulate             -- : ∀ p q r → p ⊓ q ⊓ r ≃ (p ⊓ q) ⊓ (q ⊓ r)
  ; ⊔-triangulate             -- : ∀ p q r → p ⊔ q ⊔ r ≃ (p ⊔ q) ⊔ (q ⊔ r)

  ; ⊓-glb                     -- : ∀ {p q r} → p ≥ r → q ≥ r → p ⊓ q ≥ r
  ; ⊓-mono-≤                  -- : Monotonic₂ _≤_ _≤_ _≤_ _⊓_
  ; ⊓-monoˡ-≤                 -- : ∀ p → Monotonic₁_≤_ _≤_ (_⊓ p)
  ; ⊓-monoʳ-≤                 -- : ∀ p → Monotonic₁_≤_ _≤_ (p ⊓_)

  ; ⊔-lub                     -- : ∀ {p q r} → p ≤ r → q ≤ r → p ⊔ q ≤ r
  ; ⊔-mono-≤                  -- : Monotonic₂ _≤_ _≤_ _≤_ _⊔_
  ; ⊔-monoˡ-≤                 -- : ∀ p → Monotonic₁_≤_ _≤_ (_⊔ p)
  ; ⊔-monoʳ-≤                 -- : ∀ p → Monotonic₁_≤_ _≤_ (p ⊔_)
  )
  renaming
  ( x⊓y≈y⇒y≤x  to p⊓q≃q⇒q≤p      -- : ∀ {p q} → p ⊓ q ≃ q → q ≤ p
  ; x⊓y≈x⇒x≤y  to p⊓q≃p⇒p≤q      -- : ∀ {p q} → p ⊓ q ≃ p → p ≤ q
  ; x⊔y≈y⇒x≤y  to p⊔q≃q⇒p≤q      -- : ∀ {p q} → p ⊔ q ≃ q → p ≤ q
  ; x⊔y≈x⇒y≤x  to p⊔q≃p⇒q≤p      -- : ∀ {p q} → p ⊔ q ≃ p → q ≤ p

  ; x⊓y≤x      to p⊓q≤p          -- : ∀ p q → p ⊓ q ≤ p
  ; x⊓y≤y      to p⊓q≤q          -- : ∀ p q → p ⊓ q ≤ q
  ; x≤y⇒x⊓z≤y  to p≤q⇒p⊓r≤q      -- : ∀ {p q} r → p ≤ q → p ⊓ r ≤ q
  ; x≤y⇒z⊓x≤y  to p≤q⇒r⊓p≤q      -- : ∀ {p q} r → p ≤ q → r ⊓ p ≤ q
  ; x≤y⊓z⇒x≤y  to p≤q⊓r⇒p≤q      -- : ∀ {p} q r → p ≤ q ⊓ r → p ≤ q
  ; x≤y⊓z⇒x≤z  to p≤q⊓r⇒p≤r      -- : ∀ {p} q r → p ≤ q ⊓ r → p ≤ r

  ; x≤x⊔y      to p≤p⊔q          -- : ∀ p q → p ≤ p ⊔ q
  ; x≤y⊔x      to p≤q⊔p          -- : ∀ p q → p ≤ q ⊔ p
  ; x≤y⇒x≤y⊔z  to p≤q⇒p≤q⊔r      -- : ∀ {p q} r → p ≤ q → p ≤ q ⊔ r
  ; x≤y⇒x≤z⊔y  to p≤q⇒p≤r⊔q      -- : ∀ {p q} r → p ≤ q → p ≤ r ⊔ q
  ; x⊔y≤z⇒x≤z  to p⊔q≤r⇒p≤r      -- : ∀ p q {r} → p ⊔ q ≤ r → p ≤ r
  ; x⊔y≤z⇒y≤z  to p⊔q≤r⇒q≤r      -- : ∀ p q {r} → p ⊔ q ≤ r → q ≤ r

  ; x⊓y≤x⊔y    to p⊓q≤p⊔q        -- : ∀ p q → p ⊓ q ≤ p ⊔ q
  )

open ⊓-⊔-latticeProperties public
  using
  ( ⊓-semilattice             -- : Semilattice _ _
  ; ⊔-semilattice             -- : Semilattice _ _
  ; ⊔-⊓-lattice               -- : Lattice _ _
  ; ⊓-⊔-lattice               -- : Lattice _ _
  ; ⊔-⊓-distributiveLattice   -- : DistributiveLattice _ _
  ; ⊓-⊔-distributiveLattice   -- : DistributiveLattice _ _

  ; ⊓-isSemilattice           -- : IsSemilattice _≃_ _⊓_
  ; ⊔-isSemilattice           -- : IsSemilattice _≃_ _⊔_
  ; ⊔-⊓-isLattice             -- : IsLattice _≃_ _⊔_ _⊓_
  ; ⊓-⊔-isLattice             -- : IsLattice _≃_ _⊓_ _⊔_
  ; ⊔-⊓-isDistributiveLattice -- : IsDistributiveLattice _≃_ _⊔_ _⊓_
  ; ⊓-⊔-isDistributiveLattice -- : IsDistributiveLattice _≃_ _⊓_ _⊔_
  )

------------------------------------------------------------------------
-- Raw bundles

⊓-rawMagma : RawMagma _ _
⊓-rawMagma = Magma.rawMagma ⊓-magma

⊔-rawMagma : RawMagma _ _
⊔-rawMagma = Magma.rawMagma ⊔-magma

⊔-⊓-rawLattice : RawLattice _ _
⊔-⊓-rawLattice = Lattice.rawLattice ⊔-⊓-lattice

------------------------------------------------------------------------
-- Monotonic or antimonotic functions distribute over _⊓_ and _⊔_

mono-≤-distrib-⊔ : ∀ {f} → Monotonic₁ _≤_ _≤_ f →
                   ∀ m n → f (m ⊔ n) ≃ f m ⊔ f n
mono-≤-distrib-⊔ pres = ⊓-⊔-properties.mono-≤-distrib-⊔ (mono⇒cong pres) pres

mono-≤-distrib-⊓ : ∀ {f} → Monotonic₁ _≤_ _≤_ f →
                   ∀ m n → f (m ⊓ n) ≃ f m ⊓ f n
mono-≤-distrib-⊓ pres = ⊓-⊔-properties.mono-≤-distrib-⊓ (mono⇒cong pres) pres

antimono-≤-distrib-⊓ : ∀ {f} → Monotonic₁ _≤_ _≥_ f →
                       ∀ m n → f (m ⊓ n) ≃ f m ⊔ f n
antimono-≤-distrib-⊓ pres = ⊓-⊔-properties.antimono-≤-distrib-⊓ (antimono⇒cong pres) pres

antimono-≤-distrib-⊔ : ∀ {f} → Monotonic₁ _≤_ _≥_ f →
                       ∀ m n → f (m ⊔ n) ≃ f m ⊓ f n
antimono-≤-distrib-⊔ pres = ⊓-⊔-properties.antimono-≤-distrib-⊔ (antimono⇒cong pres) pres

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and -_

neg-distrib-⊔-⊓ : ∀ p q → - (p ⊔ q) ≃ - p ⊓ - q
neg-distrib-⊔-⊓ = antimono-≤-distrib-⊔ neg-mono-≤

neg-distrib-⊓-⊔ : ∀ p q → - (p ⊓ q) ≃ - p ⊔ - q
neg-distrib-⊓-⊔ = antimono-≤-distrib-⊓ neg-mono-≤

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and _*_

*-distribˡ-⊓-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → p * (q ⊓ r) ≃ (p * q) ⊓ (p * r)
*-distribˡ-⊓-nonNeg p = mono-≤-distrib-⊓ (*-monoʳ-≤-nonNeg p)

*-distribʳ-⊓-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → (q ⊓ r) * p ≃ (q * p) ⊓ (r * p)
*-distribʳ-⊓-nonNeg p = mono-≤-distrib-⊓ (*-monoˡ-≤-nonNeg p)

*-distribˡ-⊔-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → p * (q ⊔ r) ≃ (p * q) ⊔ (p * r)
*-distribˡ-⊔-nonNeg p = mono-≤-distrib-⊔ (*-monoʳ-≤-nonNeg p)

*-distribʳ-⊔-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → (q ⊔ r) * p ≃ (q * p) ⊔ (r * p)
*-distribʳ-⊔-nonNeg p = mono-≤-distrib-⊔ (*-monoˡ-≤-nonNeg p)

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and _*_

*-distribˡ-⊔-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → p * (q ⊔ r) ≃ (p * q) ⊓ (p * r)
*-distribˡ-⊔-nonPos p = antimono-≤-distrib-⊔ (*-monoʳ-≤-nonPos p)

*-distribʳ-⊔-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → (q ⊔ r) * p ≃ (q * p) ⊓ (r * p)
*-distribʳ-⊔-nonPos p = antimono-≤-distrib-⊔ (*-monoˡ-≤-nonPos p)

*-distribˡ-⊓-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → p * (q ⊓ r) ≃ (p * q) ⊔ (p * r)
*-distribˡ-⊓-nonPos p = antimono-≤-distrib-⊓ (*-monoʳ-≤-nonPos p)

*-distribʳ-⊓-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → (q ⊓ r) * p ≃ (q * p) ⊔ (r * p)
*-distribʳ-⊓-nonPos p = antimono-≤-distrib-⊓ (*-monoˡ-≤-nonPos p)

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and _<_

⊓-mono-< : Monotonic₂ _<_ _<_ _<_ _⊓_
⊓-mono-< {p} {r} {q} {s} p<r q<s with ⊓-sel r s
... | inj₁ r⊓s≃r = <-respʳ-≃ (≃-sym r⊓s≃r) (≤-<-trans (p⊓q≤p p q) p<r)
... | inj₂ r⊓s≃s = <-respʳ-≃ (≃-sym r⊓s≃s) (≤-<-trans (p⊓q≤q p q) q<s)

⊔-mono-< : Monotonic₂ _<_ _<_ _<_ _⊔_
⊔-mono-< {p} {r} {q} {s} p<r q<s with ⊔-sel p q
... | inj₁ p⊔q≃p = <-respˡ-≃ (≃-sym p⊔q≃p) (<-≤-trans p<r (p≤p⊔q r s))
... | inj₂ p⊔q≃q = <-respˡ-≃ (≃-sym p⊔q≃q) (<-≤-trans q<s (p≤q⊔p r s))

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and predicates

pos⊓pos⇒pos : ∀ p .{{_ : Positive p}} →
              ∀ q .{{_ : Positive q}} →
              Positive (p ⊓ q)
pos⊓pos⇒pos p q = positive (⊓-mono-< (positive⁻¹ p) (positive⁻¹ q))

pos⊔pos⇒pos : ∀ p .{{_ : Positive p}} →
              ∀ q .{{_ : Positive q}} →
              Positive (p ⊔ q)
pos⊔pos⇒pos p q = positive (⊔-mono-< (positive⁻¹ p) (positive⁻¹ q))

------------------------------------------------------------------------
-- Properties of ∣_∣
------------------------------------------------------------------------

∣-∣-cong : p ≃ q → ∣ p ∣ ≃ ∣ q ∣
∣-∣-cong p@{mkℚᵘ +[1+ _ ] _} q@{mkℚᵘ +[1+ _ ] _} (*≡* ↥p↧q≡↥q↧p) = *≡* ↥p↧q≡↥q↧p
∣-∣-cong p@{mkℚᵘ +0       _} q@{mkℚᵘ +0       _} (*≡* ↥p↧q≡↥q↧p) = *≡* ↥p↧q≡↥q↧p
∣-∣-cong p@{mkℚᵘ -[1+ _ ] _} q@{mkℚᵘ +0       _} (*≡* ())
∣-∣-cong p@{mkℚᵘ -[1+ _ ] _} q@{mkℚᵘ -[1+ _ ] _} (*≡* ↥p↧q≡↥q↧p) = *≡* (begin
  ↥ ∣ p ∣ ℤ.* ↧ q            ≡⟨ ℤ.neg-involutive _ ⟩
  ℤ.- ℤ.- (↥ ∣ p ∣ ℤ.* ↧ q)  ≡⟨ cong ℤ.-_ (ℤ.neg-distribˡ-* (↥ ∣ p ∣) (↧ q)) ⟩
  ℤ.- (↥ p ℤ.* ↧ q)          ≡⟨ cong ℤ.-_ ↥p↧q≡↥q↧p ⟩
  ℤ.- (↥ q ℤ.* ↧ p)          ≡⟨ cong ℤ.-_ (ℤ.neg-distribˡ-* (↥ ∣ q ∣) (↧ p)) ⟩
  ℤ.- ℤ.- (↥ ∣ q ∣ ℤ.* ↧ p)  ≡⟨ ℤ.neg-involutive _ ⟨
  ↥ ∣ q ∣ ℤ.* ↧ p            ∎)
  where open ≡-Reasoning

∣p∣≃0⇒p≃0 : ∣ p ∣ ≃ 0ℚᵘ → p ≃ 0ℚᵘ
∣p∣≃0⇒p≃0 {mkℚᵘ (ℤ.+ n)  d-1} p≃0ℚ = p≃0ℚ
∣p∣≃0⇒p≃0 {mkℚᵘ -[1+ n ] d-1} (*≡* ())

0≤∣p∣ : ∀ p → 0ℚᵘ ≤ ∣ p ∣
0≤∣p∣ (mkℚᵘ +0       _) = *≤* (ℤ.+≤+ ℕ.z≤n)
0≤∣p∣ (mkℚᵘ +[1+ _ ] _) = *≤* (ℤ.+≤+ ℕ.z≤n)
0≤∣p∣ (mkℚᵘ -[1+ _ ] _) = *≤* (ℤ.+≤+ ℕ.z≤n)

∣-p∣≡∣p∣ : ∀ p → ∣ - p ∣ ≡ ∣ p ∣
∣-p∣≡∣p∣ (mkℚᵘ +[1+ n ] d) = refl
∣-p∣≡∣p∣ (mkℚᵘ +0       d) = refl
∣-p∣≡∣p∣ (mkℚᵘ -[1+ n ] d) = refl

∣-p∣≃∣p∣ : ∀ p → ∣ - p ∣ ≃ ∣ p ∣
∣-p∣≃∣p∣ = ≃-reflexive ∘ ∣-p∣≡∣p∣

0≤p⇒∣p∣≡p : 0ℚᵘ ≤ p → ∣ p ∣ ≡ p
0≤p⇒∣p∣≡p {mkℚᵘ (ℤ.+ n)  d-1} 0≤p = refl
0≤p⇒∣p∣≡p {mkℚᵘ -[1+ n ] d-1} 0≤p = contradiction 0≤p (<⇒≱ (*<* ℤ.-<+))

0≤p⇒∣p∣≃p : 0ℚᵘ ≤ p → ∣ p ∣ ≃ p
0≤p⇒∣p∣≃p {p} = ≃-reflexive ∘ 0≤p⇒∣p∣≡p {p}

∣p∣≡p⇒0≤p : ∣ p ∣ ≡ p → 0ℚᵘ ≤ p
∣p∣≡p⇒0≤p {mkℚᵘ (ℤ.+ n) d-1} ∣p∣≡p = *≤* (begin
  0ℤ ℤ.* +[1+ d-1 ]  ≡⟨ ℤ.*-zeroˡ (ℤ.+ d-1) ⟩
  0ℤ                 ≤⟨ ℤ.+≤+ ℕ.z≤n ⟩
  ℤ.+ n              ≡⟨ ℤ.*-identityʳ (ℤ.+ n) ⟨
  ℤ.+ n ℤ.* 1ℤ       ∎)
  where open ℤ.≤-Reasoning

∣p∣≡p∨∣p∣≡-p : ∀ p → (∣ p ∣ ≡ p) ⊎ (∣ p ∣ ≡ - p)
∣p∣≡p∨∣p∣≡-p (mkℚᵘ (ℤ.+ n)    d-1) = inj₁ refl
∣p∣≡p∨∣p∣≡-p (mkℚᵘ (-[1+ n ]) d-1) = inj₂ refl

∣p∣≃p⇒0≤p : ∣ p ∣ ≃ p → 0ℚᵘ ≤ p
∣p∣≃p⇒0≤p {p} ∣p∣≃p with ∣p∣≡p∨∣p∣≡-p p
... | inj₁ ∣p∣≡p  = ∣p∣≡p⇒0≤p ∣p∣≡p
... | inj₂ ∣p∣≡-p rewrite ∣p∣≡-p = ≤-reflexive (≃-sym (p≃-p⇒p≃0 p (≃-sym ∣p∣≃p)))

∣p+q∣≤∣p∣+∣q∣ : ∀ p q → ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p+q∣≤∣p∣+∣q∣ p@record{} q@record{} = *≤* (begin
  ↥ ∣ p + q ∣ ℤ.* ↧ (∣ p ∣ + ∣ q ∣)                ≡⟨⟩
  ↥ ∣ (↥p↧q ℤ.+ ↥q↧p) / ↧p↧q ∣ ℤ.* ℤ.+ ↧p↧q        ≡⟨⟩
  ↥ (ℤ.+ ℤ.∣ ↥p↧q ℤ.+ ↥q↧p ∣ / ↧p↧q) ℤ.* ℤ.+ ↧p↧q  ≡⟨ cong (ℤ._* ℤ.+ ↧p↧q) (↥[n/d]≡n (ℤ.+ ℤ.∣ ↥p↧q ℤ.+ ↥q↧p ∣) ↧p↧q) ⟩
  ℤ.+ ℤ.∣ ↥p↧q ℤ.+ ↥q↧p ∣ ℤ.* ℤ.+ ↧p↧q             ≤⟨ ℤ.*-monoʳ-≤-nonNeg (ℤ.+ ↧p↧q) (ℤ.+≤+ (ℤ.∣i+j∣≤∣i∣+∣j∣ ↥p↧q ↥q↧p)) ⟩
  (ℤ.+ ℤ.∣ ↥p↧q ∣ ℤ.+ ℤ.+ ℤ.∣ ↥q↧p ∣) ℤ.* ℤ.+ ↧p↧q ≡⟨ cong₂ (λ h₁ h₂ → (h₁ ℤ.+ h₂) ℤ.* ℤ.+ ↧p↧q) ∣↥p∣↧q≡∣↥p↧q∣ ∣↥q∣↧p≡∣↥q↧p∣ ⟨
  (∣↥p∣↧q ℤ.+ ∣↥q∣↧p) ℤ.* ℤ.+ ↧p↧q                 ≡⟨⟩
  (↥∣p∣↧q ℤ.+ ↥∣q∣↧p) ℤ.* ℤ.+ ↧p↧q                 ≡⟨ cong (ℤ._* ℤ.+ ↧p↧q) (↥[n/d]≡n (↥∣p∣↧q ℤ.+ ↥∣q∣↧p) ↧p↧q) ⟩
  ↥ ((↥∣p∣↧q ℤ.+ ↥∣q∣↧p) / ↧p↧q) ℤ.* ℤ.+ ↧p↧q      ≡⟨⟩
  ↥ (∣ p ∣ + ∣ q ∣) ℤ.* ↧ ∣ p + q ∣ ∎)
  where
    open ℤ.≤-Reasoning
    ↥p↧q = ↥ p ℤ.* ↧ q
    ↥q↧p = ↥ q ℤ.* ↧ p
    ↥∣p∣↧q = ↥ ∣ p ∣ ℤ.* ↧ q
    ↥∣q∣↧p = ↥ ∣ q ∣ ℤ.* ↧ p
    ∣↥p∣↧q = ℤ.+ ℤ.∣ ↥ p ∣ ℤ.* ↧ q
    ∣↥q∣↧p = ℤ.+ ℤ.∣ ↥ q ∣ ℤ.* ↧ p
    ↧p↧q = ↧ₙ p ℕ.* ↧ₙ q
    ∣m∣n≡∣mn∣ : ∀ m n → ℤ.+ ℤ.∣ m ∣ ℤ.* ℤ.+ n ≡ ℤ.+ ℤ.∣ m ℤ.* ℤ.+ n ∣
    ∣m∣n≡∣mn∣ m n = begin-equality
      ℤ.+ ℤ.∣ m ∣ ℤ.* ℤ.+ n                        ≡⟨⟩
      ℤ.+ ℤ.∣ m ∣ ℤ.* ℤ.+ ℤ.∣ ℤ.+ n ∣              ≡⟨ ℤ.pos-* ℤ.∣ m ∣ ℤ.∣ ℤ.+ n ∣ ⟨
      ℤ.+ (ℤ.∣ m ∣ ℕ.* n)                          ≡⟨⟩
      ℤ.+ (ℤ.∣ m ∣ ℕ.* ℤ.∣ ℤ.+ n ∣)                ≡⟨ cong ℤ.+_ (ℤ.∣i*j∣≡∣i∣*∣j∣ m (ℤ.+ n)) ⟨
      ℤ.+ (ℤ.∣ m ℤ.* ℤ.+ n ∣)                      ∎
    ∣↥p∣↧q≡∣↥p↧q∣ : ∣↥p∣↧q ≡ ℤ.+ ℤ.∣ ↥p↧q ∣
    ∣↥p∣↧q≡∣↥p↧q∣ = ∣m∣n≡∣mn∣ (↥ p) (↧ₙ q)
    ∣↥q∣↧p≡∣↥q↧p∣ : ∣↥q∣↧p ≡ ℤ.+ ℤ.∣ ↥q↧p ∣
    ∣↥q∣↧p≡∣↥q↧p∣ = ∣m∣n≡∣mn∣ (↥ q) (↧ₙ p)

∣p-q∣≤∣p∣+∣q∣ : ∀ p q → ∣ p - q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p-q∣≤∣p∣+∣q∣ p q = begin
  ∣ p   -     q ∣  ≤⟨ ∣p+q∣≤∣p∣+∣q∣ p (- q) ⟩
  ∣ p ∣ + ∣ - q ∣  ≡⟨ cong (∣ p ∣ +_) (∣-p∣≡∣p∣ q) ⟩
  ∣ p ∣ + ∣   q ∣  ∎
  where open ≤-Reasoning

∣p*q∣≡∣p∣*∣q∣ : ∀ p q → ∣ p * q ∣ ≡ ∣ p ∣ * ∣ q ∣
∣p*q∣≡∣p∣*∣q∣ p@record{} q@record{} = begin
  ∣ p * q ∣                                           ≡⟨⟩
  ∣ (↥ p ℤ.* ↥ q) / (↧ₙ p ℕ.* ↧ₙ q) ∣                 ≡⟨⟩
  ℤ.+ ℤ.∣ ↥ p ℤ.* ↥ q ∣ / (↧ₙ p ℕ.* ↧ₙ q)             ≡⟨ cong (λ h → ℤ.+ h / ((↧ₙ p) ℕ.* (↧ₙ q))) (ℤ.∣i*j∣≡∣i∣*∣j∣ (↥ p) (↥ q)) ⟩
  ℤ.+ (ℤ.∣ ↥ p ∣ ℕ.* ℤ.∣ ↥ q ∣) / (↧ₙ p ℕ.* ↧ₙ q)     ≡⟨ cong (_/ (↧ₙ p ℕ.* ↧ₙ q)) (ℤ.pos-* ℤ.∣ ↥ p ∣ ℤ.∣ ↥ q ∣) ⟩
  (ℤ.+ ℤ.∣ ↥ p ∣ ℤ.* ℤ.+ ℤ.∣ ↥ q ∣) / (↧ₙ p ℕ.* ↧ₙ q) ≡⟨⟩
  (ℤ.+ ℤ.∣ ↥ p ∣ / ↧ₙ p) * (ℤ.+ ℤ.∣ ↥ q ∣ / ↧ₙ q)     ≡⟨⟩
  ∣ p ∣ * ∣ q ∣                                       ∎
  where open ≡-Reasoning

∣p*q∣≃∣p∣*∣q∣ : ∀ p q → ∣ p * q ∣ ≃ ∣ p ∣ * ∣ q ∣
∣p*q∣≃∣p∣*∣q∣ p q = ≃-reflexive (∣p*q∣≡∣p∣*∣q∣ p q)

∣∣p∣∣≡∣p∣ : ∀ p → ∣ ∣ p ∣ ∣ ≡ ∣ p ∣
∣∣p∣∣≡∣p∣ p = 0≤p⇒∣p∣≡p (0≤∣p∣ p)

∣∣p∣∣≃∣p∣ : ∀ p → ∣ ∣ p ∣ ∣ ≃ ∣ p ∣
∣∣p∣∣≃∣p∣ p = ≃-reflexive (∣∣p∣∣≡∣p∣ p)

∣-∣-nonNeg : ∀ p → NonNegative ∣ p ∣
∣-∣-nonNeg (mkℚᵘ +[1+ _ ] _) = _
∣-∣-nonNeg (mkℚᵘ +0       _) = _
∣-∣-nonNeg (mkℚᵘ -[1+ _ ] _) = _

------------------------------------------------------------------------
-- Properties of ⌊_⌋ and ⌈_⌉

⌊q⌋≤q : ∀ q → ⌊ q ⌋ / 1 ≤ q
⌊q⌋≤q q@record{} = *≤* (begin
  ⌊ q ⌋ ℤ.* (↧ q) ≤⟨ [n/d]*d≤n (↥ q) (↧ q) ⟩
  (↥ q)           ≡⟨  sym (ℤ.*-identityʳ (↥ q)) ⟩
  (↥ q) ℤ.* (↧ (⌊ q ⌋ / 1)) ∎)
  where
  open ℤ.≤-Reasoning

q<⌊q⌋+1 : ∀ q → q < ℤ.suc ⌊ q ⌋ / 1
q<⌊q⌋+1 q@record{} = *<* ( begin-strict
  ↥q ℤ.* 1ℤ    ≡⟨ ℤ.*-identityʳ ↥q ⟩
  ↥q           ≡⟨ a≡a%n+[a/n]*n ↥q ↧q ⟩
  ℤ.+ (↥q ℤ.% ↧q) ℤ.+ ⌊ q ⌋ ℤ.* ↧q
               <⟨ ℤ.+-monoˡ-< (⌊ q ⌋ ℤ.* ↧q) (ℤ.+<+ (n%d<d ↥q ↧q)) ⟩
  ↧q ℤ.+ ⌊ q ⌋ ℤ.* ↧q
               ≡⟨ cong (λ h → h ℤ.+ ⌊ q ⌋ ℤ.* ↧q) (sym (ℤ.*-identityˡ ↧q)) ⟩
  (1ℤ ℤ.* ↧q) ℤ.+ ⌊ q ⌋ ℤ.* ↧q
               ≡⟨ sym (ℤ.*-distribʳ-+ ↧q 1ℤ (↥q ℤ./ ↧q)) ⟩
  ℤ.suc ⌊ q ⌋ ℤ.* ↧q ∎)
  where
  open ℤ.≤-Reasoning
  ↥q = ↥ q
  ↧q = ↧ q

q≤⌈q⌉ : ∀ q → q ≤ ⌈ q ⌉ / 1
q≤⌈q⌉ q@record{} = subst
  (λ h → h ≤ - (⌊ - q ⌋ / 1))
  (neg-involutive-≡ q)
  (neg-mono-≤ (⌊q⌋≤q (- q)))

⌈q⌉-1<q : ∀ q → ℤ.pred ⌈ q ⌉ / 1 < q
⌈q⌉-1<q q@record{} = subst₂  _<_
  (cong (λ h → h / 1) (ℤ.neg-distrib-+ 1ℤ (⌊ - q ⌋)))
  (neg-involutive-≡ q)
  (neg-mono-< (q<⌊q⌋+1 (- q)))

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.5

neg-mono-<-> = neg-mono-<
{-# WARNING_ON_USAGE neg-mono-<->
"Warning: neg-mono-<-> was deprecated in v1.5.
Please use neg-mono-< instead."
#-}

-- Version 2.0

↥[p/q]≡p = ↥[n/d]≡n
{-# WARNING_ON_USAGE ↥[p/q]≡p
"Warning: ↥[p/q]≡p was deprecated in v2.0.
Please use ↥[n/d]≡n instead."
#-}
↧[p/q]≡q = ↧[n/d]≡d
{-# WARNING_ON_USAGE ↧[p/q]≡q
"Warning: ↧[p/q]≡q was deprecated in v2.0.
Please use ↧[n/d]≡d instead."
#-}
*-monoʳ-≤-pos : ∀ {r} → Positive r → (r *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos r@{mkℚᵘ +[1+ _ ] _} _ = *-monoʳ-≤-nonNeg r
{-# WARNING_ON_USAGE *-monoʳ-≤-pos
"Warning: *-monoʳ-≤-pos was deprecated in v2.0.
Please use *-monoʳ-≤-nonNeg instead."
#-}
*-monoˡ-≤-pos : ∀ {r} → Positive r → (_* r) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos r@{mkℚᵘ +[1+ _ ] _} _ = *-monoˡ-≤-nonNeg r
{-# WARNING_ON_USAGE *-monoˡ-≤-pos
"Warning: *-monoˡ-≤-nonNeg was deprecated in v2.0.
Please use *-monoˡ-≤-nonNeg instead."
#-}
≤-steps = p≤q⇒p≤r+q
{-# WARNING_ON_USAGE ≤-steps
"Warning: ≤-steps was deprecated in v2.0
Please use p≤q⇒p≤r+q instead."
#-}
*-monoˡ-≤-neg : ∀ r → Negative r → (_* r) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-neg r@(mkℚᵘ -[1+ _ ] _) _ = *-monoˡ-≤-nonPos r
{-# WARNING_ON_USAGE *-monoˡ-≤-neg
"Warning: *-monoˡ-≤-neg was deprecated in v2.0.
Please use *-monoˡ-≤-nonPos instead."
#-}
*-monoʳ-≤-neg : ∀ r → Negative r → (r *_) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-neg r@(mkℚᵘ -[1+ _ ] _) _ = *-monoʳ-≤-nonPos r
{-# WARNING_ON_USAGE *-monoʳ-≤-neg
"Warning: *-monoʳ-≤-neg was deprecated in v2.0.
Please use *-monoʳ-≤-nonPos instead."
#-}
*-cancelˡ-<-pos : ∀ r → Positive r → ∀ {p q} → r * p < r * q → p < q
*-cancelˡ-<-pos r@(mkℚᵘ +[1+ _ ] _) r>0 = *-cancelˡ-<-nonNeg r
{-# WARNING_ON_USAGE *-cancelˡ-<-pos
"Warning: *-cancelˡ-<-pos was deprecated in v2.0.
Please use *-cancelˡ-<-nonNeg instead."
#-}
*-cancelʳ-<-pos : ∀ r → Positive r → ∀ {p q} → p * r < q * r → p < q
*-cancelʳ-<-pos r@(mkℚᵘ +[1+ _ ] _) r>0 = *-cancelʳ-<-nonNeg r
{-# WARNING_ON_USAGE *-cancelʳ-<-pos
"Warning: *-cancelʳ-<-pos was deprecated in v2.0.
Please use *-cancelʳ-<-nonNeg instead."
#-}
*-cancelˡ-<-neg : ∀ r → Negative r → ∀ {p q} → r * p < r * q → q < p
*-cancelˡ-<-neg r@(mkℚᵘ -[1+ _ ] _) _ = *-cancelˡ-<-nonPos r
{-# WARNING_ON_USAGE *-cancelˡ-<-neg
"Warning: *-cancelˡ-<-neg was deprecated in v2.0.
Please use *-cancelˡ-<-nonPos instead."
#-}
*-cancelʳ-<-neg : ∀ r → Negative r → ∀ {p q} → p * r < q * r → q < p
*-cancelʳ-<-neg r@(mkℚᵘ -[1+ _ ] _) _ = *-cancelʳ-<-nonPos r
{-# WARNING_ON_USAGE *-cancelʳ-<-neg
"Warning: *-cancelʳ-<-neg was deprecated in v2.0.
Please use *-cancelʳ-<-nonPos instead."
#-}
positive⇒nonNegative : ∀ {p} → Positive p → NonNegative p
positive⇒nonNegative {p} p>0 = pos⇒nonNeg p {{p>0}}
{-# WARNING_ON_USAGE positive⇒nonNegative
"Warning: positive⇒nonNegative was deprecated in v2.0.
Please use pos⇒nonNeg instead."
#-}
negative⇒nonPositive : ∀ {p} → Negative p → NonPositive p
negative⇒nonPositive {p} p<0 = neg⇒nonPos p {{p<0}}
{-# WARNING_ON_USAGE negative⇒nonPositive
"Warning: negative⇒nonPositive was deprecated in v2.0.
Please use neg⇒nonPos instead."
#-}
negative<positive : ∀ {p q} → .(Negative p) → .(Positive q) → p < q
negative<positive {p} {q} p<0 q>0 = neg<pos p q {{p<0}} {{q>0}}
{-# WARNING_ON_USAGE negative<positive
"Warning: negative<positive was deprecated in v2.0.
Please use neg<pos instead."
#-}

{- issue1865/issue1755: raw bundles have moved to `Data.X.Base` -}
open Data.Rational.Unnormalised.Base public
  using (+-rawMagma; +-0-rawGroup; *-rawMagma; +-*-rawNearSemiring; +-*-rawSemiring; +-*-rawRing)
  renaming (+-0-rawMonoid to +-rawMonoid; *-1-rawMonoid to *-rawMonoid)
