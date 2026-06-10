------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nary where

------------------------------------------------------------------------
-- Concrete examples can be found in README.Nary. This file's comments
-- are more focused on the implementation details and the motivations
-- behind the design decisions.
------------------------------------------------------------------------

open import Data.Unit.Base using (⊤)
open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base as Product using (_×_; _,_)
open import Data.Product.Nary.NonDependent
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_$_; _∘′_)
open import Function.Nary.NonDependent
open import Level using (Level; _⊔_; Lift)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong; subst)
open import Relation.Nullary.Negation.Core using (¬_; contradiction′)
open import Relation.Nullary.Decidable.Core as Dec
  using (Dec; yes; no; _because_; _×-dec_)
import Relation.Unary as Unary
  using (Pred; Satisfiable; Universal; IUniversal)

private
  variable
    r : Level
    R : Set r

------------------------------------------------------------------------
-- Generic type constructors

-- `Relation.Unary` provides users with a wealth of combinators to work
-- with indexed sets. We can generalise these to n-ary relations.

-- The crucial thing to notice here is that because we are explicitly
-- considering that the input function should be a `Set`-ended `Arrows`,
-- all the other parameters are inferrable. This allows us to make the
-- number arguments (`n`) implicit.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Quantifiers

-- If we already know how to quantify over one variable, we can easily
-- describe how to quantify over `n` variables by induction over said `n`.

quantₙ : (∀ {i l} {I : Set i} → (I → Set l) → Set (i ⊔ l)) →
         ∀ n {ls} {as : Sets n ls} →
         Arrows n as (Set r) → Set (r ⊔ (⨆ n ls))
quantₙ Q zero     f = f
quantₙ Q (suc n)  f = Q (λ x → quantₙ Q n (f x))

infix 5 ∃⟨_⟩ Π[_] ∀[_]

-- existential quantifier

∃⟨_⟩ : ∀ {n ls r} {as : Sets n ls} → as ⇉ Set r → Set (r ⊔ (⨆ n ls))
∃⟨_⟩ = quantₙ Unary.Satisfiable _

-- explicit universal quantifiers

Π[_] : ∀ {n ls r} {as : Sets n ls} → as ⇉ Set r → Set (r ⊔ (⨆ n ls))
Π[_] = quantₙ Unary.Universal _

-- implicit universal quantifiers

∀[_] : ∀ {n ls r} {as : Sets n ls} → as ⇉ Set r → Set (r ⊔ (⨆ n ls))
∀[_] = quantₙ Unary.IUniversal _

-- ≡?-mapₙ : ∀ n. (con : A₁ → ⋯ → Aₙ → R) →
--                Injectiveₙ n con →
--                ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                Dec (a₁₁ ≡ a₁₂) → ⋯ → Dec (aₙ₁ ≡ aₙ₂) →
--                Dec (con a₁₁ ⋯ aₙ₁ ≡ con a₁₂ ⋯ aₙ₂)

≡?-mapₙ : ∀ n {ls} {as : Sets n ls} (con : Arrows n as R) → Injectiveₙ n con →
          ∀ {l r} → Arrows n (Dec <$> Equalₙ n l r) (Dec (uncurryₙ n con l ≡ uncurryₙ n con r))
≡?-mapₙ n con con-inj =
  curryₙ n λ a?s → let as? = Product-dec n a?s in
  Dec.map′ (cong (uncurryₙ n con) ∘′ fromEqualₙ n) con-inj as?

------------------------------------------------------------------------
-- Substitution

module _ {n r ls} {as : Sets n ls} (P : as ⇉ Set r) where

-- Substitutionₙ : ∀ n. ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                      a₁₁ ≡ a₁₂ → ⋯ → aₙ₁ ≡ aₙ₂ →
--                      P a₁₁ ⋯ aₙ₁ → P a₁₂ ⋯ aₙ₂

  Substitutionₙ : Set (r ⊔ (⨆ n ls))
  Substitutionₙ = ∀ {l r} → Equalₙ n l r ⇉ (uncurryₙ n P l → uncurryₙ n P r)

  substₙ : Substitutionₙ
  substₙ = curryₙ n (subst (uncurryₙ n P) ∘′ fromEqualₙ n)

------------------------------------------------------------------------
-- Pointwise liftings of k-ary operators

-- Rather than having multiple ad-hoc lifting functions for various
-- arities we have a fully generic liftₙ functional which lifts a k-ary
-- operator to work with k n-ary functions whose respective codomains
-- match the domains of the operator.
-- The type of liftₙ is fairly unreadable. Here it is written with ellipsis:

-- liftₙ : ∀ k n. (B₁ → ⋯ → Bₖ → R) →
--                (A₁ → ⋯ → Aₙ → B₁) →
--                       ⋮
--                (A₁ → ⋯ → Aₙ → B₁) →
--                (A₁ → ⋯ → Aₙ → R)

liftₙ : ∀ k n {ls rs} {as : Sets n ls} {bs : Sets k rs} →
        Arrows k bs R → Arrows k (smap _ (Arrows n as) k bs) (Arrows n as R)
liftₙ k n op = curry⊤ₙ k λ fs →
               curry⊤ₙ n λ vs →
               uncurry⊤ₙ k op $
               palg _ _ k (λ f → uncurry⊤ₙ n f vs) fs where

  -- The bulk of the work happens in this auxiliary definition:
  palg : ∀ f (F : ∀ {l} → Set l → Set (f l)) n {ls} {as : Sets n ls} →
         (∀ {l} {r : Set l} → F r → r) → Product⊤ n (smap f F n as) → Product⊤ n as
  palg f F zero    alg ps       = _
  palg f F (suc n) alg (p , ps) = alg p , palg f F n alg ps


-- implication

infixr 6 _⇒_
_⇒_ : ∀ {n} {ls r s} {as : Sets n ls} →
      as ⇉ Set r → as ⇉ Set s → as ⇉ Set (r ⊔ s)
_⇒_ = liftₙ 2 _ (λ A B → A → B)

-- conjunction

infixr 7 _∩_
_∩_ : ∀ {n} {ls r s} {as : Sets n ls} →
      as ⇉ Set r → as ⇉ Set s → as ⇉ Set (r ⊔ s)
_∩_ = liftₙ 2 _ _×_

-- disjunction

infixr 8 _∪_
_∪_ : ∀ {n} {ls r s} {as : Sets n ls} →
      as ⇉ Set r → as ⇉ Set s → as ⇉ Set (r ⊔ s)
_∪_ = liftₙ 2 _ _⊎_

-- negation

∁ : ∀ {n ls r} {as : Sets n ls} → as ⇉ Set r → as ⇉ Set r
∁ = liftₙ 1 _ ¬_


apply⊤ₙ : ∀ {n ls r} {as : Sets n ls} {R : as ⇉ Set r} →
          Π[ R ] → (vs : Product⊤ n as) → uncurry⊤ₙ n R vs
apply⊤ₙ {zero}  prf vs       = prf
apply⊤ₙ {suc n} prf (v , vs) = apply⊤ₙ (prf v) vs

applyₙ : ∀ {n ls r} {as : Sets n ls} {R : as ⇉ Set r} →
         Π[ R ] → (vs : Product n as) → uncurry⊤ₙ n R (toProduct⊤ n vs)
applyₙ {n} prf vs = apply⊤ₙ prf (toProduct⊤ n vs)

iapply⊤ₙ : ∀ {n ls r} {as : Sets n ls} {R : as ⇉ Set r} →
           ∀[ R ] → {vs : Product⊤ n as} → uncurry⊤ₙ n R vs
iapply⊤ₙ {zero}  prf = prf
iapply⊤ₙ {suc n} prf = iapply⊤ₙ {n} prf

iapplyₙ : ∀ {n ls r} {as : Sets n ls} {R : as ⇉ Set r} →
          ∀[ R ] → {vs : Product n as} → uncurry⊤ₙ n R (toProduct⊤ n vs)
iapplyₙ {n} prf = iapply⊤ₙ {n} prf

------------------------------------------------------------------------
-- Properties of N-ary relations

-- Decidability

Decidable : ∀ {n ls r} {as : Sets n ls} → as ⇉ Set r → Set (r ⊔ ⨆ n ls)
Decidable R = Π[ mapₙ _ Dec R ]

-- erasure

⌊_⌋ : ∀ {n ls r} {as : Sets n ls} {R : as ⇉ Set r} → Decidable R → as ⇉ Set r
⌊_⌋ {zero}  R? = Lift _ (Dec.True R?)
⌊_⌋ {suc n} R? a = ⌊ R? a ⌋

-- equivalence between R and its erasure

fromWitness : ∀ {n ls r} {as : Sets n ls} (R : as ⇉ Set r) (R? : Decidable R) →
              ∀[ ⌊ R? ⌋ ⇒ R ]
fromWitness {zero} R R? with R?
... | yes           r = λ _ → r
... | false because _ = λ ()
fromWitness {suc n} R R? = fromWitness (R _) (R? _)

toWitness : ∀ {n ls r} {as : Sets n ls} (R : as ⇉ Set r) (R? : Decidable R) →
              ∀[ R ⇒ ⌊ R? ⌋ ]
toWitness {zero} R R? with R?
... | true because _ = _
... | no          ¬r = contradiction′ ¬r
toWitness {suc n} R R? = toWitness (R _) (R? _)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

≟-mapₙ = ≡?-mapₙ
{-# WARNING_ON_USAGE ≟-mapₙ
"Warning: ≟-mapₙ was deprecated in v2.4.
Please use ≡?-mapₙ instead."
#-}
