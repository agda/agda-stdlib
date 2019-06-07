------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nary where

------------------------------------------------------------------------
-- Concrete examples can be found in README.Nary. This file's comments
-- are more focused on the implementation details and the motivations
-- behind the design decisions.
------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Product.Nary.NonDependent
open import Data.Sum using (_⊎_)
open import Function using (_$_; _∘′_)
open import Function.Nary.NonDependent
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
import Relation.Unary as Unary
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

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

------------------------------------------------------------------------
-- Decidability transformer

-- Injectiveₙ : ∀ n. ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                   con a₁₁ ⋯ aₙ₁ ≡ con a₁₂ ⋯ aₙ₂ →
--                   a₁₁ ≡ a₁₂ × ⋯ × aₙ₁ ≡ aₙ₂

Injectiveₙ : ∀ n {ls} {as : Sets n ls} {R : Set r} →
             Arrows n as R → Set (r Level.⊔ ⨆ n ls)
Injectiveₙ n f = ∀ {l r} → uncurryₙ n f l ≡ uncurryₙ n f r →
                 Product n (Equalₙ n l r)

injectiveₙ : ∀ n {ls} {as : Sets n ls} {R : Set r} (con : Arrows n as R) →
             (∀ {l r} → uncurryₙ n con l ≡ uncurryₙ n con r → l ≡ r) →
             Injectiveₙ n con
injectiveₙ n con con-inj eq = toEqualₙ n (con-inj eq)

-- ≟-mapₙ : ∀ n. (con : A₁ → ⋯ → Aₙ → R) →
--               Injectiveₙ n con →
--               ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--               Dec (a₁₁ ≡ a₁₂) → ⋯ Dec (aₙ₁ ≡ aₙ₂) →
--               Dec (con a₁₁ ⋯ aₙ₁ ≡ con a₁₂ ⋯ aₙ₂)

≟-mapₙ : ∀ n {ls} {as : Sets n ls} (con : Arrows n as R) → Injectiveₙ n con →
         ∀ {l r} → Arrows n (Dec <$> Equalₙ n l r) (Dec (uncurryₙ n con l ≡ uncurryₙ n con r))
≟-mapₙ n con con-inj =
  curryₙ n λ a?s → let as? = Product-dec n a?s in
  Dec.map′ (cong (uncurryₙ n con) ∘′ fromEqualₙ n) con-inj as?

------------------------------------------------------------------------
-- Pointwise liftings of k-ary operators

-- Rather than having multiple ad-hoc lifting functions for various arities
-- we have a fully generic liftₙ functional which lifts a k-ary operator
-- to work with k n-ary functions whose respective codomains match the domains
-- of the operator.
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
