------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for types of functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

-- Note that these bundles differ from those found elsewhere in other
-- library hierarchies as they take Setoids as parameters. This is
-- because a function is of no use without knowing what its domain and
-- codomain is, as well which equalities are being considered over them.
-- One consequence of this is that they are not built from the
-- definitions found in `Function.Structures` as is usually the case in
-- other library hierarchies, as this would duplicate the equality
-- axioms.

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Bundles where

open import Function.Base using (_∘_)
open import Function.Definitions
import Function.Structures as FunctionStructures
open import Level using (Level; _⊔_; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Function.Consequences.Propositional
open Setoid using (isEquivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid bundles
------------------------------------------------------------------------

module _ (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionStructures _≈₁_ _≈₂_

------------------------------------------------------------------------
-- Bundles with one element

  -- Called `Func` rather than `Function` in order to avoid clashing
  -- with the top-level module.
  record Func : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to   : A → B
      cong : Congruent _≈₁_ _≈₂_ to

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public
      using (module Eq₁; module Eq₂)


  record Injection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to          : A → B
      cong        : Congruent _≈₁_ _≈₂_ to
      injective   : Injective _≈₁_ _≈₂_ to

    function : Func
    function = record
      { to   = to
      ; cong = cong
      }

    open Func function public
      hiding (to; cong)

    isInjection : IsInjection to
    isInjection = record
      { isCongruent = isCongruent
      ; injective   = injective
      }


  record Surjection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to         : A → B
      cong       : Congruent _≈₁_ _≈₂_ to
      surjective : Surjective _≈₁_ _≈₂_ to

    function : Func
    function = record
      { to   = to
      ; cong = cong
      }

    open Func function public
      hiding (to; cong)

    isSurjection : IsSurjection to
    isSurjection = record
      { isCongruent = isCongruent
      ; surjective  = surjective
      }

    open IsSurjection isSurjection public
      using
      ( strictlySurjective
      )

    to⁻ : B → A
    to⁻ = proj₁ ∘ surjective

    to∘to⁻ : ∀ x → to (to⁻ x) ≈₂ x
    to∘to⁻ = proj₂ ∘ strictlySurjective


  record Bijection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      cong      : Congruent _≈₁_ _≈₂_ to
      bijective : Bijective _≈₁_ _≈₂_ to

    injective : Injective _≈₁_ _≈₂_ to
    injective = proj₁ bijective

    surjective : Surjective _≈₁_ _≈₂_ to
    surjective = proj₂ bijective

    injection : Injection
    injection = record
      { cong      = cong
      ; injective = injective
      }

    surjection : Surjection
    surjection = record
      { cong       = cong
      ; surjective = surjective
      }

    open Injection  injection  public using (isInjection)
    open Surjection surjection public using (isSurjection; to⁻;  strictlySurjective)

    isBijection : IsBijection to
    isBijection = record
      { isInjection = isInjection
      ; surjective  = surjective
      }

    open IsBijection isBijection public using (module Eq₁; module Eq₂)


------------------------------------------------------------------------
-- Bundles with two elements

module _ (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionStructures _≈₁_ _≈₂_

  record Equivalence : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : Congruent _≈₁_ _≈₂_ to
      from-cong : Congruent _≈₂_ _≈₁_ from

    toFunction : Func From To
    toFunction = record
      { to = to
      ; cong = to-cong
      }

    open Func toFunction public
      using (module Eq₁; module Eq₂)
      renaming (isCongruent to to-isCongruent)

    fromFunction : Func To From
    fromFunction = record
      { to = from
      ; cong = from-cong
      }

    open Func fromFunction public
      using ()
      renaming (isCongruent to from-isCongruent)


  record LeftInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : Congruent _≈₁_ _≈₂_ to
      from-cong : Congruent _≈₂_ _≈₁_ from
      inverseˡ  : Inverseˡ _≈₁_ _≈₂_ to from

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = to-cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isLeftInverse : IsLeftInverse to from
    isLeftInverse = record
      { isCongruent = isCongruent
      ; from-cong   = from-cong
      ; inverseˡ    = inverseˡ
      }

    open IsLeftInverse isLeftInverse public
      using (module Eq₁; module Eq₂; strictlyInverseˡ; isSurjection)

    equivalence : Equivalence
    equivalence = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      }

    isSplitSurjection : IsSplitSurjection to
    isSplitSurjection = record
      { from = from
      ; isLeftInverse = isLeftInverse
      }

    surjection : Surjection From To
    surjection = record
      { to = to
      ; cong = to-cong
      ; surjective = λ y → from y , inverseˡ
      }



  record RightInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : Congruent _≈₁_ _≈₂_ to
      from-cong : from Preserves _≈₂_ ⟶ _≈₁_
      inverseʳ  : Inverseʳ _≈₁_ _≈₂_ to from

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = to-cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isRightInverse : IsRightInverse to from
    isRightInverse = record
      { isCongruent = isCongruent
      ; from-cong   = from-cong
      ; inverseʳ    = inverseʳ
      }

    open IsRightInverse isRightInverse public
      using (module Eq₁; module Eq₂; strictlyInverseʳ)

    equivalence : Equivalence
    equivalence = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      }


  record Inverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : Congruent _≈₁_ _≈₂_ to
      from-cong : Congruent _≈₂_ _≈₁_ from
      inverse   : Inverseᵇ _≈₁_ _≈₂_ to from

    inverseˡ : Inverseˡ _≈₁_ _≈₂_ to from
    inverseˡ = proj₁ inverse

    inverseʳ : Inverseʳ _≈₁_ _≈₂_ to from
    inverseʳ = proj₂ inverse

    leftInverse : LeftInverse
    leftInverse = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      ; inverseˡ  = inverseˡ
      }

    rightInverse : RightInverse
    rightInverse = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      ; inverseʳ  = inverseʳ
      }

    open LeftInverse leftInverse   public using (isLeftInverse; strictlyInverseˡ)
    open RightInverse rightInverse public using (isRightInverse; strictlyInverseʳ)

    isInverse : IsInverse to from
    isInverse = record
      { isLeftInverse = isLeftInverse
      ; inverseʳ      = inverseʳ
      }

    open IsInverse isInverse public using (module Eq₁; module Eq₂)


------------------------------------------------------------------------
-- Bundles with three elements

  record BiEquivalence : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to         : A → B
      from₁      : B → A
      from₂      : B → A
      to-cong    : Congruent _≈₁_ _≈₂_ to
      from₁-cong : Congruent _≈₂_ _≈₁_ from₁
      from₂-cong : Congruent _≈₂_ _≈₁_ from₂


  record BiInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to          : A → B
      from₁       : B → A
      from₂       : B → A
      to-cong     : Congruent _≈₁_ _≈₂_ to
      from₁-cong  : Congruent _≈₂_ _≈₁_ from₁
      from₂-cong  : Congruent _≈₂_ _≈₁_ from₂
      inverseˡ  : Inverseˡ _≈₁_ _≈₂_ to from₁
      inverseʳ  : Inverseʳ _≈₁_ _≈₂_ to from₂

    to-isCongruent : IsCongruent to
    to-isCongruent = record
      { cong           = to-cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isBiInverse : IsBiInverse to from₁ from₂
    isBiInverse = record
      { to-isCongruent = to-isCongruent
      ; from₁-cong     = from₁-cong
      ; from₂-cong     = from₂-cong
      ; inverseˡ       = inverseˡ
      ; inverseʳ       = inverseʳ
      }

    biEquivalence : BiEquivalence
    biEquivalence = record
      { to-cong    = to-cong
      ; from₁-cong = from₁-cong
      ; from₂-cong = from₂-cong
      }

------------------------------------------------------------------------
-- Other

  -- A left inverse is also known as a “split surjection”.
  --
  -- As the name implies, a split surjection is a special kind of
  -- surjection where the witness generated in the domain in the
  -- function for elements `x₁` and `x₂` are equal if `x₁ ≈ x₂` .
  --
  -- The difference is the `from-cong` law --- generally, the section
  -- (called `Surjection.to⁻` or `SplitSurjection.from`) of a surjection
  -- need not respect equality, whereas it must in a split surjection.
  --
  -- The two notions coincide when the equivalence relation on `B` is
  -- propositional equality (because all functions respect propositional
  -- equality).
  --
  -- For further background on (split) surjections, one may consult any
  -- general mathematical references which work without the principle
  -- of choice. For example:
  --
  --   https://ncatlab.org/nlab/show/split+epimorphism.
  --
  -- The connection to set-theoretic notions with the same names is
  -- justified by the setoid type theory/homotopy type theory
  -- observation/definition that (∃x : A. P) = ∥ Σx : A. P ∥ --- i.e.,
  -- we can read set-theoretic ∃ as squashed/propositionally truncated Σ.
  --
  -- We see working with setoids as working in the MLTT model of a setoid
  -- type theory, in which ∥ X ∥ is interpreted as the setoid with carrier
  -- set X and the equivalence relation that relates all elements.
  -- All maps into ∥ X ∥ respect equality, so in the idiomatic definitions
  -- here, we drop the corresponding trivial `cong` field completely.

  SplitSurjection : Set _
  SplitSurjection = LeftInverse

  module SplitSurjection (splitSurjection : SplitSurjection) =
    LeftInverse splitSurjection

------------------------------------------------------------------------
-- Infix abbreviations for oft-used items
------------------------------------------------------------------------

-- Same naming convention as used for propositional equality below, with
-- appended ₛ (for 'S'etoid).

infixr 0 _⟶ₛ_
_⟶ₛ_ : Setoid a ℓ₁ → Setoid b ℓ₂ → Set _
_⟶ₛ_ = Func

------------------------------------------------------------------------
-- Bundles specialised for propositional equality
------------------------------------------------------------------------

infix 3 _⟶_ _↣_ _↠_ _⤖_ _⇔_ _↩_ _↪_ _↩↪_ _↔_
_⟶_ : Set a → Set b → Set _
A ⟶ B = Func (≡.setoid A) (≡.setoid B)

_↣_ : Set a → Set b → Set _
A ↣ B = Injection (≡.setoid A) (≡.setoid B)

_↠_ : Set a → Set b → Set _
A ↠ B = Surjection (≡.setoid A) (≡.setoid B)

_⤖_ : Set a → Set b → Set _
A ⤖ B = Bijection (≡.setoid A) (≡.setoid B)

_⇔_ : Set a → Set b → Set _
A ⇔ B = Equivalence (≡.setoid A) (≡.setoid B)

_↩_ : Set a → Set b → Set _
A ↩ B = LeftInverse (≡.setoid A) (≡.setoid B)

_↪_ : Set a → Set b → Set _
A ↪ B = RightInverse (≡.setoid A) (≡.setoid B)

_↩↪_ : Set a → Set b → Set _
A ↩↪ B = BiInverse (≡.setoid A) (≡.setoid B)

_↔_ : Set a → Set b → Set _
A ↔ B = Inverse (≡.setoid A) (≡.setoid B)

-- We now define some constructors for the above that
-- automatically provide the required congruency proofs.

module _ {A : Set a} {B : Set b} where

  mk⟶ : (A → B) → A ⟶ B
  mk⟶ to = record
    { to        = to
    ; cong      = ≡.cong to
    }

  mk↣ : ∀ {to : A → B} → Injective _≡_ _≡_ to → A ↣ B
  mk↣ {to} inj = record
    { to         = to
    ; cong      = ≡.cong to
    ; injective = inj
    }

  mk↠ : ∀ {to : A → B} → Surjective _≡_ _≡_ to → A ↠ B
  mk↠ {to} surj = record
    { to         = to
    ; cong       = ≡.cong to
    ; surjective = surj
    }

  mk⤖ : ∀ {to : A → B} → Bijective _≡_ _≡_ to → A ⤖ B
  mk⤖ {to} bij = record
    { to        = to
    ; cong      = ≡.cong to
    ; bijective = bij
    }

  mk⇔ : ∀ (to : A → B) (from : B → A) → A ⇔ B
  mk⇔ to from = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    }

  mk↩ : ∀ {to : A → B} {from : B → A} → Inverseˡ _≡_ _≡_ to from → A ↩ B
  mk↩ {to} {from} invˡ = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    ; inverseˡ  = invˡ
    }

  mk↪ : ∀ {to : A → B} {from : B → A} → Inverseʳ _≡_ _≡_ to from → A ↪ B
  mk↪ {to} {from} invʳ = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    ; inverseʳ  = invʳ
    }

  mk↩↪ : ∀ {to : A → B} {from₁ : B → A} {from₂ : B → A} →
         Inverseˡ _≡_ _≡_ to from₁ → Inverseʳ _≡_ _≡_ to from₂ → A ↩↪ B
  mk↩↪ {to} {from₁} {from₂} invˡ invʳ = record
    { to         = to
    ; from₁      = from₁
    ; from₂      = from₂
    ; to-cong    = ≡.cong to
    ; from₁-cong = ≡.cong from₁
    ; from₂-cong = ≡.cong from₂
    ; inverseˡ   = invˡ
    ; inverseʳ   = invʳ
    }

  mk↔ : ∀ {to : A → B} {from : B → A} → Inverseᵇ _≡_ _≡_ to from → A ↔ B
  mk↔ {to} {from} inv = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    ; inverse   = inv
    }


  -- Strict variant of the above.
  mk↠ₛ : ∀ {to : A → B} → StrictlySurjective _≡_ to → A ↠ B
  mk↠ₛ = mk↠ ∘ strictlySurjective⇒surjective

  mk↔ₛ′ : ∀ (to : A → B) (from : B → A) →
          StrictlyInverseˡ _≡_ to from →
          StrictlyInverseʳ _≡_ to from →
          A ↔ B
  mk↔ₛ′ to from invˡ invʳ = mk↔ {to} {from}
    ( strictlyInverseˡ⇒inverseˡ to invˡ
    , strictlyInverseʳ⇒inverseʳ to invʳ
    )

------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------

-- Alternative syntax for the application of functions

module _ {From : Setoid a ℓ₁} {To : Setoid b ℓ₂} where
  open Setoid

  infixl 5 _⟨$⟩_
  _⟨$⟩_ : Func From To → Carrier From → Carrier To
  _⟨$⟩_ = Func.to
