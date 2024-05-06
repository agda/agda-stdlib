------------------------------------------------------------------------
-- The Agda standard library
--
-- Syntax for the building blocks of equational reasoning modules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level; _⊔_; suc)
open import Relation.Nullary.Decidable.Core
  using (Dec; True; toWitness)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.Core using (Rel; REL; _⇒_)
open import Relation.Binary.Definitions
  using (_Respectsʳ_; Asymmetric; Trans; Sym; Reflexive)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_)

-- List of `Reasoning` modules that do not use this framework and so
-- need to be updated manually if the syntax changes.
--
--   Data/Vec/Relation/Binary/Equality/Cast
--   Relation/Binary/HeterogeneousEquality
--   Effect/Monad/Partiality
--   Effect/Monad/Partiality/All
--   Codata/Guarded/Stream/Relation/Binary/Pointwise
--   Function/Reasoning

module Relation.Binary.Reasoning.Syntax where

private
  variable
    a ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C : Set a
    x y z : A

------------------------------------------------------------------------
-- Syntax for beginning a reasoning chain
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Basic begin syntax

module begin-syntax
  (R : REL A B ℓ₁)
  {S : REL A B ℓ₂}
  (reflexive : R ⇒ S)
  where

  infix 1 begin_

  begin_ : R x y → S x y
  begin_ = reflexive

------------------------------------------------------------------------
-- Begin subrelation syntax

-- Sometimes we want to support sub-relations with the
-- same reasoning operators as the main relations (e.g. perform equality
-- proofs with non-strict reasoning operators). This record bundles all
-- the parts needed to extract the sub-relation proofs.
record SubRelation {A : Set a} (R : Rel A ℓ₁) ℓ₂ ℓ₃ : Set (a ⊔ ℓ₁ ⊔ suc ℓ₂ ⊔ suc ℓ₃) where
  field
    S : Rel A ℓ₂
    IsS : R x y → Set ℓ₃
    IsS? : ∀ (xRy : R x y) → Dec (IsS xRy)
    extract : ∀ {xRy : R x y} → IsS xRy → S x y

module begin-subrelation-syntax
  (R : Rel A ℓ₁)
  (sub : SubRelation R ℓ₂ ℓ₃)
  where
  open SubRelation sub

  infix 1 begin_

  begin_ : ∀ {x y} (xRy : R x y) → {s : True (IsS? xRy)} → S x y
  begin_ r {s} = extract (toWitness s)

-- Begin equality syntax
module begin-equality-syntax
  (R : Rel A ℓ₁)
  (sub : SubRelation R ℓ₂ ℓ₃) where

  open begin-subrelation-syntax R sub public
    renaming (begin_ to begin-equality_)

-- Begin apartness syntax
module begin-apartness-syntax
  (R : Rel A ℓ₁)
  (sub : SubRelation R ℓ₂ ℓ₃) where

  open begin-subrelation-syntax R sub public
    renaming (begin_ to begin-apartness_)

-- Begin strict syntax
module begin-strict-syntax
  (R : Rel A ℓ₁)
  (sub : SubRelation R ℓ₂ ℓ₃) where

  open begin-subrelation-syntax R sub public
    renaming (begin_ to begin-strict_)

------------------------------------------------------------------------
-- Begin membership syntax

module begin-membership-syntax
  (R : Rel A ℓ₁)
  (_∈_ : REL B A ℓ₂)
  (resp : _∈_ Respectsʳ R) where

  infix  1 step-∈

  step-∈ : ∀ (x : B) {xs ys} → R xs ys → x ∈ xs → x ∈ ys
  step-∈ x = resp

  syntax step-∈ x  xs⊆ys x∈xs  = x ∈⟨ x∈xs ⟩ xs⊆ys

------------------------------------------------------------------------
-- Begin contradiction syntax

-- Used with asymmetric subrelations to derive a contradiction from a
-- proof that an element is related to itself.
module begin-contradiction-syntax
  (R : Rel A ℓ₁)
  (sub : SubRelation R ℓ₂ ℓ₃)
  (asym : Asymmetric (SubRelation.S sub))
  where

  open SubRelation sub

  infix 1 begin-contradiction_

  begin-contradiction_ : ∀ (xRx : R x x) {s : True (IsS? xRx)} →
                         ∀ {b} {B : Set b} → B
  begin-contradiction_ {x} r {s} = contradiction x<x (asym x<x)
    where
    x<x : S x x
    x<x = extract (toWitness s)

------------------------------------------------------------------------
-- Syntax for continuing a chain of reasoning steps
------------------------------------------------------------------------

-- Note that the arguments to the `step`s are not provided in their
-- "natural" order and syntax declarations are later used to re-order
-- them. This is because the `step` ordering allows the type-checker to
-- better infer the middle argument `y` from the `_IsRelatedTo_`
-- argument (see issue 622).
--
-- This has two practical benefits. First it speeds up type-checking by
-- approximately a factor of 5. Secondly it allows the combinators to be
-- used with macros that use reflection, e.g. `Tactic.RingSolver`, where
-- they need to be able to extract `y` using reflection.

------------------------------------------------------------------------
-- Syntax for unidirectional relations

-- See https://github.com/agda/agda-stdlib/issues/2150 for a possible
-- simplification.

module _
  {R : REL A B ℓ₂}
  (S : REL B C ℓ₁)
  (T : REL A C ℓ₃)
  (step : Trans R S T)
  where

  forward : ∀ (x : A) {y z} → S y z → R x y → T x z
  forward x yRz x∼y = step {x} x∼y yRz

  -- Arbitrary relation syntax
  module ∼-syntax where
    infixr 2 step-∼
    step-∼ = forward
    syntax step-∼ x yRz x∼y = x ∼⟨ x∼y ⟩ yRz


  -- Preorder syntax
  module ≲-syntax where
    infixr 2 step-≲
    step-≲ = forward
    syntax step-≲ x yRz x≲y = x ≲⟨ x≲y ⟩ yRz


  -- Partial order syntax
  module ≤-syntax where
    infixr 2 step-≤
    step-≤ = forward
    syntax step-≤ x yRz x≤y = x ≤⟨ x≤y ⟩ yRz


  -- Strict partial order syntax
  module <-syntax where
    infixr 2 step-<
    step-< = forward
    syntax step-< x yRz x<y = x <⟨ x<y ⟩ yRz


  -- Subset order syntax
  module ⊆-syntax where
    infixr 2 step-⊆
    step-⊆ = forward
    syntax step-⊆ x yRz x⊆y = x ⊆⟨ x⊆y ⟩ yRz


  -- Strict subset order syntax
  module ⊂-syntax where
    infixr 2 step-⊂
    step-⊂ = forward
    syntax step-⊂ x yRz x⊂y = x ⊂⟨ x⊂y ⟩ yRz


  -- Square subset order syntax
  module ⊑-syntax where
    infixr 2 step-⊑
    step-⊑ = forward
    syntax step-⊑ x yRz x⊑y = x ⊑⟨ x⊑y ⟩ yRz


  -- Strict square subset order syntax
  module ⊏-syntax where
    infixr 2 step-⊏
    step-⊏ = forward
    syntax step-⊏ x yRz x⊏y = x ⊏⟨ x⊏y ⟩ yRz


  -- Divisibility syntax
  module ∣-syntax where
    infixr 2 step-∣
    step-∣ = forward
    syntax step-∣ x yRz x∣y = x ∣⟨ x∣y ⟩ yRz


  -- Single-step syntax
  module ⟶-syntax where
    infixr 2 step-⟶
    step-⟶ = forward
    syntax step-⟶ x yRz x∣y = x ⟶⟨ x∣y ⟩ yRz


  -- Multi-step syntax
  module ⟶*-syntax where
    infixr 2 step-⟶*
    step-⟶* = forward
    syntax step-⟶* x yRz x∣y = x ⟶*⟨ x∣y ⟩ yRz


------------------------------------------------------------------------
-- Syntax for bidirectional relations

  module _
    {U : REL B A ℓ₄}
    (sym : Sym U R)
    where

    backward : ∀ x {y z} → S y z → U y x → T x z
    backward x yRz x≈y = forward x yRz (sym x≈y)

    -- Setoid equality syntax
    module ≈-syntax where
      infixr 2 step-≈-⟩ step-≈-⟨
      step-≈-⟩ = forward
      step-≈-⟨ = backward
      syntax step-≈-⟩ x yRz x≈y = x ≈⟨ x≈y ⟩ yRz
      syntax step-≈-⟨ x yRz y≈x = x ≈⟨ y≈x ⟨ yRz

      -- Deprecated
      infixr 2 step-≈ step-≈˘
      step-≈ = step-≈-⟩
      {-# WARNING_ON_USAGE step-≈
      "Warning: step-≈ was deprecated in v2.0.
      Please use step-≈-⟩ instead."
      #-}
      step-≈˘ = step-≈-⟨
      {-# WARNING_ON_USAGE step-≈˘
      "Warning: step-≈˘ and _≈˘⟨_⟩_ was deprecated in v2.0.
      Please use step-≈-⟨ and _≈⟨_⟨_ instead."
      #-}
      syntax step-≈˘ x yRz y≈x = x ≈˘⟨ y≈x ⟩ yRz


    -- Container equality syntax
    module ≋-syntax where
      infixr 2 step-≋-⟩ step-≋-⟨
      step-≋-⟩ = forward
      step-≋-⟨ = backward
      syntax step-≋-⟩ x yRz x≋y = x ≋⟨ x≋y ⟩ yRz
      syntax step-≋-⟨ x yRz y≋x = x ≋⟨ y≋x ⟨ yRz


      -- Don't remove until https://github.com/agda/agda/issues/5617 fixed.
      infixr 2 step-≋ step-≋˘
      step-≋ = step-≋-⟩
      {-# WARNING_ON_USAGE step-≋
      "Warning: step-≋ was deprecated in v2.0.
      Please use step-≋-⟩ instead."
      #-}
      step-≋˘ = step-≋-⟨
      {-# WARNING_ON_USAGE step-≋˘
      "Warning: step-≋˘ and _≋˘⟨_⟩_ was deprecated in v2.0.
      Please use step-≋-⟨ and _≋⟨_⟨_ instead."
      #-}
      syntax step-≋˘ x yRz y≋x = x ≋˘⟨ y≋x ⟩ yRz


    -- Other equality syntax
    module ≃-syntax where
      infixr 2 step-≃-⟩ step-≃-⟨
      step-≃-⟩ = forward
      step-≃-⟨ = backward
      syntax step-≃-⟩ x yRz x≃y = x ≃⟨ x≃y ⟩ yRz
      syntax step-≃-⟨ x yRz y≃x = x ≃⟨ y≃x ⟨ yRz


    -- Apartness relation syntax
    module #-syntax where
      infixr 2 step-#-⟩ step-#-⟨
      step-#-⟩ = forward
      step-#-⟨ = backward
      syntax step-#-⟩ x yRz x#y = x #⟨ x#y ⟩ yRz
      syntax step-#-⟨ x yRz y#x = x #⟨ y#x ⟨ yRz

      -- Don't remove until https://github.com/agda/agda/issues/5617 fixed.
      infixr 2 step-# step-#˘
      step-# = step-#-⟩
      {-# WARNING_ON_USAGE step-#
      "Warning: step-# was deprecated in v2.0.
      Please use step-#-⟩ instead."
      #-}
      step-#˘ = step-#-⟨
      {-# WARNING_ON_USAGE step-#˘
      "Warning: step-#˘ and _#˘⟨_⟩_ was deprecated in v2.0.
      Please use step-#-⟨ and _#⟨_⟨_ instead."
      #-}
      syntax step-#˘ x yRz y#x = x #˘⟨ y#x ⟩ yRz


    -- Bijection syntax
    module ⤖-syntax where
      infixr 2 step-⤖ step-⬻
      step-⤖ = forward
      step-⬻ = backward
      syntax step-⤖ x yRz x⤖y = x ⤖⟨ x⤖y ⟩ yRz
      syntax step-⬻ x yRz y⤖x = x ⬻⟨ y⤖x ⟩ yRz


    -- Inverse syntax
    module ↔-syntax where
      infixr 2 step-↔-⟩ step-↔-⟨
      step-↔-⟩ = forward
      step-↔-⟨ = backward
      syntax step-↔-⟩ x yRz x↔y = x ↔⟨ x↔y ⟩ yRz
      syntax step-↔-⟨ x yRz y↔x = x ↔⟨ y↔x ⟨ yRz


    -- Inverse syntax
    module ↭-syntax where
      infixr 2 step-↭-⟩ step-↭-⟨
      step-↭-⟩ = forward
      step-↭-⟨ = backward
      syntax step-↭-⟩ x yRz x↭y = x ↭⟨ x↭y ⟩ yRz
      syntax step-↭-⟨ x yRz y↭x = x ↭⟨ y↭x ⟨ yRz


      -- Don't remove until https://github.com/agda/agda/issues/5617 fixed.
      infixr 2 step-↭ step-↭˘
      step-↭ = forward
      {-# WARNING_ON_USAGE step-↭
      "Warning: step-↭ was deprecated in v2.0.
      Please use step-↭-⟩ instead."
      #-}
      step-↭˘ = backward
      {-# WARNING_ON_USAGE step-↭˘
      "Warning: step-↭˘ and _↭˘⟨_⟩_ was deprecated in v2.0.
      Please use step-↭-⟨ and _↭⟨_⟨_ instead."
      #-}
      syntax step-↭˘ x yRz y↭x = x ↭˘⟨ y↭x ⟩ yRz

------------------------------------------------------------------------
-- Propositional equality

-- Crucially often the step function cannot just be `subst` or pattern
-- match on `refl` as we often want to compute which constructor the
-- relation begins with, in order for the implicit subrelation
-- arguments to resolve. See `≡-noncomputable-syntax` below if this
-- is not required.
module ≡-syntax
  (R : REL A B ℓ₁)
  (step : Trans _≡_ R R)
  where

  infixr 2 step-≡-⟩  step-≡-∣ step-≡-⟨
  step-≡-⟩ = forward R R step

  step-≡-∣ : ∀ x {y} → R x y → R x y
  step-≡-∣ x xRy = xRy

  step-≡-⟨ = backward R R step ≡.sym

  syntax step-≡-⟩ x yRz x≡y = x ≡⟨ x≡y ⟩ yRz
  syntax step-≡-∣ x xRy     = x ≡⟨⟩ xRy
  syntax step-≡-⟨ x yRz y≡x = x ≡⟨ y≡x ⟨ yRz


  -- Don't remove until https://github.com/agda/agda/issues/5617 fixed.
  infixr 2 step-≡ step-≡˘
  step-≡ = step-≡-⟩
  {-# WARNING_ON_USAGE step-≡
  "Warning: step-≡ was deprecated in v2.0.
  Please use step-≡-⟩ instead."
  #-}
  step-≡˘ = step-≡-⟨
  {-# WARNING_ON_USAGE step-≡˘
  "Warning: step-≡˘ and _≡˘⟨_⟩_ was deprecated in v2.0.
  Please use step-≡-⟨ and _≡⟨_⟨_ instead."
  #-}
  syntax step-≡˘ x yRz y≡x = x ≡˘⟨ y≡x ⟩ yRz


-- Unlike ≡-syntax above, chains of reasoning using this syntax will not
-- reduce when proofs of propositional equality which are not definitionally
-- equal to `refl` are passed.
module ≡-noncomputing-syntax (R : REL A B ℓ₁) where

  private
    step : Trans _≡_ R R
    step ≡.refl xRy = xRy

  open ≡-syntax R step public

------------------------------------------------------------------------
-- Syntax for ending a chain of reasoning
------------------------------------------------------------------------

module end-syntax
  (R : Rel A ℓ₁)
  (reflexive : Reflexive R)
  where

  infix 3 _∎

  _∎ : ∀ x → R x x
  x ∎ = reflexive

