------------------------------------------------------------------------
-- The Agda standard library
--
-- Example of multi-sorted algebras as indexed containers
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module README.Data.Container.Indexed.MultiSortedAlgebraExample where

------------------------------------------------------------------------
-- Preliminaries
------------------------------------------------------------------------
-- We import library content for indexed containers, standard types,
-- and setoids.

open import Level

open import Data.Container.Indexed.Core using (Container; ⟦_⟧; _◃_/_)
open import Data.Container.Indexed.FreeMonad using (_⋆C_)
open import Data.W.Indexed using (W; sup)

open import Data.Product using (Σ; _×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)

open import Function using (_∘_)
open import Function.Bundles using (Func)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Data.Container.Indexed.Relation.Binary.Equality.Setoid as ICSetoid
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Setoid using (Carrier; _≈_; isEquivalence)
open Func renaming (to to apply)

-- Letter ℓ denotes universe levels.

variable
  ℓ ℓ' ℓˢ ℓᵒ ℓᵃ ℓᵐ ℓᵉ ℓⁱ : Level
  I : Set ℓⁱ
  S : Set ℓˢ

------------------------------------------------------------------------
-- The interpretation of a container (Op ◃ Ar / sort) is
--
--   ⟦ Op ◃ Ar / sort ⟧ X s = Σ[ o ∈ Op s ] ((i : Ar o) → X (sort o i))
--
-- which contains pairs consisting of an operator $o$ and its collection
-- of arguments.  The least fixed point of (X ↦ ⟦ C ⟧ X) is the indexed
-- W-type given by C, and it contains closed first-order terms of the
-- multi-sorted algebra C.

-- We need to interpret indexed containers on Setoids.
-- This definition is missing from the standard library v1.7.

⟦_⟧s : (C : Container I S ℓᵒ ℓᵃ) (ξ : I → Setoid ℓᵐ ℓᵉ) → S → Setoid _ _
⟦ C ⟧s ξ = ICSetoid.setoid ξ C

------------------------------------------------------------------------
-- Multi-sorted algebras
--------------------------------------------------------------------------
-- A multi-sorted algebra is an indexed container.
--
-- * Sorts are indexes.
--
-- * Operators are commands/shapes.
--
-- * Arities/argument are responses/positions.
--
-- Closed terms (initial model) are given by the W type for a container,
-- renamed to μ here (for least fixed-point).

-- We assume a fixed signature (Sort, Ops).

module _ (Sort : Set ℓˢ) (Ops : Container Sort Sort ℓᵒ ℓᵃ) where
  open Container Ops renaming
    ( Command   to  Op
    ; Response  to  Arity
    ; next      to  sort
    )

-- We let letter $s$ range over sorts and $\mathit{op}$ over operators.

  variable
    s s'    : Sort
    op op'  : Op s

------------------------------------------------------------------------
-- Models

  -- A model is given by an interpretation (Den $s$) for each sort $s$
  -- plus an interpretation (den $o$) for each operator $o$.

  record SetModel ℓᵐ : Set (ℓˢ ⊔ ℓᵒ ⊔ ℓᵃ ⊔ suc ℓᵐ) where
    field
      Den : Sort → Set ℓᵐ
      den : {s : Sort} → ⟦ Ops ⟧ Den s → Den s

  -- The setoid model requires operators to respect equality.
  -- The Func record packs a function (apply) with a proof (cong)
  -- that the function maps equals to equals.

  record SetoidModel ℓᵐ ℓᵉ : Set (ℓˢ ⊔ ℓᵒ ⊔ ℓᵃ ⊔ suc (ℓᵐ ⊔ ℓᵉ)) where
    field
      Den  :  Sort → Setoid ℓᵐ ℓᵉ
      den  :  {s : Sort} → Func (⟦ Ops ⟧s Den s) (Den s)


------------------------------------------------------------------------
-- Terms

  -- To obtain terms with free variables, we add additional nullary
  -- operators, each representing a variable.
  --
  -- These are covered in the standard library FreeMonad module,
  -- albeit with the restriction that the operator and variable sets
  -- have the same size.

  Cxt = Sort → Set ℓᵒ

  variable
    Γ Δ : Cxt

  -- Terms with free variables in Var.

  module _ (Var : Cxt) where

    -- We keep the same sorts, but add a nullary operator for each variable.

    Ops⁺ : Container Sort Sort ℓᵒ ℓᵃ
    Ops⁺ = Ops ⋆C Var

    -- Terms with variables are then given by the W-type for the extended container.

    Tm = W Ops⁺

    -- We define nice constructors for variables and operator application
    -- via pattern synonyms.
    -- Note that the $f$ in constructor var' is a function from the empty set,
    -- so it should be uniquely determined.  However, Agda's equality is
    -- more intensional and will not identify all functions from the empty set.
    -- Since we do not make use of the axiom of function extensionality,
    -- we sometimes have to consult the extensional equality of the
    -- function setoid.

    pattern _∙_ op args  = sup (inj₂ op , args)
    pattern var' x f     = sup (inj₁ x , f    )
    pattern var x        = var' x _

  -- Letter $t$ ranges over terms, and $\mathit{ts}$ over argument vectors.

  variable
    t t' t₁ t₂ t₃  :  Tm Γ s
    ts ts'         :  (i : Arity op) → Tm Γ (sort _ i)

------------------------------------------------------------------------
-- Parallel substitutions

  -- A substitution from Δ to Γ holds a term in Γ for each variable in Δ.

  Sub : (Γ Δ : Cxt) → Set _
  Sub Γ Δ = ∀{s} (x : Δ s) → Tm Γ s

  -- Application of a substitution.

  _[_] : (t : Tm Δ s) (σ : Sub Γ Δ) → Tm Γ s
  (var x  )  [ σ ] = σ x
  (op ∙ ts)  [ σ ] = op ∙ λ i → ts i [ σ ]

  -- Letter $σ$ ranges over substitutions.

  variable
    σ σ' : Sub Γ Δ

------------------------------------------------------------------------
-- Interpretation of terms in a model
------------------------------------------------------------------------

  -- Given an algebra $M$ of set-size $ℓ^m$ and equality-size $ℓ^e$,
  -- we define the interpretation of an $s$-sorted term $t$ as element
  -- of $M(s)$ according to an environment $ρ$ that maps each variable
  -- of sort $s'$ to an element of $M(s')$.

  module _ {M : SetoidModel ℓᵐ ℓᵉ} where
    open SetoidModel M

    -- Equality in $M$'s interpretation of sort $s$.

    _≃_ : Den s .Carrier → Den s .Carrier → Set _
    _≃_ {s = s} = Den s ._≈_

    -- An environment for Γ maps each variable $x : Γ(s)$ to an element of $M(s)$.
    -- Equality of environments is defined pointwise.

    Env : Cxt → Setoid _ _
    Env Γ .Carrier   = {s : Sort} (x : Γ s) → Den s .Carrier
    Env Γ ._≈_ ρ ρ'  = {s : Sort} (x : Γ s) → ρ x ≃ ρ' x
    Env Γ .isEquivalence .IsEquivalence.refl   {s = s}   x = Den s .Setoid.refl
    Env Γ .isEquivalence .IsEquivalence.sym       h {s}  x = Den s .Setoid.sym   (h x)
    Env Γ .isEquivalence .IsEquivalence.trans  g  h {s}  x = Den s .Setoid.trans (g x) (h x)

    -- Interpretation of terms is iteration on the W-type.
    -- The standard library offers `iter' (on sets), but we need this to be a Func (on setoids).

    ⦅_⦆ : ∀{s} (t : Tm Γ s) → Func (Env Γ) (Den s)
    ⦅ var x      ⦆ .apply  ρ     = ρ x
    ⦅ var x      ⦆ .cong   ρ=ρ'  = ρ=ρ' x
    ⦅ op ∙ args  ⦆ .apply  ρ     = den .apply  (op    , λ i → ⦅ args i ⦆ .apply ρ)
    ⦅ op ∙ args  ⦆ .cong   ρ=ρ'  = den .cong   (refl  , λ i → ⦅ args i ⦆ .cong ρ=ρ')

    -- An equality between two terms holds in a model
    -- if the two terms are equal under all valuations of their free variables.

    Equal : ∀ {Γ s} (t t' : Tm Γ s) → Set _
    Equal {Γ} {s} t t' = ∀ (ρ : Env Γ .Carrier) → ⦅ t ⦆ .apply ρ ≃ ⦅ t' ⦆ .apply ρ

    -- This notion is an equivalence relation.

    isEquiv : IsEquivalence (Equal {Γ = Γ} {s = s})
    isEquiv {s = s} .IsEquivalence.refl  ρ       = Den s .Setoid.refl
    isEquiv {s = s} .IsEquivalence.sym   e ρ     = Den s .Setoid.sym (e ρ)
    isEquiv {s = s} .IsEquivalence.trans e e' ρ  = Den s .Setoid.trans (e ρ) (e' ρ)

------------------------------------------------------------------------
-- Substitution lemma

    -- Evaluation of a substitution gives an environment.

    ⦅_⦆s : Sub Γ Δ → Env Γ .Carrier → Env Δ .Carrier
    ⦅ σ ⦆s ρ x = ⦅ σ x ⦆ .apply ρ

    -- Substitution lemma: ⦅t[σ]⦆ρ ≃ ⦅t⦆⦅σ⦆ρ

    substitution : (t : Tm Δ s) (σ : Sub Γ Δ) (ρ : Env Γ .Carrier) →
      ⦅ t [ σ ] ⦆ .apply ρ ≃ ⦅ t ⦆ .apply (⦅ σ ⦆s ρ)
    substitution (var x)    σ ρ = Den _ .Setoid.refl
    substitution (op ∙ ts)  σ ρ = den .cong (refl , λ i → substitution (ts i) σ ρ)

------------------------------------------------------------------------
-- Equations

  -- An equation is a pair $t ≐ t'$ of terms of the same sort in the same context.

  record Eq : Set (ℓˢ ⊔ suc ℓᵒ ⊔ ℓᵃ) where
    constructor _≐_
    field
      {cxt}  : Sort → Set ℓᵒ
      {srt}  : Sort
      lhs    : Tm cxt srt
      rhs    : Tm cxt srt

  -- Equation $t ≐ t'$ holding in model $M$.

  _⊧_ : (M : SetoidModel ℓᵐ ℓᵉ) (eq : Eq) → Set _
  M ⊧ (t ≐ t') = Equal {M = M} t t'

  -- Sets of equations are presented as collection E : I → Eq
  -- for some index set I : Set ℓⁱ.

  -- An entailment/consequence $E ⊃ t ≐ t'$ is valid
  -- if $t ≐ t'$ holds in all models that satify equations $E$.

  module _ {ℓᵐ ℓᵉ} where

    _⊃_ : (E : I → Eq) (eq : Eq) → Set _
    E ⊃ eq = ∀ (M : SetoidModel ℓᵐ ℓᵉ) → (∀ i → M ⊧ E i) → M ⊧ eq

  -- Derivations
  --------------

  -- Equalitional logic allows us to prove entailments via the
  -- inference rules for the judgment $E ⊢ Γ ▹ t ≡ t'$.
  -- This could be coined as equational theory over a given
  -- set of equations $E$.
  -- Relation $E ⊢ Γ ▹ \_ ≡ \_$ is the least congruence over the equations $E$.

  data _⊢_▹_≡_ {I : Set ℓⁱ}
    (E : I → Eq) : (Γ : Cxt) (t t' : Tm Γ s) → Set (ℓˢ ⊔ suc ℓᵒ ⊔ ℓᵃ ⊔ ℓⁱ) where

    hyp    :  ∀ i → let t ≐ t' = E i in
              E ⊢ _ ▹ t ≡ t'

    base   :  ∀ (x : Γ s) {f f' : (i : ⊥) → Tm _ (⊥-elim i)} →
              E ⊢ Γ ▹ var' x f ≡ var' x f'

    app    :  (∀ i → E ⊢ Γ ▹ ts i ≡ ts' i) →
              E ⊢ Γ ▹ (op ∙ ts) ≡ (op ∙ ts')

    sub    :  E ⊢ Δ ▹ t ≡ t' →
              ∀ (σ : Sub Γ Δ) →
              E ⊢ Γ ▹ (t [ σ ]) ≡ (t' [ σ ])

    refl   :  ∀ (t : Tm Γ s) →
              E ⊢ Γ ▹ t ≡ t

    sym    :  E ⊢ Γ ▹ t ≡ t' →
              E ⊢ Γ ▹ t' ≡ t

    trans  :  E ⊢ Γ ▹ t₁ ≡ t₂ →
              E ⊢ Γ ▹ t₂ ≡ t₃ →
              E ⊢ Γ ▹ t₁ ≡ t₃

------------------------------------------------------------------------
-- Soundness of the inference rules

  -- We assume a model $M$ that validates all equations in $E$.

  module Soundness {I : Set ℓⁱ} (E : I → Eq) (M : SetoidModel ℓᵐ ℓᵉ)
    (V : ∀ i → M ⊧ E i) where
    open SetoidModel M

    -- In any model $M$ that satisfies the equations $E$,
    -- derived equality is actual equality.

    sound : E ⊢ Γ ▹ t ≡ t' → M ⊧ (t ≐ t')

    sound (hyp i)                        =  V i
    sound (app {op = op} es) ρ           =  den .cong (refl , λ i → sound (es i) ρ)
    sound (sub {t = t} {t' = t'} e σ) ρ  =  begin
      ⦅ t [ σ ]   ⦆ .apply ρ   ≈⟨ substitution {M = M} t σ ρ ⟩
      ⦅ t         ⦆ .apply ρ'  ≈⟨ sound e ρ' ⟩
      ⦅ t'        ⦆ .apply ρ'  ≈⟨ substitution {M = M} t' σ ρ ⟨
      ⦅ t' [ σ ]  ⦆ .apply ρ   ∎
      where
      open SetoidReasoning (Den _)
      ρ' = ⦅ σ ⦆s ρ

    sound (base x {f} {f'})              =  isEquiv {M = M} .IsEquivalence.refl {var' x λ()}

    sound (refl t)                       =  isEquiv {M = M} .IsEquivalence.refl {t}
    sound (sym {t = t} {t' = t'} e)      =  isEquiv {M = M} .IsEquivalence.sym
                                            {x = t} {y = t'} (sound e)
    sound (trans  {t₁ = t₁} {t₂ = t₂}
                  {t₃ = t₃} e e')        =  isEquiv {M = M} .IsEquivalence.trans
                                            {i = t₁} {j = t₂} {k = t₃} (sound e) (sound e')


------------------------------------------------------------------------
-- Birkhoff's completeness theorem
------------------------------------------------------------------------

  -- Birkhoff proved that any equation $t ≐ t'$ is derivable from $E$
  -- when it is valid in all models satisfying $E$.  His proof (for
  -- single-sorted algebras) is a blue print for many more
  -- completeness proofs.  They all proceed by constructing a
  -- universal model aka term model.  In our case, it is terms
  -- quotiented by derivable equality $E ⊢ Γ ▹ \_ ≡ \_$.  It then
  -- suffices to prove that this model satisfies all equations in $E$.

------------------------------------------------------------------------
-- Universal model

  -- A term model for $E$ and $Γ$ interprets sort $s$ by (Tm Γ s) quotiented by $E ⊢ Γ ▹ \_ ≡ \_$.

  module TermModel {I : Set ℓⁱ} (E : I → Eq) where
    open SetoidModel

    -- Tm Γ s quotiented by E⊢Γ▹·≡·.

    TmSetoid : Cxt → Sort → Setoid _ _
    TmSetoid Γ s .Carrier                             = Tm Γ s
    TmSetoid Γ s ._≈_                                 = E ⊢ Γ ▹_≡_
    TmSetoid Γ s .isEquivalence .IsEquivalence.refl   = refl _
    TmSetoid Γ s .isEquivalence .IsEquivalence.sym    = sym
    TmSetoid Γ s .isEquivalence .IsEquivalence.trans  = trans

    -- The interpretation of an operator is simply the operator.
    -- This works because $E⊢Γ▹\_≡\_$ is a congruence.

    tmInterp : ∀ {Γ s} → Func (⟦ Ops ⟧s (TmSetoid Γ) s) (TmSetoid Γ s)
    tmInterp .apply (op , ts) = op ∙ ts
    tmInterp .cong (refl , h) = app h

    -- The term model per context Γ.

    M : Cxt → SetoidModel _ _
    M Γ .Den = TmSetoid Γ
    M Γ .den = tmInterp

    -- The identity substitution σ₀ maps variables to themselves.

    σ₀ : {Γ : Cxt} → Sub Γ Γ
    σ₀ x = var' x  λ()

    -- σ₀ acts indeed as identity.

    identity : (t : Tm Γ s) → E ⊢ Γ ▹ t [ σ₀ ] ≡ t
    identity (var x)    = base x
    identity (op ∙ ts)  = app λ i → identity (ts i)

    -- Evaluation in the term model is substitution $E ⊢ Γ ▹ ⦅t⦆σ ≡ t[σ]$.
    -- This would even hold "up to the nose" if we had function extensionality.

    evaluation : (t : Tm Δ s) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (⦅_⦆ {M = M Γ} t .apply σ) ≡ (t [ σ ])
    evaluation (var x)    σ = refl (σ x)
    evaluation (op ∙ ts)  σ = app (λ i → evaluation (ts i) σ)

    -- The term model satisfies all the equations it started out with.

    satisfies : ∀ i → M Γ ⊧ E i
    satisfies i σ = begin
      ⦅ tₗ ⦆ .apply σ  ≈⟨ evaluation tₗ σ ⟩
      tₗ [ σ ]         ≈⟨ sub (hyp i) σ ⟩
      tᵣ [ σ ]         ≈⟨ evaluation tᵣ σ ⟨
      ⦅ tᵣ ⦆ .apply σ  ∎
      where
      open SetoidReasoning (TmSetoid _ _)
      tₗ  = E i .Eq.lhs
      tᵣ = E i .Eq.rhs

------------------------------------------------------------------------
-- Completeness

-- Birkhoff's completeness theorem \citeyearpar{birkhoff:1935}:
-- Any valid consequence is derivable in the equational theory.

  module Completeness {I : Set ℓⁱ} (E : I → Eq) {Γ s} {t t' : Tm Γ s} where
    open TermModel E

    completeness : E ⊃ (t ≐ t') → E ⊢ Γ ▹ t ≡ t'
    completeness V =     begin
      t                  ≈˘⟨ identity t ⟩
      t  [ σ₀ ]          ≈˘⟨ evaluation t σ₀ ⟩
      ⦅ t   ⦆ .apply σ₀  ≈⟨ V (M Γ) satisfies σ₀ ⟩
      ⦅ t'  ⦆ .apply σ₀  ≈⟨ evaluation t' σ₀ ⟩
      t' [ σ₀ ]          ≈⟨ identity t' ⟩
      t'                 ∎
      where open SetoidReasoning (TmSetoid Γ s)
