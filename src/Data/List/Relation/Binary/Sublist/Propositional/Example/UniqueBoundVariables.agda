------------------------------------------------------------------------
-- The Agda standard library
--
-- A larger example for sublists (propositional case):
-- Simply-typed lambda terms with globally unique variables
-- (both bound and free ones).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Example.UniqueBoundVariables (Base : Set) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Data.List.Base using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (Null; [])
open import Data.List.Relation.Binary.Sublist.Propositional using
  ( _⊆_; []; _∷_; _∷ʳ_
  ; ⊆-refl; ⊆-trans; minimum
  ; from∈; to∈; lookup
  ; ⊆-pushoutˡ; RawPushout
  ; Disjoint; DisjointUnion
  ; separateˡ; Separation
  )
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using
  ( ∷ˡ⁻
  ; ⊆-trans-assoc
  ; from∈∘to∈; from∈∘lookup; lookup-⊆-trans
  ; ⊆-pushoutˡ-is-wpo
  ; Disjoint→DisjointUnion; DisjointUnion→Disjoint
  ; Disjoint-sym; DisjointUnion-inj₁; DisjointUnion-inj₂; DisjointUnion-[]ʳ
  ; weakenDisjoint; weakenDisjointUnion; shrinkDisjointˡ
  ; disjoint⇒disjoint-to-union; DisjointUnion-fromAny∘toAny-∷ˡ⁻
  ; equalize-separators
  )

open import Data.Product using (_,_; proj₁; proj₂)

-- Simple types over a set Base of base types.

data Ty : Set where
  base : (o : Base) → Ty
  _⇒_ : (a b : Ty) → Ty

-- Typing contexts are lists of types.

Cxt = List Ty

variable
  a b : Ty
  Γ Δ : Cxt
  x y : a ∈ Γ

-- The familiar intrinsically well-typed formulation of STLC
-- where a de Bruijn index x is a pointer into the context.

module DeBruijn where

  data Tm (Δ : Cxt) : (a : Ty) → Set where
    var : (x : a ∈ Δ) → Tm Δ a
    abs : (t : Tm (a ∷ Δ) b) → Tm Δ (a ⇒ b)
    app : (t : Tm Δ (a ⇒ b)) (u : Tm Δ a) → Tm Δ b

-- We formalize now intrinsically well-typed STLC with
-- named variables that are globally unique, i.e.,
-- each variable can be bound at most once.

-- List of bound variables of a term.

BVars = List Ty

variable
  B    : BVars
  noBV : Null B

-- There is a single global context Γ of all variables used in the terms.
-- Each list of bound variables B is a sublist of Γ.

variable
  β βₜ βᵤ yβ β\y : B ⊆ Γ

-- Named terms are parameterized by a sublist β : B ⊆ Γ of bound variables.
-- Variables outside B can occur as free variables in a term.
--
--   * Variables x do not contain any bound variables (Null B).
--
--   * The bound variables of an application (t u) is the disjoint union
--     of the bound variables βₜ of t and βᵤ of u.
--
--   * The bound variables β of an abstraction λyt is the disjoint union
--     of the single variable y and the bound variables β\y of t.

module UniquelyNamed where

  data Tm (β : B ⊆ Γ) : (a : Ty) → Set where

    var : (noBV : Null B)
          (x : a ∈ Γ)
        → Tm β a

    abs : (y : a ∈ Γ)
          (y# : DisjointUnion (from∈ y) β\y β)
          (t : Tm β\y b)
        → Tm β (a ⇒ b)

    app : (t : Tm βₜ (a ⇒ b))
          (u : Tm βᵤ a)
          (t#u : DisjointUnion βₜ βᵤ β)
        → Tm β b

  pattern var! x = var [] x

  -- Bound variables β : B ⊆ Γ can be considered in a larger context Γ′
  -- obtained by γ : Γ ⊆ Γ′.  The embedding β′ : B ⊆ Γ′ is simply the
  -- composition of β and γ, and terms can be coerced recursively:

  weakenBV : ∀ {Γ B Γ′} {β : B ⊆ Γ} (γ : Γ ⊆ Γ′)  →
          Tm β a → Tm (⊆-trans β γ) a

  weakenBV γ (var noBV x)  = var noBV (lookup γ x)
  weakenBV γ (app t u t#u) = app (weakenBV γ t) (weakenBV γ u) (weakenDisjointUnion γ t#u)
  weakenBV γ (abs y y# t)  = abs y′ y′# (weakenBV γ t)
    where
    y′  = lookup γ y
    -- Typing:  y′# : DisjointUnion (from∈ y′) (⊆-trans β\y γ) (⊆-trans β γ)
    y′# = subst (λ □ → DisjointUnion □ _ _) (sym (from∈∘lookup _ _)) (weakenDisjointUnion γ y#)

-- We bring de Bruijn terms into scope as Exp.

open DeBruijn renaming (Tm to Exp)
open UniquelyNamed

variable
  t u  : Tm β a
  f e  : Exp Δ a

-- Relating de Bruijn terms and uniquely named terms.
--
-- The judgement δ ⊢ e ~ β ▷ t relates a de Bruijn term e with potentially free variables δ : Δ ⊆ Γ
-- to a named term t with exact bound variables β : B ⊆ Γ.  The intention is to relate exactly
-- the terms with the same meaning.
--
-- The judgement will imply the disjointness of Δ and B.

variable
  δ yδ : Δ ⊆ Γ

data _⊢_~_▷_ {Γ Δ : Cxt} (δ : Δ ⊆ Γ) : ∀{a} (e : Exp Δ a) {B} (β : B ⊆ Γ) (t : Tm β a) → Set where

  -- Free de Bruijn index x : a ∈ Δ is related to free variable y : a ∈ Γ
  -- if δ : Δ ⊆ Γ maps x to y.

  var : ∀{y} (δx≡y : lookup δ x ≡ y) (δ#β : Disjoint δ β)
      → δ ⊢ var x ~ β ▷ var! y

  -- Unnamed lambda δ ⊢ λ.e is related to named lambda y,β ▷ λy.t
  -- if body y,δ ⊢ e is related to body β ▷ t.

  abs : (y#δ : DisjointUnion (from∈ y) δ yδ)
      → (y#β : DisjointUnion (from∈ y) β yβ)
      → yδ ⊢ e ~ β ▷ t
      → δ ⊢ abs e ~ yβ ▷ abs y y#β t

  -- Application δ ⊢ f e is related to application βₜ,βᵤ ▷ t u
  -- if function δ ⊢ f is related to βₜ ▷ t
  -- and argument δ ⊢ e is related to βᵤ ▷ u.

  app : δ ⊢ f ~ βₜ ▷ t
      → δ ⊢ e ~ βᵤ ▷ u
      → (t#u : DisjointUnion βₜ βᵤ β)
      → δ ⊢ app f e ~ β ▷ app t u t#u

-- A dependent substitution lemma for ~.
-- Trivial, but needed because term equality t : Tm β a ≡ t′ : Tm β′ a is heterogeneous,
-- or, more precisely, indexed by a sublist equality β ≡ β′.

subst~ : ∀ {a Δ Γ B} {δ δ′ : Δ ⊆ Γ} {β β′ : B ⊆ Γ}
         {e : Exp Δ a} {t : Tm β a} {t′ : Tm β′ a}
         (δ≡δ′ : δ ≡ δ′)
         (β≡β′ : β ≡ β′)
         (t≡t′ : subst (λ □ → Tm □ a) β≡β′ t ≡ t′) →
         δ ⊢ e ~ β ▷ t →
         δ′ ⊢ e ~ β′ ▷ t′
subst~ refl refl refl d = d

-- The judgement δ ⊢ e ~ β ▷ t relative to Γ
-- can be transported to a bigger context γ : Γ ⊆ Γ′.

weaken~ : ∀{a Δ B Γ Γ′} {δ : Δ ⊆ Γ} {β : B ⊆ Γ} {e : Exp Δ a} {t : Tm β a}  (γ : Γ ⊆ Γ′)
  (let δ′ = ⊆-trans δ γ)
  (let β′ = ⊆-trans β γ)
  (let t′ = weakenBV γ t) →
  δ ⊢ e ~ β ▷ t →
  δ′ ⊢ e ~ β′ ▷ t′
weaken~ γ (var refl δ#β)  = var (lookup-⊆-trans γ _) (weakenDisjoint γ δ#β)
weaken~ γ (abs y#δ y#β d) = abs y′#δ′ y′#β′ (weaken~ γ d)
  where
  y′#δ′ = subst (λ □ → DisjointUnion □ _ _) (sym (from∈∘lookup _ _)) (weakenDisjointUnion γ y#δ)
  y′#β′ = subst (λ □ → DisjointUnion □ _ _) (sym (from∈∘lookup _ _)) (weakenDisjointUnion γ y#β)
weaken~ γ (app dₜ dᵤ t#u) = app (weaken~ γ dₜ) (weaken~ γ dᵤ) (weakenDisjointUnion γ t#u)

-- Lemma:  If δ ⊢ e ~ β ▷ t, then
-- the (potentially) free variables δ of the de Bruijn term e
-- are disjoint from the bound variables β of the named term t.

disjoint-fv-bv : δ ⊢ e ~ β ▷ t → Disjoint δ β
disjoint-fv-bv (var _ δ#β) = δ#β

disjoint-fv-bv {β = yβ} (abs y⊎δ y⊎β d) = δ#yβ
  where
  δ#y     = Disjoint-sym (DisjointUnion→Disjoint y⊎δ)
  yδ#β    = disjoint-fv-bv d
  δ⊆yδ,eq = DisjointUnion-inj₂ y⊎δ
  δ⊆yδ    = proj₁ δ⊆yδ,eq
  eq      = proj₂ δ⊆yδ,eq
  δ#β     = subst (λ □ → Disjoint □ _) eq (shrinkDisjointˡ δ⊆yδ yδ#β)
  δ#yβ    = disjoint⇒disjoint-to-union δ#y δ#β y⊎β

disjoint-fv-bv (app dₜ dᵤ βₜ⊎βᵤ) = disjoint⇒disjoint-to-union δ#βₜ δ#βᵤ βₜ⊎βᵤ
  where
  δ#βₜ = disjoint-fv-bv dₜ
  δ#βᵤ = disjoint-fv-bv dᵤ


-- Translating de Bruijn terms to uniquely named terms.
--
-- Given a de Bruijn term Δ ⊢ e : a, we seek to produce a named term β ▷ t : a
-- that is related to the de Bruijn term.  On the way, we have to compute the
-- global context Γ that hosts all free and bound variables of t.

-- Record (NamedOf e) collects all the outputs of the translation of e.

record NamedOf (e : Exp Δ a) : Set where
  constructor mkNamedOf
  field
    {glob} : Cxt                    -- Γ
    emb    : Δ ⊆ glob               -- δ : Δ ⊆ Γ
    {bv}   : BVars                  -- B
    bound  : bv ⊆ glob              -- β : B ⊆ Γ
    {tm}   : Tm bound a             -- t : Tm β a
    relate : emb ⊢ e ~ bound ▷ tm   -- δ ⊢ e ~ β ▷ t

-- The translation.

dB→Named : (e : Exp Δ a) → NamedOf e

-- For the translation of a variable x : a ∈ Δ, we can pick Γ := Δ and B := [].
-- Δ and B are obviously disjoint subsets of Γ.

dB→Named (var x) = record
    { emb    = ⊆-refl     -- Γ := Δ
    ; bound  = minimum _  -- no bound variables
    ; relate = var refl (DisjointUnion→Disjoint DisjointUnion-[]ʳ)
    }

-- For the translation of an abstraction
--
--   abs (t : Exp (a ∷ Δ) b) : Exp Δ (a ⇒ b)
--
-- we recursively have Γ, B and β : B ⊆ Γ with z,δ : (a ∷ Δ) ⊆ Γ
-- and know that B # a∷Δ.
--
-- We keep Γ and produce embedding δ : Δ ⊆ Γ and bound variables z ⊎ β.

dB→Named {Δ = Δ} {a = a ⇒ b} (abs e) with dB→Named e
... | record{ glob = Γ; emb = zδ; bound = β; relate = d } =
  record
    { glob   = Γ
    ; emb    = δ̇
    ; bound  = proj₁ (proj₂ z⊎β)
    ; relate = abs [a]⊆Γ⊎δ (proj₂ (proj₂ z⊎β)) d
    }
  where
  -- Typings:
  -- zδ   : a ∷ Δ ⊆ Γ
  -- β    : bv ⊆ Γ
  zδ#β    = disjoint-fv-bv d
  z       : a ∈ Γ
  z       = to∈ zδ
  [a]⊆Γ   = from∈ z
  δ̇       = ∷ˡ⁻ zδ
  [a]⊆Γ⊎δ = DisjointUnion-fromAny∘toAny-∷ˡ⁻ zδ
  [a]⊆aΔ  : [ a ] ⊆ (a ∷ Δ)
  [a]⊆aΔ  = refl ∷ minimum _
  eq      : ⊆-trans [a]⊆aΔ zδ ≡ [a]⊆Γ
  eq      = sym (from∈∘to∈ _)
  z#β     : Disjoint [a]⊆Γ β
  z#β     = subst (λ □ → Disjoint □ β) eq (shrinkDisjointˡ [a]⊆aΔ zδ#β)
  z⊎β     = Disjoint→DisjointUnion z#β

-- For the translation of an application (f e) we have by induction hypothesis
-- two independent extensions δ₁ : Δ ⊆ Γ₁ and δ₂ : Δ ⊆ Γ₂
-- and two bound variable lists β₁ : B₁ ⊆ Γ₁ and β₂ : B₂ ⊆ Γ₂.
-- We need to find a common global context Γ such that
--
--   (a) δ : Δ ⊆ Γ and
--   (b) the bound variables embed disjointly as β₁″ : B₁ ⊆ Γ and β₂″ : B₂ ⊆ Γ.
--
-- (a) δ is (eventually) found via a weak pushout of δ₁ and δ₂, giving
-- ϕ₁ : Γ₁ ⊆ Γ₁₂  and  ϕ₂ : Γ₂ ⊆ Γ₁₂.
--
-- (b) The bound variable embeddings
--
--   β₁′ = β₁ϕ₁ : B₁ ⊆ Γ₁₂ and
--   β₂′ = β₂ϕ₂ : B₂ ⊆ Γ₁₂ and
--
-- may be overlapping, but we can separate them by enlarging the global context
-- to Γ with two embeddings
--
--   γ₁ : Γ₁₂ ⊆ Γ
--   γ₂ : Γ₁₂ ⊆ Γ
--
-- such that
--
--   β₁″ = β₁′γ₁ : B₁ ⊆ Γ
--   β₂″ = β₂′γ₂ : B₂ ⊆ Γ
--
-- are disjoint.  Since Δ is disjoint to both B₁ and B₂ we have equality of
--
--   δ₁ϕ₁γ₁ : Δ ⊆ Γ
--   δ₂ϕ₂γ₂ : Δ ⊆ Γ
--
-- Thus, we can return either of them as δ.

dB→Named (app f e) with dB→Named f | dB→Named e
... | mkNamedOf {Γ₁} δ₁ β₁ {t} d₁ | mkNamedOf {Γ₂} δ₂ β₂ {u} d₂ =
  mkNamedOf δ̇ β̇ (app d₁″ d₂″ β₁″⊎β₂″)
  where
  -- Disjointness of δᵢ and βᵢ from induction hypotheses.
  δ₁#β₁   = disjoint-fv-bv d₁
  δ₂#β₂   = disjoint-fv-bv d₂

  -- join δ₁ and δ₂ via weak pushout
  po      = ⊆-pushoutˡ δ₁ δ₂
  Γ₁₂     = RawPushout.upperBound po
  ϕ₁      = RawPushout.leg₁ po
  ϕ₂      = RawPushout.leg₂ po
  δ₁′     = ⊆-trans δ₁ ϕ₁
  δ₂′     = ⊆-trans δ₂ ϕ₂
  β₁′     = ⊆-trans β₁ ϕ₁
  β₂′     = ⊆-trans β₂ ϕ₂
  δ₁′#β₁′ : Disjoint δ₁′ β₁′
  δ₁′#β₁′ = weakenDisjoint ϕ₁ δ₁#β₁
  δ₂′#β₂′ : Disjoint δ₂′ β₂′
  δ₂′#β₂′ = weakenDisjoint ϕ₂ δ₂#β₂
  δ₁′≡δ₂′ : δ₁′ ≡ δ₂′
  δ₁′≡δ₂′ = ⊆-pushoutˡ-is-wpo δ₁ δ₂
  δ₂′#β₁′ : Disjoint δ₂′ β₁′
  δ₂′#β₁′ = subst (λ □ → Disjoint □ β₁′) δ₁′≡δ₂′ δ₁′#β₁′

  -- separate β₁ and β₂
  sep     : Separation β₁′ β₂′
  sep     = separateˡ β₁′ β₂′
  γ₁      = Separation.separator₁ sep
  γ₂      = Separation.separator₂ sep
  β₁″     = Separation.separated₁ sep
  β₂″     = Separation.separated₂ sep

  -- produce their disjoint union
  uni     = Disjoint→DisjointUnion (Separation.disjoint sep)
  β̇       = proj₁ (proj₂ uni)
  β₁″⊎β₂″ : DisjointUnion β₁″ β₂″ β̇
  β₁″⊎β₂″ = proj₂ (proj₂ uni)
  ι₁      = DisjointUnion-inj₁ β₁″⊎β₂″
  ι₂      = DisjointUnion-inj₂ β₁″⊎β₂″

  -- after separation, the FVs are still disjoint from the BVs.
  δ₁″     = ⊆-trans δ₂′ γ₁
  δ₂″     = ⊆-trans δ₂′ γ₂
  δ₁″≡δ₂″ : δ₁″ ≡ δ₂″
  δ₁″≡δ₂″ = equalize-separators δ₂′#β₁′ δ₂′#β₂′
  δ₁″#β₁″ : Disjoint δ₁″ β₁″
  δ₁″#β₁″ = weakenDisjoint γ₁ δ₂′#β₁′
  δ₂″#β₂″ : Disjoint δ₂″ β₂″
  δ₂″#β₂″ = weakenDisjoint γ₂ δ₂′#β₂′
  δ̇       = δ₂″
  δ₂″#β₁″ : Disjoint δ₂″ β₁″
  δ₂″#β₁″ = subst (λ □ → Disjoint □ β₁″) δ₁″≡δ₂″ δ₁″#β₁″
  δ̇#β̇     : Disjoint δ̇ β̇
  δ̇#β̇     = disjoint⇒disjoint-to-union δ₂″#β₁″ δ₂″#β₂″ β₁″⊎β₂″

  -- Combined weakening from Γᵢ to Γ
  γ₁′     = ⊆-trans ϕ₁ γ₁
  γ₂′     = ⊆-trans ϕ₂ γ₂

  -- Weakening and converting the first derivation.
  d₁′     : ⊆-trans δ₁ γ₁′ ⊢ f ~ ⊆-trans β₁ γ₁′ ▷ weakenBV γ₁′ t
  d₁′     = weaken~ γ₁′ d₁
  δ₁≤δ̇    : ⊆-trans δ₁ γ₁′ ≡ ⊆-trans δ₂′ γ₂
  δ₁≤δ̇    = begin
            ⊆-trans δ₁ γ₁′ ≡⟨ ⊆-trans-assoc ⟩
            ⊆-trans δ₁′ γ₁ ≡⟨ cong (λ □ → ⊆-trans □ γ₁) δ₁′≡δ₂′ ⟩
            ⊆-trans δ₂′ γ₁ ≡⟨⟩
            δ₁″            ≡⟨ δ₁″≡δ₂″ ⟩
            δ₂″            ≡⟨⟩
            δ̇              ∎
  β₁≤β₁″  : ⊆-trans β₁ γ₁′ ≡ β₁″
  β₁≤β₁″  = ⊆-trans-assoc
  d₁″     : δ̇ ⊢ f ~ β₁″ ▷ subst (λ □ → Tm □ _) β₁≤β₁″ (weakenBV γ₁′ t)
  d₁″     =  subst~ δ₁≤δ̇ β₁≤β₁″ refl d₁′

  -- Weakening and converting the second derivation.
  d₂′     : ⊆-trans δ₂ γ₂′ ⊢ e ~ ⊆-trans β₂ γ₂′ ▷ weakenBV γ₂′ u
  d₂′     = weaken~ γ₂′ d₂
  β₂≤β₂″  : ⊆-trans β₂ γ₂′ ≡ β₂″
  β₂≤β₂″  = ⊆-trans-assoc
  δ₂≤δ̇    : ⊆-trans δ₂ γ₂′ ≡ δ̇
  δ₂≤δ̇    = ⊆-trans-assoc
  d₂″     : δ̇ ⊢ e ~ β₂″ ▷ subst (λ □ → Tm □ _) β₂≤β₂″ (weakenBV γ₂′ u)
  d₂″     = subst~ δ₂≤δ̇ β₂≤β₂″ refl d₂′
