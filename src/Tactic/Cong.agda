------------------------------------------------------------------------
-- The Agda standard library
--
-- A simple tactic for used to automatically compute the function
-- argument to cong.
--
-- The main use for this tactic is getting a similar experience to
-- 'rewrite' during equational reasoning. This allows us to write very
-- succinct proofs:
--
-- example : ∀ m n → m ≡ n → suc (suc (m + 0)) + m ≡ suc (suc n) + (n + 0)
-- example m n eq = begin
--     suc (suc (m + 0)) + m
--   ≡⟨ cong! (+-identityʳ m) ⟩
--     suc (suc m) + m
--   ≡⟨ cong! eq ⟩
--     suc (suc n) + n
--   ≡⟨ cong! (+-identityʳ n) ⟨
--     suc (suc n) + (n + 0)
--   ∎
--
-- Please see README.Tactic.Cong for more details.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Tactic.Cong where

open import Function.Base using (_$_)

open import Data.Bool.Base            using (true; false; if_then_else_; _∧_)
open import Data.Char.Base   as Char  using (toℕ)
open import Data.Float.Base  as Float using (_≡ᵇ_)
open import Data.List.Base   as List  using ([]; _∷_)
open import Data.Maybe.Base  as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base    as ℕ     using (ℕ; zero; suc; _≡ᵇ_; _+_)
open import Data.Unit.Base            using (⊤)
open import Data.Word64.Base   as Word64  using (toℕ)
open import Data.Product.Base         using (_×_; map₁; _,_)
open import Function                  using (flip; case_of_)

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Nullary.Decidable.Core            using (yes; no)

-- 'Data.String.Properties' defines this via 'Dec', so let's use the
-- builtin for maximum speed.
import Agda.Builtin.String as String renaming (primStringEquality to _≡ᵇ_)

open import Reflection
open import Reflection.AST.Abstraction
open import Reflection.AST.AlphaEquality        as Alpha
open import Reflection.AST.Argument             as Arg
open import Reflection.AST.Argument.Information as ArgInfo
open import Reflection.AST.Argument.Visibility  as Visibility
open import Reflection.AST.Literal              as Literal
open import Reflection.AST.Meta                 as Meta
open import Reflection.AST.Name                 as Name
open import Reflection.AST.Term                 as Term
import Reflection.AST.Traversal                 as Traversal

open import Reflection.TCM.Syntax
open import Reflection.TCM.Utilities

-- Marker to keep anti-unification from descending into the wrapped
-- subterm.
--
-- For instance, anti-unification of ⌞ a + b ⌟ + c and b + a + c
-- yields λ ϕ → ϕ + c, as opposed to λ ϕ → ϕ + ϕ + c without ⌞_⌟.
--
-- The marker is only visible to the cong! tactic, which inhibits
-- normalisation. Anywhere else, ⌞ a + b ⌟ reduces to a + b.
--
-- Thus, proving ⌞ a + b ⌟ + c ≡ b + a + c via cong! (+-comm a b)
-- also proves a + b + c ≡ b + a + c.
⌞_⌟ : ∀ {a} {A : Set a} → A → A
⌞_⌟ x = x

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

private
  -- Descend past a variable.
  varDescend : ℕ → ℕ → ℕ
  varDescend ϕ x = if ϕ ℕ.≤ᵇ x then suc x else x

  -- Descend a variable underneath pattern variables.
  patternDescend : ℕ → Pattern → Pattern × ℕ
  patternsDescend : ℕ → Args Pattern → Args Pattern × ℕ

  patternDescend ϕ (con c ps) = map₁ (con c) (patternsDescend ϕ ps)
  patternDescend ϕ (dot t)    = dot t , ϕ
  patternDescend ϕ (var x)    = var (varDescend ϕ x) , suc ϕ
  patternDescend ϕ (lit l)    = lit l , ϕ
  patternDescend ϕ (proj f)   = proj f , ϕ
  patternDescend ϕ (absurd x) = absurd (varDescend ϕ x) , suc ϕ

  patternsDescend ϕ ((arg i p) ∷ ps) =
    let (p' , ϕ') = patternDescend ϕ p
        (ps' , ϕ'') = patternsDescend ϕ' ps
    in (arg i p ∷ ps' , ϕ'')
  patternsDescend ϕ []       =
    [] , ϕ

  -- Construct an error when the goal is not 'x ≡ y' for some 'x' and 'y'.
  notEqualityError : ∀ {A : Set} Term → TC A
  notEqualityError goal = typeError (strErr "Cannot rewrite a goal that is not equality: " ∷ termErr goal ∷ [])

  unificationError : ∀ {A : Set} → TC Term → TC Term → TC A
  unificationError term symTerm = do
    term' ← term
    symTerm' ← symTerm
    -- Don't show the same term twice.
    let symErr = case term' Term.≟ symTerm' of λ where
      (yes _) → []
      (no _) → strErr "\n" ∷ termErr symTerm' ∷ []
    typeError (strErr "cong! failed, tried:\n" ∷ termErr term' ∷ symErr)

  record EqualityGoal : Set where
    constructor equals
    field
      level : Term
      type  : Term
      lhs   : Term
      rhs   : Term

  destructEqualityGoal : Term → TC EqualityGoal
  destructEqualityGoal goal@(def (quote _≡_) (lvl ∷ tp ∷ lhs ∷ rhs ∷ [])) =
    pure $ equals (unArg lvl) (unArg tp) (unArg lhs) (unArg rhs)
  destructEqualityGoal (meta m args) =
    blockOnMeta m
  destructEqualityGoal goal =
    notEqualityError goal

  -- Helper for constructing applications of 'cong'
  `cong : ∀ {a} {A : Set a} {x y : A} → EqualityGoal → Term → x ≡ y → TC Term
  `cong {a = a} {A = A} {x = x} {y = y} eqGoal f x≡y = do
    -- NOTE: We apply all implicit arguments here to ensure that using
    -- equality proofs with implicits don't lead to unsolved metavariable
    -- errors.
    let open EqualityGoal eqGoal
    eq ← quoteTC x≡y
    `a ← quoteTC a
    `A ← quoteTC A
    `x ← quoteTC x
    `y ← quoteTC y
    pure $ def (quote cong) $ `a ⟅∷⟆ `A ⟅∷⟆ level ⟅∷⟆ type ⟅∷⟆ vLam "ϕ" f ⟨∷⟩ `x ⟅∷⟆ `y ⟅∷⟆ eq ⟨∷⟩ []

------------------------------------------------------------------------
-- Anti-Unification
--
-- The core idea of the tactic is that we can compute the input
-- to 'cong' by syntactically anti-unifying both sides of the
-- equality, and then using that to construct a lambda
-- where all the differences are replaced by the lambda-abstracted
-- variable.
--
-- For instance, the two terms 'suc (m + (m + 0)) + (m + 0)' and
-- 'suc (m + m) + (m + 0)' would anti unify to 'suc (m + _) + (m + 0)'
-- which we can then use to construct the lambda 'λ ϕ → suc (m + ϕ) + (m + 0)'.
------------------------------------------------------------------------

private
  antiUnify        : ℕ → Term → Term → Term
  antiUnifyArgs    : ℕ → Args Term → Args Term → Maybe (Args Term)
  antiUnifyClauses : ℕ → Clauses → Clauses → Maybe Clauses
  antiUnifyClause  : ℕ → Clause → Clause → Maybe Clause

  pattern apply-⌞⌟ t = (def (quote ⌞_⌟) (_ ∷ _ ∷ arg _ t ∷ []))

  antiUnify ϕ (var x args) (var y args') with x ℕ.≡ᵇ y | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var ϕ []
  ... | false | just uargs = var ϕ uargs
  ... | true  | just uargs = var (varDescend ϕ x) uargs
  antiUnify ϕ (con c args) (con c' args') with c Name.≡ᵇ c' | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var ϕ []
  ... | false | just uargs = var ϕ []
  ... | true  | just uargs = con c uargs
  antiUnify ϕ (def f args) (apply-⌞⌟ t) = antiUnify ϕ (def f args) t
  antiUnify ϕ (def f args) (def f' args') with f Name.≡ᵇ f' | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var ϕ []
  ... | false | just uargs = var ϕ []
  ... | true  | just uargs = def f uargs
  antiUnify ϕ (lam v (abs s t)) (lam _ (abs _ t')) =
    lam v (abs s (antiUnify (suc ϕ) t t'))
  antiUnify ϕ (pat-lam cs args) (pat-lam cs' args') with antiUnifyClauses ϕ cs cs' | antiUnifyArgs ϕ args args'
  ... | nothing  | _       = var ϕ []
  ... | _        | nothing = var ϕ []
  ... | just ucs | just uargs = pat-lam ucs uargs
  antiUnify ϕ (Π[ s ∶ arg i a ] b) (Π[ _ ∶ arg _ a' ] b') =
    Π[ s ∶ arg i (antiUnify ϕ a a') ] antiUnify (suc ϕ) b b'
  antiUnify ϕ (sort (set t)) (sort (set t')) =
    sort (set (antiUnify ϕ t t'))
  antiUnify ϕ (sort (lit n)) (sort (lit n')) with n ℕ.≡ᵇ n'
  ... | true  = sort (lit n)
  ... | false = var ϕ []
  antiUnify ϕ (sort (propLit n)) (sort (propLit n')) with n ℕ.≡ᵇ n'
  ... | true  = sort (propLit n)
  ... | false = var ϕ []
  antiUnify ϕ (sort (inf n)) (sort (inf n')) with n ℕ.≡ᵇ n'
  ... | true  = sort (inf n)
  ... | false = var ϕ []
  antiUnify ϕ (sort unknown) (sort unknown) =
    sort unknown
  antiUnify ϕ (lit l) (lit l') with l Literal.≡ᵇ l'
  ... | true  = lit l
  ... | false = var ϕ []
  antiUnify ϕ (meta x args) (meta x' args') with x Meta.≡ᵇ x' | antiUnifyArgs ϕ args args'
  ... | _     | nothing    = var ϕ []
  ... | false | _          = var ϕ []
  ... | true  | just uargs = meta x uargs
  antiUnify ϕ unknown unknown = unknown
  antiUnify ϕ _ _ = var ϕ []

  antiUnifyArgs ϕ (arg i t ∷ args) (arg _ t' ∷ args') =
    Maybe.map (arg i (antiUnify ϕ t t') ∷_) (antiUnifyArgs ϕ args args')
  antiUnifyArgs ϕ [] [] =
    just []
  antiUnifyArgs ϕ _ _ =
    nothing

  antiUnifyClause ϕ (clause Γ pats t) (clause Δ pats' t') =
    Maybe.when ((Γ =α= Δ) ∧ (pats =α= pats'))
      let (upats , ϕ') = patternsDescend ϕ pats
      in clause Γ upats (antiUnify ϕ' t t')
  antiUnifyClause ϕ (absurd-clause Γ pats) (absurd-clause Δ pats') =
    Maybe.when ((Γ =α= Δ) ∧ (pats =α= pats')) $
      absurd-clause Γ pats
  antiUnifyClause ϕ _ _ =
    nothing

  antiUnifyClauses ϕ (c ∷ cs) (c' ∷ cs') =
    Maybe.ap (Maybe.map _∷_ (antiUnifyClause ϕ c c')) (antiUnifyClauses ϕ cs cs')
  antiUnifyClauses ϕ _ _ =
    just []


------------------------------------------------------------------------
-- Rewriting
------------------------------------------------------------------------

macro
  cong! : ∀ {a} {A : Set a} {x y : A} → x ≡ y → Term → TC ⊤
  cong! x≡y hole =
    -- NOTE: We avoid doing normalisation here as this tactic
    -- is mainly meant for equational reasoning. In that context,
    -- the endpoints of the equality are already specified in
    -- the form that the -- programmer expects them to be in,
    -- so normalising buys us nothing.
    withNormalisation false $ do
      goal ← inferType hole
      eqGoal ← destructEqualityGoal goal
      let makeTerm = λ lhs rhs → `cong eqGoal (antiUnify 0 lhs rhs) x≡y
      let lhs = EqualityGoal.lhs eqGoal
      let rhs = EqualityGoal.rhs eqGoal
      let term = makeTerm lhs rhs
      let symTerm = makeTerm rhs lhs
      let uni = _>>= flip unify hole
      -- When using ⌞_⌟ with ≡⟨ ... ⟨, (uni term) fails and
      -- (uni symTerm) succeeds.
      catchTC (uni term) $
        catchTC (uni symTerm) $ do
          -- If we failed because of unresolved metas, restart.
          blockOnMetas goal
          -- If we failed for a different reason, show an error.
          unificationError term symTerm
