------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection where

open import Data.List.Base using (List); open List

open import Data.Nat    as ℕ      using (ℕ)
open import Data.String as String using (String)

open import Data.Product
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

import Agda.Builtin.Reflection as Builtin

private
  variable
    a b c d : Level
    A B C D : Set a

------------------------------------------------------------------------
-- Names, Metas, and Literals re-exported publically

open import Reflection.Name as Name using (Name; Names) public
open import Reflection.Meta as Meta using (Meta) public
open import Reflection.Literal as Literal using (Literal) public
open Literal.Literal public
open import Reflection.Argument as Argument
  using ( Arg; arg; Args; module Relevance; module Visibility; module Information
        ; vArg; hArg; iArg
        ) public
open Argument.Relevance.Relevance public
open Argument.Visibility.Visibility public
open Argument.Information.ArgInfo public

open import Reflection.Pattern as Pattern using (Pattern) public

------------------------------------------------------------------------
-- Fixity

open Builtin public using (non-assoc; related; unrelated; fixity)
  renaming ( left-assoc  to assocˡ
           ; right-assoc to assocʳ
           ; primQNameFixity to getFixity)

------------------------------------------------------------------------
-- Terms

open Builtin public using (Abs; abs)

map-Abs : {A B : Set} → (A → B) → Abs A → Abs B
map-Abs f (abs s x) = abs s (f x)

-- Terms.

open Builtin public
  using    ( Type; Term; var; con; def; lam; pat-lam; pi; lit; meta; unknown
           ; Sort; set
           ; Clause; clause; absurd-clause )
  renaming ( agda-sort to sort )

Clauses = List Clause

-- Pattern synonyms for more compact presentation

pattern vLam s t           = lam visible   (abs s t)
pattern hLam s t           = lam hidden    (abs s t)
pattern iLam s t           = lam instance′ (abs s t)
pattern Π[_∶_]_ s a ty     = pi a (abs s ty)
pattern vΠ[_∶_]_ s a ty    = Π[ s ∶ (vArg a) ] ty
pattern hΠ[_∶_]_ s a ty    = Π[ s ∶ (hArg a) ] ty
pattern iΠ[_∶_]_ s a ty    = Π[ s ∶ (iArg a) ] ty
------------------------------------------------------------------------
-- Definitions

open Builtin public
  using    ( Definition
           ; function
           ; data-type
           ; axiom
           )
  renaming ( record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′ )

------------------------------------------------------------------------
-- Type checking monad

-- Type errors
open Builtin public using (ErrorPart; strErr; termErr; nameErr)

-- The monad
open Builtin public
  using ( TC; bindTC; unify; typeError; inferType; checkType
        ; normalise; reduce
        ; catchTC; quoteTC; unquoteTC
        ; getContext; extendContext; inContext; freshName
        ; declareDef; declarePostulate; defineFun; getType; getDefinition
        ; blockOnMeta; commitTC; isMacro; withNormalisation
        ; debugPrint; noConstraints; runSpeculative)
  renaming (returnTC to return)

infixl 1 _>>=_
infixl 1 _>>_

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
ma >>= f = bindTC ma f

_>>_ :  ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
ma >> mb = ma >>= (λ _ → mb)

newMeta : Type → TC Term
newMeta = checkType unknown

------------------------------------------------------------------------
-- Term equality is decidable

-- Boring helper functions.
private

  cong₂′ : ∀ (f : A → B → C) {x y u v} →
         x ≡ y × u ≡ v → f x u ≡ f y v
  cong₂′ f = uncurry (cong₂ f)

  cong₃′ : ∀ (f : A → B → C → D) {x y u v r s} →
         x ≡ y × u ≡ v × r ≡ s → f x u r ≡ f y v s
  cong₃′ f (refl , refl , refl) = refl

  abs₁ : ∀ {i i′} {x x′ : A} → abs i x ≡ abs i′ x′ → i ≡ i′
  abs₁ refl = refl

  abs₂ : ∀ {i i′} {x x′ : A} → abs i x ≡ abs i′ x′ → x ≡ x′
  abs₂ refl = refl

  cons₁ : ∀ {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
  cons₁ refl = refl

  cons₂ : ∀ {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  cons₂ refl = refl

  var₁ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → x ≡ x′
  var₁ refl = refl

  var₂ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → args ≡ args′
  var₂ refl = refl

  con₁ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → c ≡ c′
  con₁ refl = refl

  con₂ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → args ≡ args′
  con₂ refl = refl

  def₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
  def₁ refl = refl

  def₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
  def₂ refl = refl

  meta₁ : ∀ {x x′ args args′} → Term.meta x args ≡ meta x′ args′ → x ≡ x′
  meta₁ refl = refl

  meta₂ : ∀ {x x′ args args′} → Term.meta x args ≡ meta x′ args′ → args ≡ args′
  meta₂ refl = refl

  lam₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
  lam₁ refl = refl

  lam₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
  lam₂ refl = refl

  pat-lam₁ : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → cs ≡ cs′
  pat-lam₁ refl = refl

  pat-lam₂ : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → args ≡ args′
  pat-lam₂ refl = refl

  pi₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
  pi₁ refl = refl

  pi₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
  pi₂ refl = refl

  sort₁ : ∀ {x y} → sort x ≡ sort y → x ≡ y
  sort₁ refl = refl

  lit₁ : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
  lit₁ refl = refl

  set₁ : ∀ {x y} → set x ≡ set y → x ≡ y
  set₁ refl = refl

  slit₁ : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
  slit₁ refl = refl

  clause₁ : ∀ {ps ps′ b b′} → clause ps b ≡ clause ps′ b′ → ps ≡ ps′
  clause₁ refl = refl

  clause₂ : ∀ {ps ps′ b b′} → clause ps b ≡ clause ps′ b′ → b ≡ b′
  clause₂ refl = refl

  absurd-clause₁ : ∀ {ps ps′} → absurd-clause ps ≡ absurd-clause ps′ → ps ≡ ps′
  absurd-clause₁ refl = refl

infix 4 _≟-AbsTerm_ _≟-AbsType_ _≟-ArgTerm_ _≟-ArgType_ _≟-Args_
        _≟-Clause_ _≟-Clauses_ _≟_
        _≟-Sort_

mutual
  _≟-AbsTerm_ : Decidable (_≡_ {A = Abs Term})
  abs s a ≟-AbsTerm abs s′ a′ =
    Dec.map′ (cong₂′ abs)
             < abs₁ , abs₂ >
             (s String.≟ s′ ×-dec a ≟ a′)

  _≟-AbsType_ : Decidable (_≡_ {A = Abs Type})
  abs s a ≟-AbsType abs s′ a′ =
    Dec.map′ (cong₂′ abs)
             < abs₁ , abs₂ >
             (s String.≟ s′ ×-dec a ≟ a′)

  _≟-ArgTerm_ : Decidable (_≡_ {A = Arg Term})
  arg i a ≟-ArgTerm arg i′ a′ = Argument.unArg-dec (a ≟ a′)

  _≟-ArgType_ : Decidable (_≡_ {A = Arg Type})
  arg i a ≟-ArgType arg i′ a′ = Argument.unArg-dec (a ≟ a′)

  _≟-Args_ : Decidable (_≡_ {A = Args Term})
  []       ≟-Args []       = yes refl
  (x ∷ xs) ≟-Args (y ∷ ys) = Dec.map′ (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-ArgTerm y ×-dec xs ≟-Args ys)
  []       ≟-Args (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-Args []       = no λ()

  _≟-Clause_ : Decidable (_≡_ {A = Clause})
  clause ps b ≟-Clause clause ps′ b′ = Dec.map′ (cong₂′ clause) < clause₁ , clause₂ > (ps Pattern.≟s ps′ ×-dec b ≟ b′)
  absurd-clause ps ≟-Clause absurd-clause ps′ = Dec.map′ (cong absurd-clause) absurd-clause₁ (ps Pattern.≟s ps′)
  clause _ _      ≟-Clause absurd-clause _ = no λ()
  absurd-clause _ ≟-Clause clause _ _      = no λ()

  _≟-Clauses_ : Decidable (_≡_ {A = Clauses})
  []       ≟-Clauses []       = yes refl
  (x ∷ xs) ≟-Clauses (y ∷ ys) = Dec.map′ (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-Clause y ×-dec xs ≟-Clauses ys)
  []       ≟-Clauses (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-Clauses []       = no λ()

  _≟_ : Decidable (_≡_ {A = Term})
  var x args ≟ var x′ args′ = Dec.map′ (cong₂′ var) < var₁ , var₂ > (x ℕ.≟ x′          ×-dec args ≟-Args args′)
  con c args ≟ con c′ args′ = Dec.map′ (cong₂′ con) < con₁ , con₂ > (c Name.≟ c′       ×-dec args ≟-Args args′)
  def f args ≟ def f′ args′ = Dec.map′ (cong₂′ def) < def₁ , def₂ > (f Name.≟ f′       ×-dec args ≟-Args args′)
  meta x args ≟ meta x′ args′ = Dec.map′ (cong₂′ meta) < meta₁ , meta₂ > (x Meta.≟ x′   ×-dec args ≟-Args args′)
  lam v t    ≟ lam v′ t′    = Dec.map′ (cong₂′ lam) < lam₁ , lam₂ > (v Visibility.≟ v′ ×-dec t ≟-AbsTerm t′)
  pat-lam cs args ≟ pat-lam cs′ args′ =
                              Dec.map′ (cong₂′ pat-lam) < pat-lam₁ , pat-lam₂ > (cs ≟-Clauses cs′ ×-dec args ≟-Args args′)
  pi t₁ t₂   ≟ pi t₁′ t₂′   = Dec.map′ (cong₂′ pi)  < pi₁  , pi₂  > (t₁ ≟-ArgType t₁′  ×-dec t₂ ≟-AbsType t₂′)
  sort s     ≟ sort s′      = Dec.map′ (cong sort)  sort₁           (s ≟-Sort s′)
  lit l      ≟ lit l′       = Dec.map′ (cong lit)   lit₁           (l Literal.≟ l′)
  unknown    ≟ unknown      = yes refl

  var x args ≟ con c args′ = no λ()
  var x args ≟ def f args′ = no λ()
  var x args ≟ lam v t     = no λ()
  var x args ≟ pi t₁ t₂    = no λ()
  var x args ≟ sort _      = no λ()
  var x args ≟ lit _      = no λ()
  var x args ≟ meta _ _    = no λ()
  var x args ≟ unknown     = no λ()
  con c args ≟ var x args′ = no λ()
  con c args ≟ def f args′ = no λ()
  con c args ≟ lam v t     = no λ()
  con c args ≟ pi t₁ t₂    = no λ()
  con c args ≟ sort _      = no λ()
  con c args ≟ lit _      = no λ()
  con c args ≟ meta _ _    = no λ()
  con c args ≟ unknown     = no λ()
  def f args ≟ var x args′ = no λ()
  def f args ≟ con c args′ = no λ()
  def f args ≟ lam v t     = no λ()
  def f args ≟ pi t₁ t₂    = no λ()
  def f args ≟ sort _      = no λ()
  def f args ≟ lit _      = no λ()
  def f args ≟ meta _ _    = no λ()
  def f args ≟ unknown     = no λ()
  lam v t    ≟ var x args  = no λ()
  lam v t    ≟ con c args  = no λ()
  lam v t    ≟ def f args  = no λ()
  lam v t    ≟ pi t₁ t₂    = no λ()
  lam v t    ≟ sort _      = no λ()
  lam v t    ≟ lit _      = no λ()
  lam v t    ≟ meta _ _    = no λ()
  lam v t    ≟ unknown     = no λ()
  pi t₁ t₂   ≟ var x args  = no λ()
  pi t₁ t₂   ≟ con c args  = no λ()
  pi t₁ t₂   ≟ def f args  = no λ()
  pi t₁ t₂   ≟ lam v t     = no λ()
  pi t₁ t₂   ≟ sort _      = no λ()
  pi t₁ t₂   ≟ lit _      = no λ()
  pi t₁ t₂   ≟ meta _ _    = no λ()
  pi t₁ t₂   ≟ unknown     = no λ()
  sort _     ≟ var x args  = no λ()
  sort _     ≟ con c args  = no λ()
  sort _     ≟ def f args  = no λ()
  sort _     ≟ lam v t     = no λ()
  sort _     ≟ pi t₁ t₂    = no λ()
  sort _     ≟ lit _       = no λ()
  sort _     ≟ meta _ _    = no λ()
  sort _     ≟ unknown     = no λ()
  lit _     ≟ var x args  = no λ()
  lit _     ≟ con c args  = no λ()
  lit _     ≟ def f args  = no λ()
  lit _     ≟ lam v t     = no λ()
  lit _     ≟ pi t₁ t₂    = no λ()
  lit _     ≟ sort _      = no λ()
  lit _     ≟ meta _ _    = no λ()
  lit _     ≟ unknown     = no λ()
  meta _ _   ≟ var x args  = no λ()
  meta _ _   ≟ con c args  = no λ()
  meta _ _   ≟ def f args  = no λ()
  meta _ _   ≟ lam v t     = no λ()
  meta _ _   ≟ pi t₁ t₂    = no λ()
  meta _ _   ≟ sort _      = no λ()
  meta _ _   ≟ lit _       = no λ()
  meta _ _   ≟ unknown     = no λ()
  unknown    ≟ var x args  = no λ()
  unknown    ≟ con c args  = no λ()
  unknown    ≟ def f args  = no λ()
  unknown    ≟ lam v t     = no λ()
  unknown    ≟ pi t₁ t₂    = no λ()
  unknown    ≟ sort _      = no λ()
  unknown    ≟ lit _       = no λ()
  unknown    ≟ meta _ _    = no λ()
  pat-lam _ _ ≟ var x args  = no λ()
  pat-lam _ _ ≟ con c args  = no λ()
  pat-lam _ _ ≟ def f args  = no λ()
  pat-lam _ _ ≟ lam v t     = no λ()
  pat-lam _ _ ≟ pi t₁ t₂    = no λ()
  pat-lam _ _ ≟ sort _      = no λ()
  pat-lam _ _ ≟ lit _       = no λ()
  pat-lam _ _ ≟ meta _ _    = no λ()
  pat-lam _ _ ≟ unknown     = no λ()
  var x args  ≟ pat-lam _ _ = no λ()
  con c args  ≟ pat-lam _ _ = no λ()
  def f args  ≟ pat-lam _ _ = no λ()
  lam v t     ≟ pat-lam _ _ = no λ()
  pi t₁ t₂    ≟ pat-lam _ _ = no λ()
  sort _      ≟ pat-lam _ _ = no λ()
  lit _       ≟ pat-lam _ _ = no λ()
  meta _ _    ≟ pat-lam _ _ = no λ()
  unknown     ≟ pat-lam _ _ = no λ()

  _≟-Sort_ : Decidable (_≡_ {A = Sort})
  set t   ≟-Sort set t′  = Dec.map′ (cong set) set₁ (t ≟ t′)
  lit n   ≟-Sort lit n′  = Dec.map′ (cong lit) slit₁ (n ℕ.≟ n′)
  unknown ≟-Sort unknown = yes refl
  set _   ≟-Sort lit _   = no λ()
  set _   ≟-Sort unknown = no λ()
  lit _   ≟-Sort set _   = no λ()
  lit _   ≟-Sort unknown = no λ()
  unknown ≟-Sort set _   = no λ()
  unknown ≟-Sort lit _   = no λ()


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

returnTC = return
{-# WARNING_ON_USAGE returnTC
"Warning: returnTC was deprecated in v1.1.
Please use return instead."
#-}

lmeta₁ = Literal.meta-injective
{-# WARNING_ON_USAGE lmeta₁
"Warning: lmeta₁ was deprecated in v1.1.
Please use Reflection.Literal's meta-injective instead."
#-}

nat₁ = Literal.nat-injective
{-# WARNING_ON_USAGE nat₁
"Warning: nat₁ was deprecated in v1.1.
Please use Reflection.Literal's nat-injective instead."
#-}

word64₁ = Literal.nat-injective
{-# WARNING_ON_USAGE word64₁
"Warning: word64₁ was deprecated in v1.1.
Please use Reflection.Literal's nat-injective instead."
#-}

float₁ = Literal.nat-injective
{-# WARNING_ON_USAGE float₁
"Warning: float₁ was deprecated in v1.1.
Please use Reflection.Literal's float-injective instead."
#-}

char₁ = Literal.char-injective
{-# WARNING_ON_USAGE char₁
"Warning: char₁ was deprecated in v1.1.
Please use Reflection.Literal's char-injective instead."
#-}

string₁ = Literal.string-injective
{-# WARNING_ON_USAGE string₁
"Warning: string₁ was deprecated in v1.1.
Please use Reflection.Literal's string-injective instead."
#-}

name₁ = Literal.name-injective
{-# WARNING_ON_USAGE name₁
"Warning: name₁ was deprecated in v1.1.
Please use Reflection.Literal's name-injective instead."
#-}

arg₁ = Argument.arg-injective₁
{-# WARNING_ON_USAGE arg₁
"Warning: arg₁ was deprecated in v1.1.
Please use Reflection.Argument's arg-injective₁ instead."
#-}

arg₂ = Argument.arg-injective₂
{-# WARNING_ON_USAGE arg₂
"Warning: arg₂ was deprecated in v1.1.
Please use Reflection.Argument's arg-injective₂ instead."
#-}

pcon₁ = Pattern.con-injective₁
{-# WARNING_ON_USAGE pcon₁
"Warning: pcon₁ was deprecated in v1.1.
Please use Reflection.Pattern's con-injective₁ instead."
#-}

pcon₂ = Pattern.con-injective₂
{-# WARNING_ON_USAGE pcon₂
"Warning: pcon₂ was deprecated in v1.1.
Please use Reflection.Pattern's con-injective₂ instead."
#-}

pvar = Pattern.con-injective₂
{-# WARNING_ON_USAGE pvar
"Warning: pvar was deprecated in v1.1.
Please use Reflection.Pattern's var-injective instead."
#-}

plit₁ = Pattern.con-injective₂
{-# WARNING_ON_USAGE plit₁
"Warning: plit₁ was deprecated in v1.1.
Please use Reflection.Pattern's lit-injective instead."
#-}

pproj₁ = Pattern.con-injective₂
{-# WARNING_ON_USAGE pproj₁
"Warning: pproj₁ was deprecated in v1.1.
Please use Reflection.Pattern's proj-injective instead."
#-}

arg-info₁ = Information.arg-info-injective₁
{-# WARNING_ON_USAGE arg-info₁
"Warning: arg-info₁ was deprecated in v1.1.
Please use Reflection.Argument.Information's arg-info-injective₁ instead."
#-}

arg-info₂ = Information.arg-info-injective₂
{-# WARNING_ON_USAGE arg-info₂
"Warning: arg-info₁ was deprecated in v1.1.
Please use Reflection.Argument.Information's arg-info-injective₂ instead."
#-}

Arg-info = Information.ArgInfo
{-# WARNING_ON_USAGE Arg-info
"Warning: Arg-info was deprecated in v1.1.
Please use Reflection.Argument.Information's ArgInfo instead."
#-}

infix 4 _≟-Lit_ _≟-Name_ _≟-Meta_ _≟-Visibility_ _≟-Relevance_ _≟-Arg-info_
        _≟-Pattern_ _≟-ArgPatterns_

_≟-Lit_ = Literal._≟_
{-# WARNING_ON_USAGE _≟-Lit_
"Warning: _≟-Lit_ was deprecated in v1.1.
Please use Reflection.Literal's _≟_ instead."
#-}

_≟-Name_ = Name._≟_
{-# WARNING_ON_USAGE _≟-Name_
"Warning: _≟-Name_ was deprecated in v1.1.
Please use Reflection.Name's _≟_ instead."
#-}

_≟-Meta_ = Meta._≟_
{-# WARNING_ON_USAGE _≟-Meta_
"Warning: _≟-Meta_ was deprecated in v1.1.
Please use Reflection.Meta's _≟_ instead."
#-}

_≟-Visibility_ = Visibility._≟_
{-# WARNING_ON_USAGE _≟-Visibility_
"Warning: _≟-Visibility_ was deprecated in v1.1.
Please use Reflection.Argument.Visibility's _≟_ instead."
#-}

_≟-Relevance_ = Relevance._≟_
{-# WARNING_ON_USAGE _≟-Relevance_
"Warning: _≟-Relevance_ was deprecated in v1.1.
Please use Reflection.Argument.Relevance's _≟_ instead."
#-}

_≟-Arg-info_ = Information._≟_
{-# WARNING_ON_USAGE _≟-Arg-info_
"Warning: _≟-Arg-info_ was deprecated in v1.1.
Please use Reflection.Argument.Information's _≟_ instead."
#-}

_≟-Pattern_ = Pattern._≟_
{-# WARNING_ON_USAGE _≟-Pattern_
"Warning: _≟-Pattern_ was deprecated in v1.1.
Please use Reflection.Pattern's _≟_ instead."
#-}

_≟-ArgPatterns_ = Pattern._≟s_
{-# WARNING_ON_USAGE _≟-ArgPatterns_
"Warning: _≟-ArgPatterns_ was deprecated in v1.1.
Please use Reflection.Pattern's _≟s_ instead."
#-}

showLiteral = Literal.show
{-# WARNING_ON_USAGE showLiteral
"Warning: showLiteral was deprecated in v1.1.
Please use Reflection.Literal's show instead."
#-}

showName = Name.show
{-# WARNING_ON_USAGE showName
"Warning: showName was deprecated in v1.1.
Please use Reflection.Name's show instead."
#-}

showMeta = Meta.show
{-# WARNING_ON_USAGE showMeta
"Warning: showMeta was deprecated in v1.1.
Please use Reflection.Meta's show instead."
#-}

map-Arg = Argument.map
{-# WARNING_ON_USAGE map-Arg
"Warning: map-Arg was deprecated in v1.1.
Please use Reflection.Argument's map instead."
#-}

map-Args = Argument.map-Args
{-# WARNING_ON_USAGE map-Args
"Warning: map-Args was deprecated in v1.1.
Please use Reflection.Argument's map-Args instead."
#-}

visibility = Information.visibility
{-# WARNING_ON_USAGE visibility
"Warning: visibility was deprecated in v1.1.
Please use Reflection.Argument.Information's visibility instead."
#-}

relevance = Information.relevance
{-# WARNING_ON_USAGE relevance
"Warning: relevance was deprecated in v1.1.
Please use Reflection.Argument.Information's relevance instead."
#-}
