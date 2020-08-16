------------------------------------------------------------------------
-- The Agda standard library
--
-- Terms used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Term where

open import Data.List.Base hiding (_++_)
import Data.List.Properties as Lₚ
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.String as String using (String)
open import Reflection.Abstraction
open import Reflection.Argument
open import Reflection.Argument.Information using (visibility)
import Reflection.Argument.Visibility as Visibility; open Visibility.Visibility
import Reflection.Literal as Literal
import Reflection.Meta as Meta
open import Reflection.Name as Name using (Name)
open import Relation.Nullary
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-exporting the builtin type and constructors

open import Agda.Builtin.Reflection as Builtin public
  using (Sort; Type; Term; Clause; Pattern)
open Sort public
open Term public renaming (agda-sort to sort)
open Clause public
open Pattern public

------------------------------------------------------------------------
-- Handy synonyms

Clauses : Set
Clauses = List Clause

Telescope : Set
Telescope = String × Arg Type

-- Pattern synonyms for more compact presentation

pattern vLam s t           = lam visible   (abs s t)
pattern hLam s t           = lam hidden    (abs s t)
pattern iLam s t           = lam instance′ (abs s t)
pattern Π[_∶_]_ s a ty     = pi a (abs s ty)
pattern vΠ[_∶_]_ s a ty    = Π[ s ∶ (vArg a) ] ty
pattern hΠ[_∶_]_ s a ty    = Π[ s ∶ (hArg a) ] ty
pattern iΠ[_∶_]_ s a ty    = Π[ s ∶ (iArg a) ] ty

----------------------------------------------------------------------
-- Utility functions

getName : Term → Maybe Name
getName (con c args) = just c
getName (def f args) = just f
getName _            = nothing

-- "n ⋯⟅∷⟆ xs" prepends "n" visible unknown arguments to the list of
-- arguments. Useful when constructing the list of arguments for a
-- function with initial inferable arguments.
infixr 5 _⋯⟨∷⟩_
_⋯⟨∷⟩_ : ℕ → Args Term → Args Term
zero  ⋯⟨∷⟩ xs = xs
suc i ⋯⟨∷⟩ xs = unknown ⟨∷⟩ (i ⋯⟨∷⟩ xs)
{-# INLINE _⋯⟨∷⟩_ #-}

-- "n ⋯⟅∷⟆ xs" prepends "n" hidden unknown arguments to the list of
-- arguments. Useful when constructing the list of arguments for a
-- function with initial implicit arguments.
infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_ : ℕ → Args Term → Args Term
zero  ⋯⟅∷⟆ xs = xs
suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆ (i ⋯⟅∷⟆ xs)
{-# INLINE _⋯⟅∷⟆_ #-}

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟-AbsTerm_ _≟-AbsType_ _≟-ArgTerm_ _≟-ArgType_ _≟-Args_
        _≟-Clause_ _≟-Telescopes_ _≟-Clauses_ _≟_
        _≟-Sort_ _≟-Pattern_ _≟-ArgPatterns_

_≟-AbsTerm_      : DecidableEquality (Abs Term)
_≟-AbsType_      : DecidableEquality (Abs Type)
_≟-ArgTerm_      : DecidableEquality (Arg Term)
_≟-ArgType_      : DecidableEquality (Arg Type)
_≟-Args_         : DecidableEquality (Args Term)
_≟-Clause_       : DecidableEquality Clause
_≟-Telescope_    : DecidableEquality Telescope
_≟-Telescopes_   : DecidableEquality (List Telescope)
_≟-Clauses_      : DecidableEquality Clauses
_≟_              : DecidableEquality Term
_≟-Sort_         : DecidableEquality Sort
_≟-Pattern_      : DecidableEquality Pattern
_≟-ArgPatterns_  : DecidableEquality (Args Pattern)


-- Decidable equality 'transformers'
-- We need to inline these because the terms are not sized so termination
-- would not obvious if we were to use higher-order functions such as
-- Data.List.Properties' ≡-dec


-- Define _≟-AbsType_ _≟-AbsTerm_ _≟-ArgType_ _≟-ArgTerm_

abs s a ≟-AbsTerm abs s′ a′ = unAbs-dec (a ≟ a′)
abs s a ≟-AbsType abs s′ a′ = unAbs-dec (a ≟ a′)
arg i a ≟-ArgTerm arg i′ a′ = unArg-dec (a ≟ a′)
arg i a ≟-ArgType arg i′ a′ = unArg-dec (a ≟ a′)

-- Define ≟-Args

[]       ≟-Args []       = yes refl
(x ∷ xs) ≟-Args (y ∷ ys) = Lₚ.∷-dec (x ≟-ArgTerm y) (xs ≟-Args ys)
[]       ≟-Args (_ ∷ _)  = no λ()
(_ ∷ _)  ≟-Args []       = no λ()

-- Define _≟-Clause_

module Clause-injective where

  clause-injective₁ : ∀ {tel tel′ ps ps′ t t′} → clause tel ps t ≡ clause tel′ ps′ t′ → tel ≡ tel′
  clause-injective₁ refl = refl

  clause-injective₂ : ∀ {tel tel′ ps ps′ t t′} → clause tel ps t ≡ clause tel′ ps′ t′ → ps ≡ ps′
  clause-injective₂ refl = refl

  clause-injective₃ : ∀ {tel tel′ ps ps′ t t′} → clause tel ps t ≡ clause tel′ ps′ t′ → t ≡ t′
  clause-injective₃ refl = refl

  clause-injective : ∀ {tel tel′ ps ps′ t t′} → clause tel ps t ≡ clause tel′ ps′ t′ → tel ≡ tel′ × ps ≡ ps′ × t ≡ t′
  clause-injective = < clause-injective₁ , < clause-injective₂ , clause-injective₃ > >

  absurd-clause-injective₁ : ∀ {tel tel′ ps ps′} → absurd-clause tel ps ≡ absurd-clause tel′ ps′ → tel ≡ tel′
  absurd-clause-injective₁ refl = refl

  absurd-clause-injective₂ : ∀ {tel tel′ ps ps′} → absurd-clause tel ps ≡ absurd-clause tel′ ps′ → ps ≡ ps′
  absurd-clause-injective₂ refl = refl

  absurd-clause-injective : ∀ {tel tel′ ps ps′} → absurd-clause tel ps ≡ absurd-clause tel′ ps′ → tel ≡ tel′ × ps ≡ ps′
  absurd-clause-injective = < absurd-clause-injective₁ , absurd-clause-injective₂ >

clause tel ps t ≟-Clause clause tel′ ps′ t′ =
  Dec.map′ (uncurry₂′ (cong₃ clause)) Clause-injective.clause-injective (tel ≟-Telescopes tel′ ×-dec ps ≟-ArgPatterns ps′ ×-dec t ≟ t′)
absurd-clause tel ps ≟-Clause absurd-clause tel′ ps′ =
  Dec.map′ (uncurry′ (cong₂ absurd-clause)) Clause-injective.absurd-clause-injective (tel ≟-Telescopes tel′ ×-dec ps ≟-ArgPatterns ps′)
clause _ _ _      ≟-Clause absurd-clause _ _ = no λ()
absurd-clause _ _ ≟-Clause clause _ _ _      = no λ()

-- Define _≟-Telescope_

module Telescope-injective where

  private
    _≡ᵖ_ = _≡_ {A = String × Arg Type}

  tel-injective₁ : ∀ {s s′ x x′} → (s , x) ≡ᵖ (s′ , x′) → s ≡ s′
  tel-injective₁ refl = refl

  tel-injective₂ : ∀ {s s′ x x′} → (s , x) ≡ᵖ (s′ , x′) → x ≡ x′
  tel-injective₂ refl = refl

  tel-injective : ∀ {s s′ x x′} → (s , x) ≡ᵖ (s′ , x′) → s ≡ s′ × x ≡ x′
  tel-injective = < tel-injective₁ , tel-injective₂ >

(s , t) ≟-Telescope (s′ , t′) =
  Dec.map′ (uncurry′ (cong₂ _,_)) Telescope-injective.tel-injective (s String.≟ s′ ×-dec t ≟-ArgType t′)

-- Define _≟-Telescopes_

[]         ≟-Telescopes []              = yes refl
tel ∷ tels ≟-Telescopes tel′ ∷ tels′ =
  Lₚ.∷-dec (tel ≟-Telescope tel′) (tels ≟-Telescopes tels′)

[]     ≟-Telescopes _ ∷ _  = no (λ ())
_ ∷ _  ≟-Telescopes []     = no (λ ())

-- Define _≟-Clauses_

[]       ≟-Clauses []       = yes refl
(x ∷ xs) ≟-Clauses (y ∷ ys) = Lₚ.∷-dec (x ≟-Clause y) (xs ≟-Clauses ys)

[]      ≟-Clauses (_ ∷ _) = no λ()
(_ ∷ _) ≟-Clauses []      = no λ()

-- Define _≟_

module Term-injective where

  private
    _≡ᵗ_ = _≡_ {A = Term}

  var-injective₁ : ∀ {x x′ args args′} → var x args ≡ᵗ var x′ args′ → x ≡ x′
  var-injective₁ refl = refl

  var-injective₂ : ∀ {x x′ args args′} → var x args ≡ᵗ var x′ args′ → args ≡ args′
  var-injective₂ refl = refl

  var-injective :  ∀ {x x′ args args′} → var x args ≡ᵗ var x′ args′ → x ≡ x′ × args ≡ args′
  var-injective = < var-injective₁ , var-injective₂ >

  con-injective₁ : ∀ {c c′ args args′} → con c args ≡ᵗ con c′ args′ → c ≡ c′
  con-injective₁ refl = refl

  con-injective₂ : ∀ {c c′ args args′} → con c args ≡ᵗ con c′ args′ → args ≡ args′
  con-injective₂ refl = refl

  con-injective : ∀ {c c′ args args′} → con c args ≡ᵗ con c′ args′ → c ≡ c′ × args ≡ args′
  con-injective = < con-injective₁ , con-injective₂ >

  def-injective₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
  def-injective₁ refl = refl

  def-injective₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
  def-injective₂ refl = refl

  def-injective : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′ × args ≡ args′
  def-injective = < def-injective₁ , def-injective₂ >

  meta-injective₁ : ∀ {x x′ args args′} → meta x args ≡ meta x′ args′ → x ≡ x′
  meta-injective₁ refl = refl

  meta-injective₂ : ∀ {x x′ args args′} → meta x args ≡ meta x′ args′ → args ≡ args′
  meta-injective₂ refl = refl

  meta-injective : ∀ {x x′ args args′} → meta x args ≡ meta x′ args′ → x ≡ x′ × args ≡ args′
  meta-injective = < meta-injective₁ , meta-injective₂ >

  lam-injective₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
  lam-injective₁ refl = refl

  lam-injective₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
  lam-injective₂ refl = refl

  lam-injective : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′ × t ≡ t′
  lam-injective = < lam-injective₁ , lam-injective₂ >

  pat-lam-injective₁ : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → cs ≡ cs′
  pat-lam-injective₁ refl = refl

  pat-lam-injective₂ : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → args ≡ args′
  pat-lam-injective₂ refl = refl

  pat-lam-injective : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → cs ≡ cs′ × args ≡ args′
  pat-lam-injective = < pat-lam-injective₁ , pat-lam-injective₂ >

  pi-injective₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
  pi-injective₁ refl = refl

  pi-injective₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
  pi-injective₂ refl = refl

  pi-injective : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′ × t₂ ≡ t₂′
  pi-injective = < pi-injective₁ , pi-injective₂ >

  sort-injective : ∀ {x y} → sort x ≡ sort y → x ≡ y
  sort-injective refl = refl

  lit-injective : ∀ {x y} → lit x ≡ lit y → x ≡ y
  lit-injective refl = refl

var x args ≟ var x′ args′ =
  Dec.map′ (uncurry′ (cong₂ var)) Term-injective.var-injective (x ℕ.≟ x′ ×-dec args ≟-Args args′)
con c args ≟ con c′ args′ =
  Dec.map′ (uncurry′ (cong₂ con)) Term-injective.con-injective (c Name.≟ c′ ×-dec args ≟-Args args′)
def f args ≟ def f′ args′ =
  Dec.map′ (uncurry′ (cong₂ def)) Term-injective.def-injective (f Name.≟ f′ ×-dec args ≟-Args args′)
meta x args ≟ meta x′ args′ =
  Dec.map′ (uncurry′ (cong₂ meta)) Term-injective.meta-injective (x Meta.≟ x′   ×-dec args ≟-Args args′)
lam v t    ≟ lam v′ t′    =
  Dec.map′ (uncurry′ (cong₂ lam)) Term-injective.lam-injective (v Visibility.≟ v′ ×-dec t ≟-AbsTerm t′)
pat-lam cs args ≟ pat-lam cs′ args′ =
  Dec.map′ (uncurry′ (cong₂ pat-lam)) Term-injective.pat-lam-injective (cs ≟-Clauses cs′ ×-dec args ≟-Args args′)
pi t₁ t₂   ≟ pi t₁′ t₂′   =
  Dec.map′ (uncurry′ (cong₂ pi)) Term-injective.pi-injective (t₁ ≟-ArgType t₁′  ×-dec t₂ ≟-AbsType t₂′)
sort s     ≟ sort s′      = Dec.map′ (cong sort)  Term-injective.sort-injective (s ≟-Sort s′)
lit l      ≟ lit l′       = Dec.map′ (cong lit)   Term-injective.lit-injective (l Literal.≟ l′)
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

-- Define _≟-Sort_

module Sort-injective where

  set-injective : ∀ {x y} → set x ≡ set y → x ≡ y
  set-injective refl = refl

  slit-injective : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
  slit-injective refl = refl

set t   ≟-Sort set t′  = Dec.map′ (cong set) Sort-injective.set-injective (t ≟ t′)
lit n   ≟-Sort lit n′  = Dec.map′ (cong lit) Sort-injective.slit-injective (n ℕ.≟ n′)
unknown ≟-Sort unknown = yes refl
set _   ≟-Sort lit _   = no λ()
set _   ≟-Sort unknown = no λ()
lit _   ≟-Sort set _   = no λ()
lit _   ≟-Sort unknown = no λ()
unknown ≟-Sort set _   = no λ()
unknown ≟-Sort lit _   = no λ()

-- Define _≟-Pattern_

module Pattern-injective where

  _≡ᵖ_ = _≡_ {A = Pattern}

  con-injective₁ : ∀ {c c′ args args′} → con c args ≡ᵖ con c′ args′ → c ≡ c′
  con-injective₁ refl = refl

  con-injective₂ : ∀ {c c′ args args′} → con c args ≡ᵖ con c′ args′ → args ≡ args′
  con-injective₂ refl = refl

  con-injective : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → c ≡ c′ × args ≡ args′
  con-injective = < con-injective₁ , con-injective₂ >

  var-injective : ∀ {x y} → var x ≡ var y → x ≡ y
  var-injective refl = refl

  lit-injective : ∀ {x y} → Pattern.lit x ≡ lit y → x ≡ y
  lit-injective refl = refl

  proj-injective : ∀ {x y} → proj x ≡ proj y → x ≡ y
  proj-injective refl = refl

  dot-injective : ∀ {x y} → dot x ≡ dot y → x ≡ y
  dot-injective refl = refl


con c ps ≟-Pattern con c′ ps′ = Dec.map′ (uncurry′ (cong₂ con)) Pattern-injective.con-injective (c Name.≟ c′ ×-dec ps ≟-ArgPatterns ps′)
var n    ≟-Pattern var n′     = Dec.map′ (cong var) Pattern-injective.var-injective (n ℕ.≟ n′)
lit l    ≟-Pattern lit l′     = Dec.map′ (cong lit) Pattern-injective.lit-injective (l Literal.≟ l′)
proj a   ≟-Pattern proj a′    = Dec.map′ (cong proj) Pattern-injective.proj-injective (a Name.≟ a′)
dot t    ≟-Pattern dot t′     = Dec.map′ (cong dot) Pattern-injective.dot-injective (t ≟ t′)

con _ _ ≟-Pattern dot _ = no (λ ())
con _ _ ≟-Pattern var _ = no (λ ())
con _ _ ≟-Pattern lit _ = no (λ ())
con _ _ ≟-Pattern proj _ = no (λ ())
con _ _ ≟-Pattern absurd = no (λ ())
dot _ ≟-Pattern con _ _ = no (λ ())
dot _ ≟-Pattern var _ = no (λ ())
dot _ ≟-Pattern lit _ = no (λ ())
dot _ ≟-Pattern proj _ = no (λ ())
dot _ ≟-Pattern absurd = no (λ ())
var s ≟-Pattern con _ _ = no (λ ())
var s ≟-Pattern dot _ = no (λ ())
var s ≟-Pattern lit _ = no (λ ())
var s ≟-Pattern proj _ = no (λ ())
var s ≟-Pattern absurd = no (λ ())
lit _ ≟-Pattern con _ _ = no (λ ())
lit _ ≟-Pattern dot _ = no (λ ())
lit _ ≟-Pattern var _ = no (λ ())
lit _ ≟-Pattern proj _ = no (λ ())
lit _ ≟-Pattern absurd = no (λ ())
proj _ ≟-Pattern con _ _ = no (λ ())
proj _ ≟-Pattern dot _ = no (λ ())
proj _ ≟-Pattern var _ = no (λ ())
proj _ ≟-Pattern lit _ = no (λ ())
proj _ ≟-Pattern absurd = no (λ ())
absurd ≟-Pattern con _ _ = no (λ ())
absurd ≟-Pattern dot _ = no (λ ())
absurd ≟-Pattern var _ = no (λ ())
absurd ≟-Pattern lit _ = no (λ ())
absurd ≟-Pattern proj _ = no (λ ())
absurd ≟-Pattern absurd = yes refl

-- Define _≟-ArgPatterns_

[]             ≟-ArgPatterns []             = yes refl
(arg i p ∷ xs) ≟-ArgPatterns (arg j q ∷ ys) = Lₚ.∷-dec (unArg-dec (p ≟-Pattern q)) (xs ≟-ArgPatterns ys)

[]      ≟-ArgPatterns (_ ∷ _) = no λ()
(_ ∷ _) ≟-ArgPatterns []      = no λ()
