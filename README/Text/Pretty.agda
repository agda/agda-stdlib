------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of pretty printing
------------------------------------------------------------------------

module README.Text.Pretty where

open import Size

open import Data.Bool.Base
open import Data.List.Base as List
open import Data.List.NonEmpty as List⁺
open import Data.Nat.Base
open import Data.Product
open import Data.String.Base hiding (parens; _<+>_)
open import Data.Vec.Base as Vec
open import Function.Base

-- We import the pretty printer and pass 80 to say that we do not want to
-- have lines longer than 80 characters
open import Text.Pretty 80

open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- A small declarative programming language
------------------------------------------------------------------------

-- We define a small programming language where definitions are
-- introduced by providing a non-empty list of equations with:
-- * the same number of patterns on the LHS
-- * a term on the RHS of each equation

-- A pattern is either a variable or a constructor applied to a
-- list of subpatterns

data Pattern (i : Size) : Set where
  var : String → Pattern i
  con : ∀ {j : Size< i} → String → List (Pattern j) → Pattern i

-- A term is either a (bound) variable, the application of a
-- named definition / constructor to a list of arguments or a
-- lambda abstraction

data Term (i : Size) : Set where
  var : String → Term i
  app : ∀ {j : Size< i} → String → List (Term j) → Term i
  lam : ∀ {j : Size< i} → String → Term j → Term i

-- As explained before, a definitions is given by a list of equations

infix 1 _by_
record Def : Set where
  constructor _by_
  field name      : String
        {arity}   : ℕ
        equations : List⁺ (Vec (Pattern _) arity × (Term _))

------------------------------------------------------------------------
-- A pretty printer for this language
------------------------------------------------------------------------

-- First we print patterns. We only wrap a pattern in parentheses if it
-- is compound: i.e. if it is a constructor applied to a non-empty list
-- of subpatterns
-- Lists of patterns are printed separated by a single space.

prettyPattern  : ∀ {i} → Pattern i → Doc
prettyPatterns : ∀ {i} → List (Pattern i) → Doc

prettyPattern (var v)    = text v
prettyPattern (con c []) = text c
prettyPattern (con c ps) = parens $ text c <+> prettyPatterns ps

prettyPatterns = hsep ∘ List.map prettyPattern

-- Next we print terms. The Bool argument tells us whether we are on
-- the RHS of an application (in which case it is sensible to wrap
-- complex subterms in parentheses).

prettyTerm : ∀ {i} → Bool → Term i → Doc
prettyTerm l (var v)    = text v
prettyTerm l (app f []) = text f
prettyTerm l (app f es) = if l then parens else id
  $ text f <+> sep (List.map (prettyTerm true) es)
prettyTerm l (lam x b)  = if l then parens else id
  $ text "λ" <+> text x <> text "." <+> prettyTerm false b

-- We now have all the pieces to print definitions.
-- We print the equations below each other by using vcat.
--
-- The LHS is printed as follows: the name of the function followed by
-- the space-separated list of patterns (if any) and then an equal sign.
--
-- The RHS is printed as a term which is *not* on the RHS of an application.
--
-- Finally we can layout the definition in two different manners:
-- * either LHS followed by RHS
-- * or LHS followed and the RHS as a relative block (indented by 2 spaces)
--   on the next line

prettyDef : Def → Doc
prettyDef (fun by eqs) =
  vcat $ List⁺.toList $ flip List⁺.map eqs $ uncurry $ λ ps e →
  let lhs = text fun <+> (case ps of λ where
              [] → text "="
              _  → prettyPatterns (Vec.toList ps) <+> text "=")
      rhs = prettyTerm false e
  in lhs <+> rhs <|> lhs $$ (spaces 2 <> rhs)

-- The pretty printer is obtained by using the renderer.

pretty : Def → String
pretty = render ∘ prettyDef

------------------------------------------------------------------------
-- Some examples
------------------------------------------------------------------------

-- Our first example is the identity function defined as a λ-abstraction

`id : Def
`id = "id" by ([] , lam "x" (var "x")) ∷ []

_ : pretty `id ≡ "id = λ x. x"
_ = refl

-- If we were to assume that this definition also takes a level (a) and
-- a Set at that level (A) as arguments, we can have a slightly more complex
-- definition like so.

`explicitid : Def
`explicitid = "id" by (var "a" ∷ var "A" ∷ [] , lam "x" (var "x")) ∷ []

_ : pretty `explicitid ≡ "id a A = λ x. x"
_ = refl

-- A more complex example: boolFilter, a function that takes a boolean
-- predicate and a list as arguments and returns a list containing only
-- the values that satisfy the predicate.
-- We use nil and con for [] and _∷_ as our little toy language does not
-- support infix notations.

`filter : Def
`filter = "boolFilter"
  by ( var "P?" ∷ con "nil" [] ∷ []
     , app "nil" []
     )
   ∷ ( var "P?" ∷ con "con" (var "x" ∷ var "xs" ∷ []) ∷ []
     , let rec = app "filter" (var "P?" ∷ var "xs" ∷ []) in
       app "if" (app "P?" (var "x" ∷ [])
         ∷ app "con" (var "x" ∷ rec ∷ [])
         ∷ rec
         ∷ [])
     )
   ∷ []

_ : pretty `filter ≡
  "boolFilter P? nil = nil
\ \boolFilter P? (con x xs) = if (P? x) (con x (filter P? xs)) (filter P? xs)"
_ = refl

-- We can once more revisit this example with its more complex counterpart:
-- boolFilter taking its level and set arguments explicitly (idem for the
-- list constructors nil and con).
-- This time laying out the second equation on a single line would produce a
-- string larger than 80 characters long. So the pretty printer decides to
-- make the RHS a relative block indented by 2 spaces.

`explicitfilter : Def
`explicitfilter = "boolFilter"
  by ( var "a" ∷ var "A" ∷ var "P?" ∷ con "nil" [] ∷ []
     , app "nil" (var "a" ∷ var "A" ∷ [])
     )
   ∷ ( var "a" ∷ var "A" ∷ var "P?" ∷ con "con" (var "x" ∷ var "xs" ∷ []) ∷ []
     , let rec = app "filter" (var "a" ∷ var "A" ∷ var "P?" ∷ var "xs" ∷ []) in
       app "if" (app "P?" (var "x" ∷ [])
         ∷ app "con" (var "a" ∷ var "A" ∷ var "x" ∷ rec ∷ [])
         ∷ rec
         ∷ [])
     )
   ∷ []

_ : pretty `explicitfilter
  ≡ "boolFilter a A P? nil = nil a A
\   \boolFilter a A P? (con x xs) =
\   \  if (P? x) (con a A x (filter a A P? xs)) (filter a A P? xs)"
_ = refl
