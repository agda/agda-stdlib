
-- The Agda standard library
--
-- Macro for deriving instances of Write
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- NOTE: still figuring things out, just pushing to get over to other device

module Text.Write.Deriving where

-- Much understanding and structure taken from
--   ∙ https://github.com/UlfNorell/agda-prelude/blob/master/src/Tactic/Deriving/Eq.agda
--   ∙ https://github.com/alhassy/gentle-intro-to-reflection

open import Data.Bool.Base using (Bool; false; true; if_then_else_)
open import Data.Char.Properties using (_≡?_)
open import Data.List.Base using (_∷_; []; [_]; List; concat; _++_; zip; wordsBy; length; map; drop; reverse)
open import Data.List.Effectful
open import Data.Maybe.Base using (just; nothing; fromMaybe; Maybe) renaming (_>>=_ to _>>=Maybe_)
open import Data.Nat.Base using (ℕ; suc; _+_; ∣_-_∣′; _∸_; _<ᵇ_)
open import Data.Nat.Instances
open TraversableM using (mapM)
open import Data.String.Base using (toList; fromList; String) renaming (_++_ to _++s_)
open import Data.Unit using (⊤)
open import Data.Product.Base using (_×_; _,_; uncurry; proj₁; proj₂)
open import Function.Base using (_∘_; _$_; case_of_)
open import Reflection
open import Reflection.AST.Show using (showName)
open import Reflection.AST.Term using (Telescope; Clause; unknown; getName; Sort)
open import Reflection.AST.Name using (_≡ᵇ_)
open import Reflection.AST.Argument using (vArg; hArg; iArg; unArg)
open import Reflection.TCM
open import Reflection.TCM.Effectful using () renaming (monad to monadTCM)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Text.Write using (Write; Char; Precedence; writeParens)
open import Level using (Level; suc; zero)

open Clause
open Pattern
open Sort
open Write {{...}}

private
  debugPrefix : String
  debugPrefix = "text.write.deriving"

  debugOut : ℕ → List ErrorPart → TC ⊤
  debugOut = debugPrint debugPrefix

-- TODO:
  -- Move machinery, etc..., to appropriate (possibly new) modules
  -- Kill dead code
  -- Improve readability

------------------------------------------------------------------------
-- List Char utils

last : {a : Level} {A : Set a} → A → List A → A
last x [] = x
last x (y ∷ ys) = last y ys

unqualify : List Char → List Char
unqualify str = last str (wordsBy (_≡?_ '.') str)

------------------------------------------------------------------------
-- Weakening

-- taken directly from agda-prelude
private
  Wk : Set → Set
  Wk A = ℕ → ℕ → A → A

  wkVar : Wk ℕ
  wkVar lo k x = if x <ᵇ lo then x else x + k

  wkArgs    : Wk (List (Arg Term))
  wkArg     : Wk (Arg Term)
  wkSort    : Wk Sort
  wkClauses : Wk (List Clause)
  wkClause  : Wk Clause
  wkAbsTerm : Wk (Abs Term)

  wk : Wk Term
  wk lo k (var x args)  = var (wkVar lo k x) (wkArgs lo k args)
  wk lo k (con c args)  = con c (wkArgs lo k args)
  wk lo k (def f args)  = def f (wkArgs lo k args)
  wk lo k (meta x args) = meta x (wkArgs lo k args)
  wk lo k (lam v t)     = lam v (wkAbsTerm lo k t)
  wk lo k (pi a b)      = pi (wkArg lo k a) (wkAbsTerm lo k b)
  wk lo k (agda-sort s) = agda-sort (wkSort lo k s)
  wk lo k (lit l)       = lit l
  wk lo k (pat-lam cs args) = pat-lam (wkClauses lo k cs) (wkArgs lo k args)
  wk lo k unknown       = unknown

  wkAbsTerm lo k (abs s t)   = abs s (wk (ℕ.suc lo) k t)
  wkArgs    lo k []          = []
  wkArgs    lo k (x ∷ args)  = wkArg lo k x ∷ wkArgs lo k args
  wkArg     lo k (arg i v)   = arg i (wk lo k v)
  wkSort    lo k (set t)     = set (wk lo k t)
  wkSort    lo k (lit n)     = lit n
  wkSort    lo k (prop t)    = prop (wk lo k t)
  wkSort    lo k (propLit n) = propLit n
  wkSort    lo k (inf n)     = inf n
  wkSort    lo k unknown     = unknown

  wkClauses lo k [] = []
  wkClauses lo k (c ∷ cs) = wkClause lo k c ∷ wkClauses lo k cs

  wkClause lo k (clause tel ps b)      = clause tel ps (wk (lo + length tel) k b)
  wkClause lo k (absurd-clause tel ps) = absurd-clause tel ps

  wkPat    : Wk Pattern
  wkPatArg : Wk (Arg Pattern)
  wkPats   : Wk (List (Arg Pattern))

  wkPat    lo k (con c ps) = con c (wkPats lo k ps)
  wkPat    lo k (dot t)    = dot (wk lo k t)
  wkPat    lo k (var x)    = var (wkVar lo k x)
  wkPat    lo k (lit l)    = lit l
  wkPat    lo k (proj f)   = proj f
  wkPat    lo k (absurd x) = absurd (wkVar lo k x)
  wkPatArg lo k (arg i p)  = arg i (wkPat lo k p)
  wkPats   lo k []         = []
  wkPats   lo k (p ∷ ps)   = wkPatArg lo k p ∷ wkPats lo k ps

  weakenTerm : ℕ → Term → Term
  weakenTerm = wk 0

  wkTel : Wk Telescope
  wkTel lo k = map λ nm,arg → (proj₁ nm,arg) , (wkArg lo k (proj₂ nm,arg))

  weakenTel : ℕ → Telescope → Telescope
  weakenTel = wkTel 0

------------------------------------------------------------------------
-- Machinery for deriving things

telView : Type → Telescope × Type
telView (pi x (abs y b)) = ((y , x) ∷ (proj₁ telVb)) , proj₂ telVb
  where
    telVb : Telescope × Type
    telVb = telView b
{-# CATCHALL #-}
telView x                = [] , x

getTel : Type → Telescope
getTel = proj₁ ∘ telView

getCore : Type → Type
getCore = proj₂ ∘ telView

-- Construct a Type out of a Telescope and Core Type
telToType : Telescope → Type → Type
telToType [] core = core
telToType ((nm , x) ∷ tel) core = pi x (abs nm (telToType tel core))

-- Derive the telescope for the type of an instance, along with the deBruijin indices
-- of arguments needed for the instance type
--
-- e.g. for Write List this returns
--      {a : Level} {A : Set a} {{ Write A }} , 2 ∷ 1 ∷ []
instanceTel : Name → Name → TC (Telescope × List (Arg Term))
instanceTel cls inst = do
  t ← getType inst
  let tel = proj₁ ∘ telView $ t
  pure (computeTel cls 0 [] [] tel)
  where
    first : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → (A → B) → A × C → B × C
    first f (x , y) = f x , y

    levelToIndex : ℕ → Arg ℕ → Arg Term
    levelToIndex n (arg i x) = arg i (var (n ∸ x ∸ 1) [])

    levelsToIndices : ℕ → List (Arg ℕ) → List (Arg Term)
    levelsToIndices n xs = reverse $ map (levelToIndex n) xs

    -- if it's a sort or pi, then we need an instance in the telescope
    computeInstanceType : Name → ℕ → List (Arg ℕ) → Type → Maybe Term
    computeInstanceType class n xs (agda-sort _) =
      just (def class (vArg (var n (levelsToIndices n xs)) ∷ []))
    computeInstanceType class n xs (pi (arg info a) (abs s b)) =
      computeInstanceType class (ℕ.suc n) ((arg info n) ∷ xs) b >>=Maybe
      λ y → just (pi (hArg a) (abs s y))
    {-# CATCHALL #-}
    computeInstanceType _ _ _ _ = nothing

    -- compute the telescope in an accumulator like fashion
    -- instances are on the tail of the telescope, so are accumulated into a separate telescope and then 'wacked on'
    -- the end
    --
    -- Name is the name of the class (e.g. Write)
    -- ℕ how far down the telescope we are
    -- List (Arg ℕ) holds the accumulated *levels* of arguments, converted into indices (Arg Term) at the end
    -- Telescope 1 is the accumulated-into telescope of *instances*
    -- Telescope 2 is the starting telescope of the instance type (e.g. that of List for Write (List A))
    computeTel : Name → ℕ → List (Arg ℕ) → Telescope → Telescope → Telescope × List (Arg Term)
    computeTel class n args acc [] = reverse acc , (levelsToIndices (n + length acc) args)
    computeTel class n args acc ((nm , arg info x) ∷ tel) =
      (first ((nm , hArg x) ∷_)) $
      case computeInstanceType class 0 [] (weakenTerm 1 x)  of λ
      { (just i) → computeTel class (1 + n) ((arg info n) ∷ args) (("_" , (iArg (weakenTerm (length acc) i))) ∷ (weakenTel 1 acc)) tel
      ; nothing → computeTel class (1 + n) ((arg info n) ∷ args) (weakenTel 1 acc) tel
      }

-- Derive the type of an instance for a given record type,
-- prepending all required instances to the telescope
--
-- e.g. for Write (List), will give
--      : {{ Write A }} → Write (List A)
instanceType : Name → Name → TC Type
instanceType cls inst = do
  tel-args ← instanceTel cls inst

  let tel = proj₁ tel-args
      args = proj₂ tel-args

  pure (telToType tel (def cls [ (vArg (def inst args)) ]))

varArg : ℕ → Arg Term
varArg n = vArg (var n [])

------------------------------------------------------------------------
-- Machinery specific to Write

-- Produce the type for the auxiliary function that does the
-- actual writing (i.e. has the expanded type)
--
-- Example: writeAuxType List
--          ↦ {a : Set} {A : Set a} → {{ Write A }} → Precedence → List A → List Char → List Char
writeAuxType : Name → TC Type
writeAuxType nm = do
  tel,args ← instanceTel (quote Write) nm
  let tel = proj₁ tel,args
      args = wkArgs 0 1 $ proj₂ tel,args
  pure (telToType tel (core $ vArg (def nm args)))

  where
    listChar : Type
    listChar = def (quote List) [ (vArg (def (quote String) [])) ]

    prec : Arg Type
    prec = vArg (def (quote Precedence) [])

    core : Arg Type → Type
    core nmArg = pi prec (abs " " (pi nmArg (abs " " (pi (vArg listChar) (abs " " listChar)))))

-- Produce the type of a Write instance for a given class.
--
-- Example: writeType List ↦ {a : Set} {A : Set a} → {{ Write A }} → Write (List A)
writeType : Name → TC Type
writeType nm = instanceType (quote Write) nm

writeArgs : Name → TC (List (Arg Term))
writeArgs nm = do
  tel,args ← instanceTel (quote Write) nm
  pure $ proj₂ tel,args

-- TODO: doc comment can be better?
-- given the telescope for a constructor, produce the whole telescope for
-- its clause
conTel : Telescope → Telescope
conTel tel =  ("str" , (vArg (quoteTerm (List String)))) ∷ (tel ++ ("prec" , (vArg (quoteTerm Precedence))) ∷ [])

-- The (tail of the) Telescope for the clause of the auxiliary write function for Records.
-- i.e. Precedence → Record → List Char
recTel : Name → TC Telescope
recTel rec = do
  args ← writeArgs rec
  pure $ conTel [ ("rec" , vArg (def rec args)) ]

------------------------------------------------------------------------
-- Derive macro for Write

-- quote a List but use a specific term instead of the empty list
quoteListNoNull : List Term → Term → Term
quoteListNoNull [] y = y
quoteListNoNull (x ∷ xs) y = con (quote _∷_) (vArg x ∷ [ vArg (quoteListNoNull xs y) ])

-- Take a list of terms and turn it into a term of a list of said terms
quoteList : List Term → Term
quoteList xs = quoteListNoNull xs (con (quote List.[]) [])

-- This is where the actual function body for each constructor is defined
telWrite' : Term → List String → ℕ → Telescope → List Term
telWrite' conPrec seps len [] = []
telWrite' conPrec seps len ((nm , typ) ∷ xs) = sepTerm ∷ writeVal ∷ (telWrite' conPrec seps' len xs)
          where
            next : List String → String × (List String)
            next [] = " " , []
            next (x ∷ xs) = x , xs

            sepSeps : String × List String
            sepSeps = next seps

            sep : String
            sep = proj₁ sepSeps

            sepTerm : Term
            sepTerm = lit (string sep)

            seps' : List String
            seps' = proj₂ sepSeps

            inst : Arg Term
            inst = iArg unknown

            str : Arg Term
            str = vArg $ var (len + 1) []

            pref : Term
            pref = lit (string "(")

            suff : Term
            suff = lit (string ")")

            conVal : Arg Term
            conVal = vArg $ var ∣ len - (length xs) ∣′ []

            writeVal : Term
            writeVal = def (quote writePrec) (vArg conPrec ∷ conVal ∷ [])

-- Given a list of mixfix seperators and the telescope of a constructor, produce the
-- function body for its Write instance.
--
-- In the case the constructor is not mixfix, the seperator list should be a singleton
-- containing just the constructor name. Each seperator part is interleaved
-- between written values.
telWrite : Term → List String → Telescope → Term
telWrite prec seps tel = def (quote writeParens) (varArg 0 ∷ vArg prec ∷ vArg (quoteList (telWrite' prec seps (length tel) tel)) ∷ [])

varPat : ℕ → Arg Pattern
varPat n = vArg (Pattern.var n)

insPat : ℕ → Arg Pattern
insPat n = iArg (Pattern.var n)

telToVarPat : ℕ → List (Arg Pattern)
telToVarPat 0 = []
telToVarPat (ℕ.suc n) = telToVarPat n ++ (varPat (1 + n)) ∷ []

conNameTerm : Name → Term
conNameTerm nm = def (quote unqualify) (vArg (def (quote toList) (nmLit ∷ [])) ∷ [])
  where
    nmLit : Arg Term
    nmLit = vArg (lit (string (showName nm)))

-- Get a list of constructor seperators
-- with an additional empty seperator
-- if the constructor is mixfix and starts with a _
-- NOTE: there is *very* likely a much nicer way of writing this, but right now
--       i am too tired to figure it out
conSeps : List Char → List String
conSeps [] = []
conSeps ('_' ∷ str) with conSeps str
... | [] = [ "" ]
... | x ∷ seps = "" ∷ (" " ++s x) ∷ seps
conSeps str@(_ ∷ _) with wordsBy (_≡?_ '_') str
... | [] = []
... | sep ∷ seps = (fromList (sep ++ [ ' ' ])) ∷ (map (λ x → fromList (' ' ∷ (sep ++ [ ' ' ]))) seps)

-- clause for data-types when the constructor is empty
emptyCons : Name → Clause
emptyCons nm = Clause.clause (conTel []) ((varPat 0) ∷ conPat ∷ ((varPat 1) ∷ [])) (conNameTerm nm)
  where
    conPat : Arg Pattern
    conPat = vArg (Pattern.con nm [])

nmPrec : Name → Precedence
nmPrec nm with getFixity nm
... | fixity _ prec = prec

-- derive the clause for a single constructor of a data-type
consClause : Name → Telescope → TC Clause
consClause nm [] = pure $ emptyCons nm
consClause nm tel@(_ ∷ _) = do
  prec ← quoteTC (nmPrec nm)
  let writeTerm = telWrite prec (conSeps nmStr) tel
  pure $ Clause.clause (conTel tel) (varPat 0 ∷ conPat ∷ strPat ∷ []) writeTerm
  where
    precPat : Arg Pattern
    precPat = varPat 0

    telLen : ℕ
    telLen = Data.List.Base.length tel

    conPat : Arg Pattern
    conPat = vArg (Pattern.con nm (telToVarPat telLen))

    strPat : Arg Pattern
    strPat = varPat (telLen + 1)

    nmStr : List Char
    nmStr = unqualify (toList (showName nm))

-- Output a list of terms that each produce part of the output
-- for a record-type
-- TODO: handle bracketing? (when would the record need to be bracketed?)
recordOutputs : Name → List (Arg Name) → List Term
recordOutputs nm [] = lit (string "}") ∷ []
recordOutputs nm (x ∷ fs) = lit (string fieldName) ∷
                            lit (string " = ") ∷
                            def (quote write) (fieldArg ∷ []) ∷
                            lit (string "; ") ∷
                            recordOutputs nm fs
  where
    fieldArg : Arg Term
    fieldArg = vArg (def (unArg x) [ varArg 1 ])

    fieldName : String
    fieldName = fromList (unqualify (toList (showName (unArg x))))

-- Produce the term for the derived Write instance for record-types
recordTerm : Name → List (Arg Name) → Term
recordTerm nm fs = quoteListNoNull (prefix ∷ outs) (var 2 [])

  where
    prefix : Term
    prefix = lit (string "record { ")

    outs : List Term
    outs = recordOutputs nm fs

weakenPi : ℕ → Type → Type
weakenPi ℕ.zero t = t
weakenPi (ℕ.suc n) (pi c (abs s x)) = weakenPi n x
{-# CATCHALL #-}
weakenPi _ t = t

piCount : Type → ℕ
piCount (pi c (abs s x)) = ℕ.suc (piCount x)
{-# CATCHALL #-}
piCount _ = 0

consClauses : List (Name × Telescope) → TC (List Clause)
consClauses [] = pure $ []
consClauses ((nm , tel) ∷ nmts) = do
  tl ← consClauses nmts
  hd ← consClause nm tel
  pure $ hd ∷ tl

-- derive the body of the auxiliary function of a Write instance
computeAuxWrite : Name → Definition → TC (List Clause)
computeAuxWrite nm (record-type c fs) = do
  t ← getType c
  let params = ∣ (piCount t) - (length fs) ∣′
      t' = weakenPi params t
  tel ← recTel nm
  let pats = varPat 0 ∷ varPat 1 ∷ varPat 2 ∷ []
      body = recordTerm c fs
      clause = Clause.clause tel pats body
  pure [ clause ]
computeAuxWrite nm (data-type p cs) = do
  ts ← mapM monadTCM getType cs
  let tels = map (drop p ∘ proj₁ ∘ telView) ts
  clauses ← consClauses (zip cs tels)
  debugOut 0 (termErr (pat-lam clauses []) ∷ [])
  pure clauses
{-# CATCHALL #-}
computeAuxWrite _ _  = typeError (strErr "Write instances can only be derived for data and record types" ∷ [])

-- Declare a Write instance with a given name for a given
-- type.
--
-- e.g.
-- declareWriteInstance 'ListWrite' (quote List)
-- ↦
-- ListWrite : {a : Level} {A : Set a} {{Write A}} → Write (List A)
declareWriteInstance : Name → Name → TC ⊤
declareWriteInstance fnm class = do
  t ← writeType class

  declareDef (iArg fnm) t

-- Define the Write instance of a given name for a given
-- type.
--
-- The instance must already be declared, e.g. via declareWriteInstance.
-- This also declares another top-level name with the 'expanded' type of Write
-- (Precedence → A → List Char → List Char), and attaches the 'actual' definition to that.
-- For a type T, the name of this auxillary function is "write[T]".
--
-- The instance then simply constructs a record of Write out of it. This is to allow
-- for the definition to recurse on itself.
defineWriteInstance : Name → Name → TC ⊤
defineWriteInstance inm class = do
  fnm ← freshName ("write[" ++s showName inm ++s "]")
  ft ← writeAuxType class

  declareDef (vArg fnm) ft
  defineFun inm (Clause.clause [] [] (con (quote Text.Write.mkWrite) [ vArg (def fnm []) ]) ∷ [])

  classDef ← getDefinition class
  clauses ← computeAuxWrite class classDef
  -- typeError [ termErr $ pat-lam clauses [] ]
  defineFun fnm clauses

  pure _

-- Usage (example for List):
--  unquoteDecl ListWrite = deriveWriteI ListWrite (quote List)
deriveWrite : Name → Name → TC ⊤
deriveWrite iname typ = (declareWriteInstance iname typ) >> (defineWriteInstance iname typ)

syntax deriveWrite x y = y derives Write as x

-- some example usage
record Test' (A B : Set) : Set where
  field
    a : ℕ
    b : ℕ
    c : A

infix 20 _a_
data Test'' {A : Set} (C : ℕ): Set where
  _a_ : A → List ℕ → Test'' C

-- infix 20 Test''._a_

open import Data.List.Instances
instance
  unquoteDecl Test'Write = (quote Test') derives Write as Test'Write
  unquoteDecl Test''Write = (quote Test'') derives Write as Test''Write

test' : Test' ℕ ℕ
test' .Test'.a = 5
test' .Test'.b = 99
test' .Test'.c = 101

test'' : Test'' 5
test'' = 0 a (1 ∷ 2 ∷ 3 ∷ [])

f : String
f = write test''
