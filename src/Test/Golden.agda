------------------------------------------------------------------------
-- The Agda standard library
--
-- Golden testing framework
------------------------------------------------------------------------

-- This is a port of the golden testing framework used by the Idris2
-- compiler and various Idris2 libraries.
-- It provides the core features required to perform golden file testing.
--
-- We provide the core functionality to run a *single* golden file test,
-- or a whole test tree. This allows the developer freedom to use as is
-- or design the rest of the test harness to their liking.

------------------------------------------------------------------------
-- Test Structure
--
-- This harness works from the assumption that each individual golden
-- test comprises of a directory with the following structure:
--
-- + `run` a *shell* script that runs the test. We expect it to:
--   * Use `$1` as the variable standing for the Agda executable to be tested
--   * Clean up after itself (e.g. by running `rm -rf build/`)
--
-- + `expected` a file containting the expected output of `run`
--
-- During testing, the test harness will generate an `output` file.
-- It will be compared to the `expected` golden file provided by the user.
-- In case there is a mismatch, the framework will:

-- + either display output & expected if the session is not interactive
-- + or use the following command line to produce a diff and ask the user
--   whether they want to overwrite the currently `expected` value:
--
--  git diff --no-index --exit-code --word-diff=color expected output
--
-- If `git` fails then the runner will simply present the expected and
-- 'given' files side-by-side.
--
-- Of note, it is helpful to add `output` to a local `.gitignore` instance
-- to ensure that it is not mistakenly versioned.


------------------------------------------------------------------------
-- Options
--
-- The test harness has several options that may be set:
--
-- + `Agda`         The path of the executable we are testing.
-- + `onlyNames`    The tests to run relative to the generated executable.
-- + `onlyFile`     The file listing the tests to run relative to the generated executable.
-- + `interactive`  Whether to offer to update the expected file or not.
-- + `timing`       Whether to display time taken for each test.
-- + `failureFile`  The file in which to write the list of failing tests.
--
-- We provide an options parser (`options`) that takes the list of command line
-- arguments and constructs this for you.
---

------------------------------------------------------------------------
-- Usage
--
-- When compiled to an executable the expected usage is:
--
--```sh
--runtests <path to executable under test>
--   [--timing]
--   [--interactive]
--   [--only-file PATH]
--   [--failure-file PATH]
--   [--only [NAMES]]
--```
--
-- assuming that the test runner is compiled to an executable named `runtests`.

{-# OPTIONS --without-K --guardedness #-}

module Test.Golden where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
import Data.Char as Char
open import Data.Fin using (#_)
open import Data.List.Base as List using (List; []; _∷_; _++_; filter; partitionSums)
open import Data.List.Relation.Binary.Infix.Heterogeneous.Properties using (infix?)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _≡ᵇ_; _<ᵇ_; _+_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; lines; unlines; unwords; concat)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤)

open import Function.Base using (id; _$_; case_of_)

open import Relation.Nullary using (does)

open import Codata.Musical.Notation using (♯_)
open import IO

open import System.Clock as Clock using (time′; Time)
open import System.Environment using (getArgs)
open import System.Exit using (exitSuccess; exitFailure; die; isFailure)
open import System.Process using (callCommand; system)

record Options : Set where
  field
    -- What is the name of the Agda executable?
    exeUnderTest : String -- TODO: filepath library
    -- Should we only run some specific cases?
    onlyNames    : List String
    -- Should we run the test suite interactively?
    interactive : Bool
    -- Should we time and display the tests?
    timing : Bool
    -- Should we write the list of failing cases to a file?
    failureFile : Maybe String
open Options

initOptions : String → Options
initOptions exe = record
  { exeUnderTest = exe
  ; onlyNames    = []
  ; interactive  = false
  ; timing       = false
  ; failureFile  = nothing
  }

usage : String
usage = unwords
  $ "Usage:"
  ∷ "runtests <path>"
  ∷ "[--timing]"
  ∷ "[--interactive]"
  ∷ "[--failure-file PATH]"
  ∷ "[--only-file PATH]"
  ∷ "[--only [NAMES]]"
  ∷ []

-- Process the command line options
options : List String → IO (Maybe Options)
options(exe ∷ rest) = mkOptions exe rest where

  go : List String → Maybe String → Options → Maybe (Maybe String × Options)
  go []                             mfp opts = just (mfp , opts)
  go ("--timing"            ∷ args) mfp opts =
    go args mfp (record opts { timing = true })
  go ("--interactive"       ∷ args) mfp opts =
    go args mfp (record opts { interactive = true })
  go ("--failure-file" ∷ fp ∷ args) mfp opts =
    go args mfp (record opts { failureFile = just fp })
  go ("--only"              ∷ args) mfp opts =
    go args mfp (record opts { onlyNames = args })
  go _ _ _ = nothing

  mkOptions : String → List String → IO (Maybe Options)
  mkOptions exe rest = do
    just (mfp , opts) ← pure $ go rest nothing (initOptions exe)
      where _ → pure nothing
    just fp ← pure mfp
      where _ → pure (just opts)
    only ← readFiniteFile fp
    pure $ just $ record opts { onlyNames = lines only ++ onlyNames opts }

options _ = pure nothing


-- The result of a test run
-- `Left` corresponds to a failure and `Right` to a success
Result : Set
Result = String ⊎ String

-- Run the specified golden test with the supplied options.
-- TODO: filepath library
runTest : Options → String → IO Result
runTest opts testPath = do
  time ← time′ $ callCommand $ unwords
           $ "cd" ∷ testPath
           ∷ "&&" ∷ "sh ./run" ∷ opts .exeUnderTest ∷ "| tr -d '\\r' > output"
           ∷ []

  -- TODO: check the files exist before reading them!
  out ← readFiniteFile (testPath String.++ "/output")
  exp ← readFiniteFile (testPath String.++ "/expected")

  let result = does (out String.≟ exp)

  if result
    then printTiming (opts .timing) time ": success"
    else do printTiming (opts .timing) time ": FAILURE"
            if opts .interactive
              then mayOverwrite (just exp) out
              else putStrLn (unlines (expVsOut exp out))

  pure $ if result then inj₂ testPath else inj₁ testPath

  where

    getAnswer : IO Bool
    getAnswer = untilJust $ do
      str ← getLine
      case str of λ where
        "y" → pure $ just true
        "n" → pure $ just false
        ""  → pure $ just false -- default answer is no
        _   → do putStrLn "Invalid answer."
                 pure nothing

    expVsOut : String → String → List String
    expVsOut exp out = "Expected:" ∷ exp ∷ "Given:" ∷ out ∷ []

    mayOverwrite : Maybe String → String → IO _
    mayOverwrite mexp out = do
      case mexp of λ where
        nothing → putStr $ unlines
          $ "Golden value missing. I computed the following result:"
          ∷ out
          ∷ "Accept new golden value? [y/N]"
          ∷ []
        (just exp) → do
          code ← system $ concat
            $ "git diff --no-index --exit-code --word-diff=color "
            ∷ testPath ∷ "/expected "
            ∷ testPath ∷ "/output"
            ∷ []
          putStrLn $ unlines
            $ "Golden value differs from actual value."
            ∷ (if isFailure code then expVsOut exp out else [])
            ++ "Accept actual value as new golden value? [y/N]"
            ∷ []

      b ← getAnswer
      when b $ writeFile (testPath String.++ "/expected") out

    printTiming : Bool → Time → String → IO _
    printTiming true  time msg = putStrLn (unwords (msg ∷ Clock.show time (# 3) ∷ []))
    printTiming false _    msg = putStrLn msg


-- A test pool is characterised by
--  + a name
--  + and a list of directory paths
record TestPool : Set where
  constructor mkTestPool
  field
    poolName : String
    testCases : List String
open TestPool

module Summary where

  -- The summary of a test pool run
  record Summary : Set where
    constructor mkSummary
    field
      success : List String
      failure : List String
  open Summary public

  init : Summary
  init = mkSummary [] []

  merge : Summary → Summary → Summary
  merge (mkSummary ws1 ls1) (mkSummary ws2 ls2) =
   mkSummary (ws2 ++ ws1) (ls2 ++ ls1)

  update : List Result -> Summary -> Summary
  update res sum =
    let (ls2 , ws2) = partitionSums res in
    merge sum (mkSummary ws2 ls2)

open Summary using (Summary) hiding (module Summary)

-- Only keep the tests that have been asked for
filterTests : Options -> List String -> List String
filterTests opts = case onlyNames opts of λ where
  [] → id
  xs → let names = List.map String.toList xs in
       filter (λ n → any? (λ m → infix? Char._≟_ m (String.toList n)) names)

poolRunner : Options → TestPool → IO Summary
poolRunner opts pool = do
  -- check there is a non-empty list of tests we want to run
  let tests = filterTests opts (pool .testCases)
  (_ ∷ _) ← pure tests
    where [] → pure Summary.init

  -- announce the test pool and run them
  putStrLn banner
  loop Summary.init tests

  where

  separator : String
  separator = String.replicate 72 '-'

  banner : String
  banner = unlines
         $ "" ∷ separator
         ∷ pool .poolName
         ∷ separator ∷ ""
         ∷ []

  loop : Summary → List String → IO Summary
  loop acc [] = pure acc
  loop acc (test ∷ tests) = do
    res <- runTest opts test
    loop (Summary.update (res ∷ []) acc) tests

runner : List TestPool → IO ⊤
runner tests = do
  -- figure out the options
  args ← getArgs
  just opts ← options args
    where nothing → die usage

  -- run the tests
  ress ← List.mapM (poolRunner opts) tests
  let open Summary
  let res = List.foldl merge init ress

  -- report the result
  let nsucc = List.length (res .success)
  let nfail = List.length (res .failure)
  let ntotal = nsucc + nfail
  putStrLn $ concat $ show nsucc ∷ "/" ∷ show ntotal ∷ " test successful" ∷ []

  -- deal with failures
  let list = unlines (res .failure)
  when (0 <ᵇ nfail) $ do
    putStrLn "Failing tests:"
    putStrLn list
  whenJust (opts .failureFile) $ λ fp → writeFile fp list

  -- exit
  if 0 ≡ᵇ nfail
   then exitSuccess
   else exitFailure
