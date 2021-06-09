------------------------------------------------------------------------
-- The Agda standard library
--
-- Directory tree as a functional structure
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness --sized-types #-}

module System.Directory.Tree where

open import IO
open import Size
open import Codata.Thunk using (Thunk; force)

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base as List using (List; partitionSums)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_$_)
open import System.Directory
open import System.FilePath.Posix

private
  variable
    m n : Nature
    i : Size

{-# NO_UNIVERSE_CHECK #-}
data Tree n i : Set where
  _∋_:<_ :
    FilePath n →                                  -- path to the root of the tree
    List (FilePath n) →                           -- list of files in it
    List (FilePath n × (IO (Thunk (Tree n) i))) → -- trees for subdirectories
    Tree n i

AbsoluteTree : Set
AbsoluteTree = Tree Nature.absolute _

RelativeTree : Set
RelativeTree = Tree Nature.relative _

treeᵗ : KnownNature n →                -- nature of the paths stored in the tree
        (AbsolutePath × FilePath n) →  -- path to the root (absolute for setting, n for storing)
        IO (Thunk (Tree n) i)
treeᵗ kn (afp , fp) = withCurrentDirectory afp $ do
  -- get content of the current directory
  vs ← listDirectory afp
  -- tag each filepath with whether it points to a directory
  bvs ← List.forM vs $ λ fp → do
    fp   ← toKnownNature kn fp
    true ← doesDirectoryExist fp where false → pure (inj₂ fp)
    -- thanks to withCurrentDirectory, this will return the right answer
    afp  ← makeAbsolute fp
    pure (inj₁ (fp , (afp , fp)))
  -- partition into a list ds of directories and one fs of files
  let (ds , fs) = partitionSums bvs
  -- return the files together with the ability to further explore the tree
  pure (λ where .force → fp ∋ fs :< List.map (Prod.map₂ (treeᵗ kn)) ds)

tree : {{KnownNature n}} → FilePath m → IO (Tree n _)
tree {{kn}} fp = do
  afp ← makeAbsolute fp
  fp  ← toKnownNature kn fp
  tree# <$> treeᵗ kn (afp , fp)

  where

    tree# : Thunk (Tree n) ∞ → Tree n _
    tree# t = t .force
