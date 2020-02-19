------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about how data types are laid out in the standard
-- library.
------------------------------------------------------------------------

module README.Data where

-- The top-level folder `Data` contains all the definitions of datatypes
-- and their associated properties.

-- Datatypes can broadly split into two categories
--   i) "Basic" datatypes which do not take other datatypes as generic
--      arguments (Nat, String, Fin, Bool, Char etc.)
--   ii) "Container" datatypes which take other generic datatypes as
--   arguments, (List, Vec, Sum, Product, Maybe, AVL trees etc.)

------------------------------------------------------------------------
-- Basic datatypes
------------------------------------------------------------------------

-- Basic datatypes are usually organised as follows:

-- 1. A `Base` module which either contains the definition of the
-- datatype or reimports it from the builtin modules, along with common
-- functions, operations and relations over elements of the datatype.

import Data.Nat.Base
import Data.Integer.Base
import Data.Char.Base
import Data.String.Base
import Data.Bool.Base

-- Commonly these modules don't need to be imported directly as their
-- contents is re-exported by the top level module (see below).

-- 2. A `Properties` module which contains the basic properties of the
-- functions, operations and relations contained in the base module.

import Data.Nat.Properties
import Data.Integer.Properties
import Data.Char.Properties
import Data.String.Properties
import Data.Bool.Properties

-- 3. A top-level module which re-exports the contents of the base
-- module as well as various queries (i.e. decidability proofs) from the
-- properties file.

import Data.Nat
import Data.Integer
import Data.Char
import Data.String
import Data.Bool

-- 4. A `Solver` module (for those datatypes that have an algebraic solver)
-- which can be used to automatically solve equalities over the basic datatype.

import Data.Nat.Solver
import Data.Integer.Solver
import Data.Bool.Solver

-- 5. More complex operations and relations are commonly found in their
-- own module beneath the top-level directory. For example:

import Data.Nat.DivMod
import Data.Integer.Coprimality

-- Note that eventually there is a plan to re-organise the library to
-- have the top-level module export a far wider range of properties and
-- additional operations in order to minimise the number of imports
-- needed. Currently it is necessary to import each of these separately
-- however.

------------------------------------------------------------------------
-- Container datatypes
------------------------------------------------------------------------

-- 1. As with basic datatypes, a `Base` module which contains the
-- definition of the datatype, along with common functions and
-- operations over that data. Unlike basic datatypes, the `Base` module
-- for container datatypes does not export any relations or predicates
-- over the datatype (see the `Relation` section below).

import Data.List.Base
import Data.Maybe.Base
import Data.Sum.Base

-- Commonly these modules don't need to be imported directly as their
-- contents is re-exported by the top level module (see below).

-- 2. As with basic datatypes, a `Properties` module which contains the
-- basic properties of the functions, operations and contained in the
-- base module.

import Data.List.Properties
import Data.Maybe.Properties
import Data.Sum.Properties

-- 3. As with basic datatypes, a top-level module which re-exports the
-- contents of the base module. In some cases this may also contain
-- additional functions which could not be placed into the corresponding
-- Base module because of cyclic dependencies.

import Data.List
import Data.Maybe
import Data.Sum

-- 4. A `Relation.Binary` folder where binary relations over the datatypes
-- are stored. Because relations over container datatypes often depend on
-- relations over the parameter datatype, this differs from basic datatypes
-- where the binary relations are usually defined in the `Base` module, e.g.
-- equality over the type `List A` depends on equality over type `A`.

-- For example the `Pointwise` relation that takes a relation over the
-- underlying type A and lifts it to the container parameterised can be found
-- as follows:

import Data.List.Relation.Binary.Pointwise
import Data.Maybe.Relation.Binary.Pointwise
import Data.Sum.Relation.Binary.Pointwise

-- Another useful subfolder in the `Data.X.Relation.Binary` folders is the
-- `Data.X.Relation.Binary.Equality` folder which contains various forms of
-- equality over the datatype.

-- 5. A `Relation.Unary` folder where unary relations, or predicates,
-- over the datatypes are stored. These can be viewed as properties
-- over a single list.

-- For example a common, useful example is `Data.X.Relation.Unary.Any`
-- that contains the types of proofs that at least one element in the
-- container satisfies some predicate/property.

import Data.List.Relation.Unary.Any
import Data.Vec.Relation.Unary.Any
import Data.Maybe.Relation.Unary.Any

-- Alternatively the `Data.X.Relation.Unary.All` module contains the
-- type of proofs that all elements in the container satisfy some
-- property.

import Data.List.Relation.Unary.All
import Data.Vec.Relation.Unary.All
import Data.Maybe.Relation.Unary.All

-- 6. A `Categorical` module/folder that contains categorical
-- interpretations of the datatype.

import Data.List.Categorical
import Data.Maybe.Categorical
import Data.Sum.Categorical.Left
import Data.Sum.Categorical.Right

-- 7. A `Function` folder that contains lifting of various types of
-- functions (e.g. injections, surjections, bijections, inverses) to
-- the datatype.

import Data.Sum.Function.Propositional
import Data.Sum.Function.Setoid
import Data.Product.Function.Dependent.Propositional
import Data.Product.Function.Dependent.Setoid

------------------------------------------------------------------------
-- Full list of documentation for the Data folder
------------------------------------------------------------------------

-- Some examples showing where the natural numbers/integers and some
-- related operations and properties are defined, and how they can be
-- used:

import README.Data.Nat
import README.Data.Nat.Induction

import README.Data.Integer

-- Some examples showing how the AVL tree module can be used.

import README.Data.AVL

-- Some examples showing how List module can be used.

import README.Data.List

-- Some examples showing how the Fresh list can be used.

import README.Data.List.Fresh

-- Using List's Interleaving to define a fully certified filter function.

import README.Data.Interleaving

-- Example of an encoding of record types with manifest fields and "with".

import README.Data.Record

-- Example use case for a trie: a wee generic lexer

import README.Data.Trie.NonDependent

-- Examples how (indexed) containers and constructions over them (free
-- monad, least fixed point, etc.) can be used

import README.Data.Container.FreeMonad
import README.Data.Container.Indexed
