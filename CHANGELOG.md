Version 1.7
===========

The library has been tested using Agda 2.6.2

Highlights
----------

* New module for making system calls during type checking, `Reflection.External`,
  which re-exports `Agda.Builtin.Reflection.External`.

Bug-fixes
---------

* Added missing module `Function.Metric` which re-exports 
  `Function.Metric.(Core/Definitions/Structures/Bundles)`. This module was referred
  to in the documentation of its children but until now was not present.

Non-backwards compatible changes
--------------------------------

#### Changes to floating-point arithmetic

* The functions in `Data.Float.Base` were updated following changes upstream,
  in `Agda.Builtin.Float`, see <https://github.com/agda/agda/pull/4885>.

* The bitwise binary relations on floating-point numbers (`_<_`, `_≈ᵇ_`, `_==_`)
  have been removed without replacement, as they were deeply unintuitive, e.g., `∀ x → x < -x`.

#### Reflection

* The representation of reflected syntax in `Reflection.Term`,
  `Reflection.Pattern`, `Reflection.Argument` and
  `Reflection.Argument.Information` has been updated to match the new
  representation used in Agda 2.6.2. Specifically, the following
  changes were made:

  * The type of the `var` constructor of the `Pattern` datatype has
    been changed from `(x : String) → Pattern` to `(x : Int) →
    Pattern`.
	
  * The type of the `dot` constructor of the `Pattern` datatype has
    been changed from `Pattern` to `(t : Term) → Pattern`.
	
  * The types of the `clause` and `absurd-clause` constructors of the
    `Clause` datatype now take an extra argument `(tel : Telescope)`,
    where `Telescope = List (String × Arg Type)`.
	
  * The following constructors have been added to the `Sort` datatype:
    `prop : (t : Term) → Sort`, `propLit : (n : Nat) → Sort`, and
    `inf : (n : Nat) → Sort`.

  * In `Reflection.Argument.Information` the function `relevance` was
    replaced by `modality`.

  * The type of the `arg-info` constructor is now
    `(v : Visibility) (m : Modality) → ArgInfo`.

  * In `Reflection.Argument` (as well as `Reflection`) there is a new
    pattern synonym `defaultModality`, and the pattern synonyms
    `vArg`, `hArg` and `iArg` have been changed.

  * Two new modules have been added, `Reflection.Argument.Modality`
    and `Reflection.Argument.Quantity`. The constructors of the types
    `Modality` and `Quantity` are reexported from `Reflection`.

#### Sized types

* Sized types are no longer considered safe in Agda 2.6.2. As a
  result, all modules that use `--sized-types` no longer have the
  `--safe` flag.  For a full list of affected modules, refer to
  https://github.com/agda/agda-stdlib/pull/1465/files#diff-e1c0e3196e4cea6ff808f5d2906031a7657130e10181516206647b83c7014584R91-R131.

#### Other

* `Data.Maybe.Base` now re-exports the definition of `Maybe` given by
  `Agda.Builtin.Maybe`. The `Foreign.Haskell` modules and definitions
  corresponding to `Maybe` have been removed. See the release notes of 
  Agda 2.6.2 for more information.

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* New module for making system calls during type checking:
  ```agda
  Reflection.External
  ```

* Added `Reflection.Universe` defining a universe for the reflected syntax types.
* Added `Reflection.Annotated` defining annotated reflected syntax and
  functions to compute annotations and traverse terms based on annotations.
* Added `Reflection.Annotated.Free` implementing free variable annotations for
  reflected terms.

* Added `Relation.Unary.Sized` for unary relations over sized types now that `Size`
  lives in it's own universe since Agda 2.6.2.

* Metrics specialised to co-domains with rational numbers:
  ```
  Function.Metric.Rational
  Function.Metric.Rational.Definitions
  Function.Metric.Rational.Structures
  Function.Metric.Rational.Bundles
  ```

Other minor additions
---------------------

* Added new type in `Size`:
  ```agda
  SizedSet ℓ = Size → Set ℓ
  ```
