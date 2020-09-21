Version 1.5-dev
===============

The library has been tested using Agda 2.6.2

Highlights
----------

* New module for making system calls during type checking, `Reflection.External`,
  which re-exports `Agda.Builtin.Reflection.External`.

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

#### Reflection

* The representation of reflected syntax in `Reflection.Term` and
  `Reflection.Pattern` has been updated to match the new
  representation used in Agda 2.6.2. Specifically, the following changes were made:

  * The type of the `var` constructor of the `Pattern` datatype has
    been changed from `(x : String) → Pattern` to `(x : Int) →
    Pattern`.
  * The type of the `dot` constructor of the `Pattern` datatype has
    been changed from `Pattern` to `(t : Term) → Pattern`
  * The types of the `clause` and `absurd-clause` constructors of the
    `Clause` datatype now take an extra argument `(tel : Telescope)`,
    where `Telescope = List (String × Arg Type)`.

  See the release notes of Agda 2.6.2 for more information.

#### Other

* `Data.Maybe.Base` now re-exports the definition of `Maybe` given by
  `Agda.Builtin.Maybe`. The `Foreign.Haskell` modules and definitions
  corresponding to `Maybe` have been removed.

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
  which re-exports and augments the contents of `Agda.Builtin.Reflection.External`.

Other major changes
-------------------

Other minor additions
---------------------
