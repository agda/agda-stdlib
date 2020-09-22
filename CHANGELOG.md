Version 1.5-dev
===============

The library has been tested using Agda 2.6.2

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

#### Changes to floating-point arithmetic

* The functions in `Data.Float.Base` were updated following changes upstream,
  in `Agda.Builtin.Float`, see <https://github.com/agda/agda/pull/4885>.

* The bitwise binary relations on floating-point numbers (`_<_`, `_≈ᵇ_`, `_==_`)
  have been removed without replacement, as they were deeply unintuitive, e.g., `∀ x → x < -x`.

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

* Added `Reflection.Traversal` for generic de Bruijn-aware traversals of reflected terms.
* Added `Reflection.DeBruijn` with weakening, strengthening and free variable operations
  on reflected terms.

Other major changes
-------------------

Other minor additions
---------------------
