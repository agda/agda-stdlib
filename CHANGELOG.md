Version 1.2-dev
===============

The library has been tested using Agda version 2.6.0.1.

Changes since 1.1:

Highlights
----------



Bug-fixes
---------



Other non-backwards compatible changes
--------------------------------------



New modules
-----------
The following new modules have been added to the library:

* The following new modules have been added to the library:
  ```
  Data.Float.Base
  Data.Float.Properties

  Data.Word.Base
  Data.Word.Properties

  Reflection.Abstraction
  Reflection.Argument
  Reflection.Argument.Information
  Reflection.Argument.Relevance
  Reflection.Argument.Visibility
  Reflection.Definition
  Reflection.Literal
  Reflection.Meta
  Reflection.Name
  Reflection.Pattern
  Reflection.Term
  ```

Relocated modules
-----------------
The following modules have been moved as part of a drive to improve
usability and consistency across the library. The old modules still exist and
therefore all existing code should still work, however they have been deprecated
and, although not anticipated any time soon, they may eventually
be removed in some future release of the library. After the next release of Agda
automated warnings will be attached to these modules to discourage their use.

* The modules `Data.Word.Unsafe` and `Data.Float.Unsafe` have been removed
  as there are no longer any unsafe operations.

Deprecated names
----------------
The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.

Other minor additions
---------------------

* Decidable equality over floating point numbers has been made safe and
  so  `_≟_` has been moved from `Data.Float.Unsafe` to `Data.Float.Properties`.

* Added new definitions to `Data.Word.Base`:
  ```agda
  _≈_ : Rel Word64 zero
  _<_ : Rel Word64 zero
  ```

* Decidable equality over words has been made safe and so `_≟_` has been
  moved from `Data.Word.Unsafe` to `Data.Word.Properties`.

* Added new definitions in `Relation.Binary.Core`:
  ```agda
  DecidableEquality A = Decidable {A = A} _≡_
  ```
