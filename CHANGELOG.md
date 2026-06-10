Version 3.0
===========

The library has been tested using Agda 2.8.0.

Highlights
----------

* The notation for `Decidable` relations has been (partially) standardised: thus
  - `_≡?_` (at `infix 4`) for `DecidableEquality`
  - `_≈?_` (ditto.) for the general `IsDecEquivalence`

  At present, the old fieldname `_≟_` has been retained, in order to avoid
  a non-backwards compatible/breaking change of fieldname, which will plan
  to do in Version 3.0, with accompanying deprecation of that name, against
  its eventual removal in subsequent versions.

  The change leads to a number of (trivial) renamings/deprecations, others more
  substantive in `Data.{Nat|Fin}.Properties` for the concrete datatypes, which
  are summarised below, but are not each documented for all affected modules.

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

* [Issue #2548](https://github.com/agda/agda-stdlib/issues/2458) Consistent with other names (such as `∙-cong`, `ε-homo` etc.) in `Algebra.*`, the field name of the basic homomorphism property in `Algebra.Morphism.Structures.IsMagmaHomomorphism` has been renamed from `homo` to `∙-homo`.

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Morphism.Structures`:
  ```agda
  homo  ↦  ∙-homo
  ```


New modules
-----------

Additions to existing modules
-----------------------------
