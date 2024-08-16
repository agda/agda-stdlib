Version 2.2-dev
===============

The library has been tested using Agda 2.6.4.3.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Additions to existing modules
-----------------------------

* In `Algebra.Definitions.RawMonoid` action of a Boolean on a RawMonoid:
  ```agda
  _∧_    : Bool → Carrier → Carrier
  _∧′_∙_ : Bool → Carrier → Carrier → Carrier
  ```

* Properties of the Boolean action on a RawMonoid:
  ```agda
  ∧-homo-true : true ∧ x ≈ x
  ∧-assocˡ    : b ∧ (b′ ∧ x) ≈ (b Bool.∧ b′) ∧ x
  b∧x∙y≈b∧x+y : b ∧′ x ∙ y ≈ (b ∧ x) + y
  ```
