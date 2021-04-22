Version 1.7
===========

The library has been tested using Agda 2.6.1 and 2.6.1.3.

Highlights
----------

Bug-fixes
---------

* Added missing module `Function.Metric` which re-exports 
  `Function.Metric.(Core/Definitions/Structures/Bundles)`. This module was referred
  to in the documentation of its children but until now was not present.

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* Metrics specialised to co-domains with rational numbers:
  ```
  Function.Metric.Rational
  Function.Metric.Rational.Definitions
  Function.Metric.Rational.Structures
  Function.Metric.Rational.Bundles
  ```

Other minor additions
---------------------
