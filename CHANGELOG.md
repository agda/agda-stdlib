Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

* `Reflection.TypeChecking.MonadSyntax` ↦ `Reflection.TypeChecking.Monad.Syntax`

Deprecated names
----------------

New modules
-----------

* Symmetric transitive closures of binary relations:
  ```
  Relation.Binary.Construct.Closure.SymmetricTransitive
  ```

* Type-checking monads
  ```
  Reflection.TypeChecking.Monad
  Reflection.TypeChecking.Monad.Categorical
  Reflection.TypeChecking.Monad.Instances
  ```

Other major changes
-------------------

Other minor additions
---------------------
* Made first argument of [,]-∘-distr in `Data.Sum.Properties` explicit
* Added map-id, map₁₂-commute, [,]-cong, [-,]-cong, [,-]-cong, map-cong, map₁-cong and map₂-cong to `Data.Sum.Properties`
