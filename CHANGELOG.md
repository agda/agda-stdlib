Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

* First instance modules

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

* The module `Induction.WellFounded.InverseImage` has been deprecated. The proofs
  `accessible` and `wellFounded` have been moved to `Relation.Binary.Construct.On`.

* `Reflection.TypeChecking.MonadSyntax` ↦ `Reflection.TypeChecking.Monad.Syntax`

Deprecated names
----------------

Other major additions
---------------------

* Instance modules:
  ```agda
  Category.Monad.Partiality.Instances
  Codata.Stream.Instances
  Codata.Covec.Instances
  Data.List.Instances
  Data.List.NonEmpty.Instances
  Data.Maybe.Instances
  Data.Vec.Instances
  Function.Identity.Instances
  ```

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
