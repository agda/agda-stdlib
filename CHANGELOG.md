Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

* Fix a type error in `README.Data.Fin.Relation.Unary.Top` within the definition of `>-weakInduction`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* Refactored usages of `+-∸-assoc 1` to `∸-suc` in:
  ```agda
  README.Data.Fin.Relation.Unary.Top
  Algebra.Properties.Semiring.Binomial
  Data.Fin.Subset.Properties
  Data.Nat.Binary.Subtraction
  Data.Nat.Combinatorics
  ```

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeSemigroup`:
  ```agda
  interchange  ↦   medial
  ```

New modules
-----------

* `Data.List.Relation.Binary.Permutation.Algorithmic{.Properties}` for the Choudhury and Fiore definition of permutation, and its equivalence with `Declarative` below.

* `Data.List.Relation.Binary.Permutation.Declarative{.Properties}` for the least congruence on `List` making `_++_` commutative, and its equivalence with the `Setoid` definition.

* `Data.List.Relation.Binary.Prefix.Propositional.Properties` showing the equivalence to left divisibility induced by the list monoid.

* `Data.List.Relation.Binary.Suffix.Propositional.Properties` showing the equivalence to right divisibility induced by the list monoid.

* `Data.List.Sort.InsertionSort.{agda|Base|Properties}` defines insertion sort and proves properties of insertion sort such as Sorted and Permutation properties.

* `Data.List.Sort.MergenSort.{agda|Base|Properties}` is a refactor of the previous `Data.List.Sort.MergenSort`.

* `Data.Sign.Show` to show a sign.

* `Effect.Monad.Random` and `Effect.Monad.Random.Instances` for an mtl-style randomness monad constraint

* `Relation.Binary.Morphism.Construct.Product` to plumb in the (categorical) product structure on `RawSetoid`.

* `Relation.Binary.Properties.PartialSetoid` to systematise properties of a PER

* `Relation.Nullary.Recomputable.Core`


Additions to existing modules
-----------------------------

* In `Algebra.Properties.RingWithoutOne`:
  ```agda
  [-x][-y]≈xy : ∀ x y → - x * - y ≈ x * y
  ```

* In `Data.Nat.Properties`:
  ```agda
  ∸-suc : m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
  ```

* In `System.Random`:
  ```agda
  randomIO : IO Bool
  randomRIO : RandomRIO {A = Bool} _≤_
  ```
