Version TODO
============

The library has been tested using Agda version 2.6.0.

Changes since 1.0:

Highlights
----------

New modules
-----------

The following new modules have been added to the library:
```
Data.List.Relation.Binary.Disjoint.Propositional
Data.List.Relation.Binary.Disjoint.Setoid
Data.List.Relation.Binary.Disjoint.Setoid.Properties

Data.List.Relation.Unary.AllPairs
Data.List.Relation.Unary.AllPairs.Properties
Data.List.Relation.Unary.Unique.Propositional
Data.List.Relation.Unary.Unique.Propositional.Properties
Data.List.Relation.Unary.Unique.Setoid
Data.List.Relation.Unary.Unique.Setoid.Properties
```

Non-backwards compatible changes
--------------------------------

#### Other

* Renamed a few `-identity` lemmas in `Codata.Stream.Properties` as they were
  proving two streams bisimilar rather than propositionally equal.
  ```agda
  repeat-ap-identity ↦ ap-repeatˡ
  ap-repeat-identity ↦ ap-repeatʳ
  ```

* Renamed a few lemmas in `Codata.Stream.Properties` to match the more stdlib
  conventions:
  ```agda
  ap-repeat-commute  ↦ ap-repeat
  map-repeat-commute ↦ map-repeat
  ```


Removed features
----------------

Deprecated features
-------------------

Other minor additions
---------------------

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-swap        : All (λ xs → All (xs ~_) ys) xss → All (λ y → All (_~ y) xss) ys

  applyDownFrom⁺₁ : (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₂ : (∀ i → P (f i)) → All P (applyDownFrom f n)
  ```
