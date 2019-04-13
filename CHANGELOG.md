Version TODO
============

The library has been tested using Agda version 2.6.0.

Changes since 1.0:

Highlights
----------

New modules
-----------

Non-backwards compatible changes
--------------------------------

Removed features
----------------

Deprecated features
-------------------

Other minor additions
---------------------

* Added new operations to `Data.List.Relation.Unary.All`:
  ```agda
  fromList : (xs : List (∃ P)) → All P (List.map proj₁ xs)
  toList   : All P xs → List (∃ P)
  self     : All (const A) xs
  ```
