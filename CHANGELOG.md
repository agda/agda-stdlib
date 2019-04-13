Version TODO
============

The library has been tested using Agda version 2.6.0.

Changes since 1.0:

Highlights
----------

Non-backwards compatible changes
--------------------------------

* Split the `Maybe`-independent content of `Data.These` into `Data.These.Base`
  to avoid cyclic dependencies with `Data.Maybe.Base` which now has an `align`
  function. `Data.These` re-exports `Data.These.Base` so it should be mostly
  transparent for users.

New modules
-----------

* List of new modules
  ```
  Data.AVL.NonEmpty
  Data.AVL.NonEmpty.Propositional

  Data.These.Base

  Data.Trie
  Data.Trie.NonEmpty
  ```

Removed features
----------------

Deprecated features
-------------------

Other minor additions
---------------------

* Added new function to `Data.AVL.Indexed`:
  ```agda
  toList : Tree V l u h → List (K& V)
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  ap        : Maybe (A → B) → Maybe A → Maybe B
  _>>=_     : Maybe A → (A → Maybe B) → Maybe B
  ```
