Version 1.3-dev
===============

The library has been tested using Agda version 2.6.0.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Other major additions
---------------------

Other minor additions
---------------------

* Added new proofs to `Data.Bool`:
  ```agda
  not-injective : not x ≡ not y → x ≡ y
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  x∈s⇒x∉∁s : x ∈ s → x ∉ ∁ s
  x∈∁s⇒x∉s : x ∈ ∁ s → x ∉ s
  x∉∁s⇒x∈s : x ∉ ∁ s → x ∈ s
  x∉s⇒x∈∁s : x ∉ s → x ∈ ∁ s
  ```
