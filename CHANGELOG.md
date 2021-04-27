Version 1.7
===========

The library has been tested using Agda 2.6.1 and 2.6.1.3.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Other minor additions
---------------------

* Added new relations to `Data.Fin.Base`:
  ```agda
  _≥_ = ℕ._≥_ on toℕ
  _>_ = ℕ._>_ on toℕ
  ```

* Added new proofs to `Data.Fin.Induction`:
  ```agda
  >-wellFounded   : WellFounded {A = Fin n} _>_
  
  <-weakInduction : P zero      → (∀ i → P (inject₁ i) → P (suc i)) → ∀ i → P i
  >-weakInduction : P (fromℕ n) → (∀ i → P (suc i) → P (inject₁ i)) → ∀ i → P i
  ```
