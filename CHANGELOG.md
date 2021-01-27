Version 1.6-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

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

* Added new function in `Data.List.Base`:
  ```agda
  last : List A → Maybe A
  ```

* Added new proofs in `Data.List.Relation.Unary.All.Properties`:
  ```agda
  head⁺ : All P xs → All P (head xs)
  tail⁺ : All P xs → All (All P) (tail xs)
  last⁺ : All P xs → All P (last xs)

  uncons⁺ : All P xs → All (P ⟨×⟩ All P) (uncons xs)
  uncons⁻ : All (P ⟨×⟩ All P) (uncons xs) → All P xs
  unsnoc⁺ : All P xs → All (All P ⟨×⟩ P) (unsnoc xs)
  unsnoc⁻ : All (All P ⟨×⟩ P) (unsnoc xs) → All P xs

  dropWhile⁺ : (Q? : Decidable Q) → All P xs → All P (dropWhile Q? xs)
  takeWhile⁺ : (Q? : Decidable Q) → All P xs → All P (takeWhile Q? xs)

  all-head-dropWhile : (P? : Decidable P) → ∀ xs → All (∁ P) (head (dropWhile P? xs))
  all-takeWhile      : (P? : Decidable P) → ∀ xs → All P (takeWhile P? xs)
  ```
