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

New modules
-----------

Additions to existing modules
-----------------------------

* In `Data.Nat.Properties`:
  ```agda
  ∸-suc : m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
  ```

* In `Data.Vec.Properties`:
  ```agda
  updateAt-take : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                  updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)

  truncate-zipWith : (m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) (f : A → B → C) →
                    truncate m≤n (zipWith f xs ys) ≡ zipWith f (truncate m≤n xs) (truncate m≤n ys)

  truncate-zipWith-truncate : (f : A → B → C) (m≤n : m ≤ n) (n≤o : n ≤ o) (xs : Vec A o) (ys : Vec B n) →
                              truncate m≤n (zipWith f (truncate n≤o xs) ys) ≡
                              zipWith f (truncate (≤-trans m≤n n≤o) xs) (truncate m≤n ys)

  truncate-updateAt : (m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) (f : A → A) →
                      updateAt (truncate m≤n xs) i f ≡
                      truncate m≤n (updateAt xs (inject≤ i m≤n) f)

  updateAt-truncate : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                      updateAt (truncate (m≤m+n m n) xs) i f ≡
                      truncate (m≤m+n m n) (updateAt xs (inject≤ i (m≤m+n m n)) f)

  map-truncate : (f : A → B) (m≤n : m ≤ n) (xs : Vec A n) →
                map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)

  ```