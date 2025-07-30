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
  take-updateAt : (f : A → A) {m n : ℕ} (xs : Vec A (m + n)) (i : Fin m) →
    updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)
  
  truncate-zipWith : (f : A → B → C) (m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) →
    truncate m≤n (zipWith f xs ys) ≡ zipWith f (truncate m≤n xs) (truncate m≤n ys)
  
  truncate-zipWith-truncate : truncate o≤m (zipWith f (truncate m≤n xs) ys) ≡
    zipWith f (truncate o≤n xs) (truncate o≤m ys)

  zipWith-truncate : zipWith f (truncate p≤p+q xs) (truncate p≤p+q ys) ≡
    truncate p≤p+q (zipWith f xs ys)

  zipWith-truncate₁ : zipWith f (truncate o≤o+m+n xs) (truncate (o≤o+m) ys) ≡
    truncate (o≤o+m) (zipWith f (truncate (o+m≤o+m+n) xs) ys)
  
  truncate-updateAt : (f : A → A) (m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) →
    updateAt (truncate m≤n xs) i f ≡ truncate m≤n (updateAt xs (inject≤ i m≤n) f)

  updateAt-truncate : updateAt (truncate p≤p+q xs) i f ≡ truncate p≤p+q (updateAt xs i′ f)

  truncate++drop≡id : (xs : Vec A (m + n)) → truncate (m≤m+n m n) xs ++ drop m xs ≡ xs

  truncate-map : (f : A → B) (m : ℕ) (m≤n : m ≤ n) (xs : Vec A n) →
  map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)

  ```