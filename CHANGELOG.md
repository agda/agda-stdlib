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
  padRight-lookup : (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) → lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i

  padRight-map : (f : A → B) (m≤n : m ≤ n) (a : A) (xs : Vec A m) → map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)

  padRight-zipWith : (f : A → B → C) (m≤n : m ≤ n) (a : A) (b : B) (xs : Vec A m) (ys : Vec B m) →
                   zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡ padRight m≤n (f a b) (zipWith f xs ys)

  padRight-zipWith₁ : (f : A → B → C) (o≤m : o ≤ m) (m≤n : m ≤ n) (a : A) (b : B) (xs : Vec A m) (ys : Vec B o) →
                    zipWith f (padRight m≤n a xs) (padRight (≤-trans o≤m m≤n) b ys) ≡
                    padRight m≤n (f a b) (zipWith f xs (padRight o≤m b ys))

  padRight-take : (m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) → take m (cast n≡m+o (padRight m≤n a xs)) ≡ xs

  padRight-drop : (m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) → drop m (cast n≡m+o (padRight m≤n a xs)) ≡ replicate o a

  padRight-updateAt : (m≤n : m ≤ n) (x : A) (xs : Vec A m) (f : A → A) (i : Fin m) →
                    updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡ padRight m≤n x (updateAt xs i f)
  ```
