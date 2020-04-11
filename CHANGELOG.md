Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

* First instance modules

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

* `Reflection.TypeChecking.MonadSyntax` ↦ `Reflection.TypeChecking.Monad.Syntax`

Deprecated names
----------------

Other major additions
---------------------

* Instance modules:
  ```agda
  Category.Monad.Partiality.Instances
  Codata.Stream.Instances
  Codata.Covec.Instances
  Data.List.Instances
  Data.List.NonEmpty.Instances
  Data.Maybe.Instances
  Data.Vec.Instances
  Function.Identity.Instances
  ```

* Symmetric transitive closures of binary relations:
  ```
  Relation.Binary.Construct.Closure.SymmetricTransitive
  ```

* Type-checking monads
  ```
  Reflection.TypeChecking.Monad
  Reflection.TypeChecking.Monad.Categorical
  Reflection.TypeChecking.Monad.Instances
  ```

Other major changes
-------------------

Other minor additions
---------------------

* Added trans-cong, cong₂-reflˡ and cong₂-reflʳ to `Relation.Binary.PropositionalEquality`
* Made first argument of [,]-∘-distr in `Data.Sum.Properties` explicit

* Added new properties to ` Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  ↭-empty-inv     : xs ↭ [] → xs ≡ []
  ¬x∷xs↭[]        : ¬ ((x ∷ xs) ↭ [])
  ↭-singleton-inv : xs ↭ [ x ] → xs ≡ [ x ]
  ↭-map-inv       : map f xs ↭ ys → ∃ λ ys′ → ys ≡ map f ys′ × xs ↭ ys′
  ↭-length        : xs ↭ ys → length xs ≡ length ys
  ```

* Added new proofs to `Data.Sum.Properties`
  ```agda
  map-id
  map₁₂-commute
  [,]-cong
  [-,]-cong
  [,-]-cong
  map-cong
  map₁-cong
  map₂-cong
  ```

* Added new proofs to `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  nothing-inv : Pointwise R nothing x → x ≡ nothing
  just-inv    : Pointwise R (just x) y → ∃ λ z → y ≡ just z × R x z
  ```
