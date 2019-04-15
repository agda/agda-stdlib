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

* In `Reflection`, `returnT` is renamed to `return`.

Removed features
----------------

Deprecated features
-------------------

Other minor additions
---------------------

* Added new function to `Data.Digit`:
  ```agda
  toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-swap        : All (λ xs → All (xs ~_) ys) xss → All (λ y → All (_~ y) xss) ys

  applyDownFrom⁺₁ : (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₂ : (∀ i → P (f i)) → All P (applyDownFrom f n)
  ```

* Added new proof to `Data.Nat.DivMod`:
  ```agda
  [a/n]*n≤a : (a div (suc n)) * (suc n) ≤ a
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  n≢0⇒n>0 : n ≢ 0 → n > 0
  m≤m*n   : 0 < n → m ≤ m * n
  m<m*n   : 0 < m → 1 < n → m < m * n
  ```

* The function `show` in `Data.Nat.Show` has been reimplemented and,
  when compiled, now runs in time `O(log₁₀(n))` rather than `O(n)`.

* Added new functions to `Data.Product`:
  ```agda
  zip′ : (A → B → C) → (D → E → F) → A × D → B × E → C × F
  ```

* Added new proof to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  ≢-sym : Symmetric {A = A} _≢_
  ```

* Reflection re-exports all operations and types defined in `Agda.Builtin.Reflection`.
  In detail,

  * For `TC` monad`: reduce`, `declarePostulate`, `commitTC`, `isMacro`, and `withNormalisation` are now re-exported.
`returnT` is renamed to `return` and infix notations `_>>=_` and `_>>_` for bind operation are added.
  * For `Fixity`: `non-assoc`, `related`, `unrelated`, and `fixity` are
    re-exported.  `left-assoc` is renamed to `assocˡ`, `right-assoc` to
`assocʳ`, and `primQNameFixity` to `getFixity`.

* Reflection adds some (experimental) pattern synonyms. E.g.,

  * `vArg` for visible relevant argument `arg (arg-info visible relevant)`
  * `hLam s t` for lambda abstraction with a hidden variable `lam hidden (abs s t)`
  * `hΠ[_∶_]_ s a ty` for Π type with an implicit index, i.e. `pi (arg (arg-info hidden relevant) a) (abs s ty)`
