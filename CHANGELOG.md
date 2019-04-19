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
Category.Monad.Reader

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

Removed features
----------------

Deprecated features
-------------------

* In `Reflection`:
  ```agda
  returnT ↦ return
  ```

Other minor additions
---------------------

* Added new function to `Data.Digit`:
  ```agda
  toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
  ```

* Added new proof to `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`:
  ```agda
  concat⁺ : Sublist (Sublist R) ass bss → Sublist R (concat ass) (concat bss)
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

* Added new names, functions and shorthand to `Reflection`:
  ```agda
  Names             = List Name
  Args A            = List (Arg A)
  
  map-Arg           : (A → B) → Arg A → Arg B
  map-Args          : (A → B) → Args A → Args B
  map-Abs           : (A → B) → Abs A → Abs B
  
  reduce            : Term → TC Term
  declarePostulate  : Arg Name → Type → TC ⊤
  commitTC          : TC ⊤
  isMacro           : Name → TC Bool
  withNormalisation : Bool → TC A → TC A
  _>>=_             : TC A → (A → TC B) → TC B
  _>>_              : TC A → TC B → TC B
  
  assocˡ            : Associativity
  assocʳ            : Associativity
  non-assoc         : Associativity
  unrelated         : Precedence
  related           : Int → Precedence
  fixity            : Associativity → Precedence → Fixity
  getFixity         : Name → Fixity
  
  vArg ty           = arg (arg-info visible relevant)   ty
  hArg ty           = arg (arg-info hidden relevant)    ty
  iArg ty           = arg (arg-info instance′ relevant) ty
  vLam s t          = lam visible   (abs s t)
  hLam s t          = lam hidden    (abs s t)
  iLam s t          = lam instance′ (abs s t)
  Π[_∶_]_ s a ty    = pi a (abs s ty)
  vΠ[_∶_]_ s a ty   = Π[ s ∶ (vArg a) ] ty
  hΠ[_∶_]_ s a ty   = Π[ s ∶ (hArg a) ] ty
  iΠ[_∶_]_ s a ty   = Π[ s ∶ (iArg a) ] ty
  ```

* The relation `_≅_` in `Relation.Binary.HeterogeneousEquality` has
  been generalised so that the types of the two equal elements need not
  be at the same universe level.

