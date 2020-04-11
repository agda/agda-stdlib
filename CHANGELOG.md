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

* Added proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  trans-cong  : trans (cong f p) (cong f q) ≡ cong f (trans p q)
  cong₂-reflˡ : cong₂ _∙_ refl p ≡ cong (x ∙_) p
  cong₂-reflʳ : cong₂ _∙_ p refl ≡ cong (_∙ u) p
  ```

* Made first argument of `[,]-∘-distr` in `Data.Sum.Properties` explicit

* Added new proofs to ``Data.Sum.Properties`:
  ```agda
  map-id        : map id id ≗ id
  map₁₂-commute : map₁ f ∘ map₂ g ≗ map₂ g ∘ map₁ f
  [,]-cong      : f ≗ f′ → g ≗ g′ → [ f , g ] ≗ [ f′ , g′ ]
  [-,]-cong     : f ≗ f′ → [ f , g ] ≗ [ f′ , g ]
  [,-]-cong     : g ≗ g′ → [ f , g ] ≗ [ f , g′ ]
  map-cong      : f ≗ f′ → g ≗ g′ → map f g ≗ map f′ g′
  map₁-cong     : f ≗ f′ → map₁ f ≗ map₁ f′
  map₂-cong     : g ≗ g′ → map₂ g ≗ map₂ g′
  ```

* Added new proofs to `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  nothing-inv : Pointwise R nothing x → x ≡ nothing
  just-inv    : Pointwise R (just x) y → ∃ λ z → y ≡ just z × R x z
  ```
