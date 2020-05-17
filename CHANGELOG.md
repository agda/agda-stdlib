Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

* First instance modules

* New standardised numeric predicates `NonZero`, `Positive`, `Negative`,
  `NonPositive`, `NonNegative`, especially designed to work as instance
  arguments.

Bug-fixes
---------

* Fixed various algebraic bundles not correctly re-exporting
  `commutativeSemigroup` proofs.

Non-backwards compatible changes
--------------------------------

* `Data.Empty.Polymorphic` and `Data.Unit.Polymorphic` were rewritten
  to explicitly use `Lift` rather that defining new types. This means
  that these are now compatible with `⊥` and `⊤` from the rest of the
  library. This allowed them to be used in the rest of library where
  explicit `Lift` was used.

Deprecated modules
------------------

* `Data.AVL` and all of its submodules have been moved to `Data.Tree.AVL`

* The module `Induction.WellFounded.InverseImage` has been deprecated. The proofs
  `accessible` and `wellFounded` have been moved to `Relation.Binary.Construct.On`.

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

* Predicate for lists that are sorted with respect to a total order
  ```
  Data.List.Relation.Unary.Sorted.TotalOrder
  Data.List.Relation.Unary.Sorted.TotalOrder.Properties
  ```

* Consequences for basic morphism properties
  ```
  Algebra.Morphism.Consequences
  ```

* Subtraction for binary naturals:
  ```
  Data.Nat.Binary.Subtraction
  ```

Other major changes
-------------------


Other minor additions
---------------------

* Added new proof to `Data.Fin.Induction`:
  ```agda
  <-wellFounded : WellFounded _<_
  ```

* Added new types and constructors to `Data.Integer.Base`:
  ```agda
  NonZero     : Pred ℤ 0ℓ
  Positive    : Pred ℤ 0ℓ
  Negative    : Pred ℤ 0ℓ
  NonPositive : Pred ℤ 0ℓ
  NonNegative : Pred ℤ 0ℓ

  ≢-nonZero   : p ≢ 0ℤ → NonZero p
  >-nonZero   : p > 0ℤ → NonZero p
  <-nonZero   : p < 0ℤ → NonZero p
  positive    : p > 0ℤ → Positive p
  negative    : p < 0ℤ → Negative p
  nonPositive : p ≤ 0ℤ → NonPositive p
  nonNegative : p ≥ 0ℤ → NonNegative p
  ```

* Added new function to `Data.Nat.Properties`:
 ```agda
 ∸-magma           : Magma _ _

 pred[m∸n]≡m∸[1+n] : pred (m ∸ n) ≡ m ∸ suc n
 ```

* The module `Data.Nat.Binary.Induction` now re-exports `Acc` and `acc`.

* Added new functions (proofs) to `Data.Nat.Binary.Properties`:
 ```agda
 +-isSemigroup            : IsSemigroup _+_
 +-semigroup              : Semigroup 0ℓ 0ℓ
 +-isCommutativeSemigroup : IsCommutativeSemigroup _+_
 +-commutativeSemigroup   : CommutativeSemigroup 0ℓ 0ℓ
 x≡0⇒double[x]≡0          : x ≡ 0ᵇ → double x ≡ 0ᵇ
 double-suc               : double (suc x) ≡ 2ᵇ + double x
 pred[x]+y≡x+pred[y]      : x ≢ 0ᵇ → y ≢ 0ᵇ → (pred x) + y ≡  x + pred y
 x+suc[y]≡suc[x]+y        : x + suc y ≡ suc x + y
 ```

* The module `Data.Nat.Bin.Induction` now re-exports `Acc` and `acc` from `Induction.WellFounded`.

* Added proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  trans-cong  : trans (cong f p) (cong f q) ≡ cong f (trans p q)
  cong₂-reflˡ : cong₂ _∙_ refl p ≡ cong (x ∙_) p
  cong₂-reflʳ : cong₂ _∙_ p refl ≡ cong (_∙ u) p
  ```

* Made first argument of `[,]-∘-distr` in `Data.Sum.Properties` explicit

* Added new function to `Data.List.Base`:
  ```agda
  wordsBy : Decidable P → List A → List (List A)
  ```

* Added new properties to ` Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  ↭-empty-inv     : xs ↭ [] → xs ≡ []
  ¬x∷xs↭[]        : ¬ ((x ∷ xs) ↭ [])
  ↭-singleton-inv : xs ↭ [ x ] → xs ≡ [ x ]
  ↭-map-inv       : map f xs ↭ ys → ∃ λ ys′ → ys ≡ map f ys′ × xs ↭ ys′
  ↭-length        : xs ↭ ys → length xs ≡ length ys
  ```

* Added new proofs to `Data.List.Relation.Unary.Linked`:
  ```agda
  map⁻    : Linked R (map f xs) → Linked (λ x y → R (f x) (f y)) xs
  filter⁺ : Transitive R → Linked R xs → Linked R (filter P? xs)
  ```

* Added new proofs to `Data.Sum.Properties`:
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

* Added new functions to `Data.String.Base`:
  ```agda
  wordsBy : Decidable P → String → List String
  words : String → List String
  ```

* Added new types and constructors to `Data.Nat.Base`:
  ```agda
  NonZero   : ℕ → Set

  ≢-nonZero : n ≢ 0 → NonZero n
  >-nonZero : n > 0 → NonZero n
  ```

* The function `pred` in `Data.Nat.Base` has been redefined as `pred n = n ∸ 1`.
  Consequently proofs about `pred` are now just special cases of proofs for `_∸_`.
  The change is fully backwards compatible.

* Added new proof to `Data.Nat.Coprimality`:
  ```agda
  ¬0-coprimeTo-2+ : ¬ Coprime 0 (2 + n)
  recompute       : .(Coprime n d) → Coprime n d
  ```

* Added new types and constructors to `Data.Rational.Unnormalised`:
  ```agda
  NonZero     : Pred ℚ 0ℓ
  Positive    : Pred ℚ 0ℓ
  Negative    : Pred ℚ 0ℓ
  NonPositive : Pred ℚ 0ℓ
  NonNegative : Pred ℚ 0ℓ

  ≢-nonZero   : p ≢ 0ℚ → NonZero p
  >-nonZero   : p > 0ℚ → NonZero p
  <-nonZero   : p < 0ℚ → NonZero p
  positive    : p > 0ℚ → Positive p
  negative    : p < 0ℚ → Negative p
  nonPositive : p ≤ 0ℚ → NonPositive p
  nonNegative : p ≥ 0ℚ → NonNegative p
  ```

* Added new types and constructors to `Data.Rational.Unnormalised`
  ```agda
  _≠_         : Rel ℚᵘ 0ℓ

  NonZero     : Pred ℚᵘ 0ℓ
  Positive    : Pred ℚᵘ 0ℓ
  Negative    : Pred ℚᵘ 0ℓ
  NonPositive : Pred ℚᵘ 0ℓ
  NonNegative : Pred ℚᵘ 0ℓ

  ≢-nonZero   : p ≠ 0ℚᵘ → NonZero p
  >-nonZero   : p > 0ℚᵘ → NonZero p
  <-nonZero   : p < 0ℚᵘ → NonZero p
  positive    : p > 0ℚᵘ → Positive p
  negative    : p < 0ℚᵘ → Negative p
  nonPositive : p ≤ 0ℚᵘ → NonPositive p
  nonNegative : p ≥ 0ℚᵘ → NonNegative p
  ```
  * New module `Relation.Nullary.Indexed` with a `Level`-polymorphic negation
  ```agda
  ¬ : (b : Level) → Set ℓ → Set (ℓ ⊔ b)
  ```
