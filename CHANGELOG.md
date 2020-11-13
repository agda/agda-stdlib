Version 1.5-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

Highlights
----------

Bug-fixes
---------

* The example module `Maybe` in `Relation.Binary.Construct.Closure.Reflexive` was
  accidentally exposed publicly. It has been made private.

* Fixed the type of the proof `map-id` in `List.Relation.Unary.All.Properties`,
  which was incorrectly abstracted over unused module parameters.

* Fixed bug where `IsRelIsomorphism` in `Relation.Binary.Morphism.Structures` did not
  publicly re-export the contents of `IsRelMonomorphism`.

* The binary relation `_≉_` exposed by records in `Relation.Binary.Bundles` now has
  the correct infix precedence.

* Added version to library name

Non-backwards compatible changes
--------------------------------

* The internal build utilities package `lib.cabal` has been renamed
  `agda-stdlib-utils.cabal` to avoid potential conflict or confusion.
  Please note that the package is not intended for external use.

* The module `Algebra.Construct.Zero` and `Algebra.Module.Construct.Zero`
  are now level-polymorphic, each taking two implicit level parameters.

* Previously the definition of `_⊖_` in `Data.Integer.Base` was defined
  inductively as:
  ```agda
  _⊖_ : ℕ → ℕ → ℤ
  m       ⊖ ℕ.zero  = + m
  ℕ.zero  ⊖ ℕ.suc n = -[1+ n ]
  ℕ.suc m ⊖ ℕ.suc n = m ⊖ n
  ```
  which meant that the unary arguments had to be evaluated. To make it
  much faster it's definition has been changed to use operations on `ℕ`
  that are backed by builtin operations:
  ```agda
  _⊖_ : ℕ → ℕ → ℤ
  m ⊖ n with m ℕ.<ᵇ n
  ... | true  = - + (n ℕ.∸ m)
  ... | false = + (m ℕ.∸ n)
  ```

Deprecated modules
------------------

* The module `TransitiveClosure` in `Induction.WellFounded` has been deprecated.
  You should instead use the standard definition of transitive closure and the
  accompanying proof of well-foundness defined in `Relation.Binary.Construct.Closure.Transitive`.

* The module `Relation.Binary.OrderMorphism` has been deprecated, as the new
  `(Homo/Mono/Iso)morphism` infrastructure in `Algebra.Morphism.Structures` is now
  complete. The new definitions are parameterised by raw bundles instead of bundles
  meaning they are much more flexible to work with.

Deprecated names
----------------

* The immediate contents of `Algebra.Morphism` have been deprecated, as the new
  `(Homo/Mono/Iso)morphism` infrastructure in `Algebra.Morphism.Structures` is now
  complete. The new definitions are parameterised by raw bundles instead of bundles
  meaning they are much more flexible to work with. The replacements are as following:
  ```agda
  IsSemigroupMorphism                   ↦ IsSemigroupHomomorphism
  IsMonoidMorphism                      ↦ IsMonoidHomomorphism
  IsCommutativeMonoidMorphism           ↦ IsMonoidHomomorphism
  IsIdempotentCommutativeMonoidMorphism ↦ IsMonoidHomomorphism
  IsGroupMorphism                       ↦ IsGroupHomomorphism
  IsAbelianGroupMorphism                ↦ IsGroupHomomorphism
  ```

* In `Relation.Binary.Construct.Closure.Reflexive`:
  ```agda
  Refl ↦ ReflClosure
  ```

* In `Relation.Binary.Construct.Closure.Transitive`:
  ```agda
  Plus′ ↦ TransClosure
  ```

New modules
-----------

* Added various generic morphism constructions for binary relations:
  ```agda
  Relation.Binary.Morphism.Construct.Composition
  Relation.Binary.Morphism.Construct.Constant
  Relation.Binary.Morphism.Construct.Identity
  ```

* Added `Reflection.Traversal` for generic de Bruijn-aware traversals of reflected terms.
* Added `Reflection.DeBruijn` with weakening, strengthening and free variable operations
  on reflected terms.

* Added `Relation.Binary.TypeClasses` for type classes to be used with instance search.

* Added various modules containing `instance` declarations:
  `Data.Bool.Instances`, `Data.Char.Instances`, `Data.Fin.Instances`,
  `Data.Float.Instances`, `Data.Integer.Instances`,
  `Data.List.Instances`, `Data.Nat.Instances`,
  `Data.Nat.Binary.Instances`, `Data.Product.Instances`,
  `Data.Rational.Instances`, `Data.Sign.Instances`,
  `Data.String.Instances`, `Data.Sum.Instances`,
  `Data.These.Instances`, `Data.Unit.Instances`,
  `Data.Unit.Polymorphic.Instances`, `Data.Vec.Instances`,
  `Data.Word.Instances`, and `Reflection.Instances`.

* Generic divisibility over algebraic structures
  ```
  Algebra.Divisibility
  Algebra.Properties.Magma.Divisibility
  Algebra.Properties.Semigroup.Divisibility
  Algebra.Properties.Monoid.Divisibility
  Algebra.Properties.CommutativeSemigroup.Divisibility
  ```

* Heterogeneous relation characterising a list as an infix segment of another:
  ```
  Data.List.Relation.Binary.Infix.Heterogeneous
  Data.List.Relation.Binary.Infix.Heterogeneous.Properties
  ```
  and added `Properties` file for the homogeneous variants of (pre/in/suf)fix:
  ```
  Data.List.Relation.Binary.Prefix.Homogeneous.Properties
  Data.List.Relation.Binary.Infix.Homogeneous.Properties
  Data.List.Relation.Binary.Suffix.Homogeneous.Properties
  ```

* Added bindings for Haskell's `System.Environment`:
  ```
  System.Environment
  System.Environment.Primitive
  ```

Other major changes
-------------------

* The new module `Relation.Binary.TypeClasses` re-exports `_≟_` from
  `IsDecEquivalence` and `_≤?_` from `IsDecTotalOrder` where the
  principal argument has been made into an instance argument. This
  enables automatic resolution if the corresponding module
  `Data.*.Instances` (or `Reflection.Instances`) is imported as well.
  For example, if `Relation.Binary.TypeClasses`, `Data.Nat.Instances`,
  and `Data.Bool.Instances` have been imported, then `true ≟ true` has
  type `Dec (true ≡ true)`, while `0 ≟ 1` has type `Dec (0 ≡ 1)`. More
  examples can be found in `README.Relation.Binary.TypeClasses`.

Other minor additions
---------------------

* All bundles in `Algebra.Bundles` now re-export the binary relation `_≉_` from the underlying `Setoid`.

* Added `Reflection.TypeChecking.Format.errorPartFmt`.

* Added new properties to `Data.List.Properties`:
  ```agda
  concat-++ : concat xss ++ concat yss ≡ concat (xss ++ yss)
  concat-concat : concat ∘ map concat ≗ concat ∘ concat
  concat-[-] : concat ∘ map [_] ≗ id
  ```

* Added new records to `Algebra.Bundles`:
  ```agda
  CommutativeMagma c ℓ : Set (suc (c ⊔ ℓ))
  RawNearSemiring c ℓ : Set (suc (c ⊔ ℓ))
  RawLattice c ℓ : Set (suc (c ⊔ ℓ))
  CancellativeCommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new definitions to `Algebra.Definitions`:
  ```agda
  AlmostLeftCancellative  e _•_ = ∀ {x} y z → ¬ x ≈ e → (x • y) ≈ (x • z) → y ≈ z
  AlmostRightCancellative e _•_ = ∀ {x} y z → ¬ x ≈ e → (y • x) ≈ (z • x) → y ≈ z
  AlmostCancellative      e _•_ = AlmostLeftCancellative e _•_ × AlmostRightCancellative e _•_
  ```

* Added new records to `Algebra.Morphism.Structures`:
  ```agda
  IsNearSemiringHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsNearSemiringMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsNearSemiringIsomorphism  (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  IsSemiringHomomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsSemiringMonomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsSemiringIsomorphism   (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  IsLatticeHomomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsLatticeMonomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsLatticeIsomorphism   (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  ```

* Added new definitions to `Algebra.Structures`:
  ```agda
  IsCommutativeMagma (• : Op₂ A) : Set (a ⊔ ℓ)
  IsCancellativeCommutativeSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ)
  ```

* Added new proofs in `Data.Integer.Properties`:
  ```agda
  [1+m]⊖[1+n]≡m⊖n : suc m ⊖ suc n ≡ m ⊖ n
  ⊖-≤             : m ≤ n → m ⊖ n ≡ - + (n ∸ m)
  -m+n≡n⊖m        : - (+ m) + + n ≡ n ⊖ m
  m-n≡m⊖n         : + m + (- + n) ≡ m ⊖ n
  ```

* Added new definition in `Data.Nat.Base`:
  ```agda
  _≤ᵇ_ : (m n : ℕ) → Bool
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  ≤ᵇ⇒≤ : T (m ≤ᵇ n) → m ≤ n
  ≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)

  <ᵇ-reflects-< : Reflects (m < n) (m <ᵇ n)
  ≤ᵇ-reflects-≤ : Reflects (m ≤ n) (m ≤ᵇ n)
  ```

* Added new proof in `Relation.Nullary.Reflects`:
  ```agda
  fromEquivalence : (T b → P) → (P → T b) → Reflects P b
  ```

* Add new properties to `Data.Vec.Properties`:
  ```agda
  take-distr-zipWith : take m (zipWith f u v) ≡ zipWith f (take m u) (take m v)
  take-distr-map : take m (map f v) ≡ map f (take m v)
  drop-distr-zipWith : drop m (zipWith f u v) ≡ zipWith f (drop m u) (drop m v)
  drop-distr-map : drop m (map f v) ≡ map f (drop m v)
  take-drop-id : take m v ++ drop m v ≡ v
  zipWith-replicate : zipWith {n = n} _⊕_ (replicate x) (replicate y) ≡ replicate (x ⊕ y)
  ```

* Added new proofs to `Relation.Binary.Construct.Closure.Transitive`:
  ```agda
  reflexive   : Reflexive _∼_ → Reflexive _∼⁺_
  symmetric   : Symmetric _∼_ → Symmetric _∼⁺_
  transitive  : Transitive _∼⁺_
  wellFounded : WellFounded _∼_ → WellFounded _∼⁺_
  ```

* Add new properties to `Data.Integer.Properties`:
  ```agda
  +-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
  ```

* Added infix declarations to `Data.Product.∃-syntax` and `Data.Product.∄-syntax`.
