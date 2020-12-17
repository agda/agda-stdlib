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

* Fixed the fixity of the reasoning combinators in
  `Data.List.Relation.Binary.Subset.(Propositional/Setoid).Properties`so that they
  compose properly.

* Added version to library name

* In `IO`, `⊤`-returning functions (such as `putStrLn`) have been made level polymorphic.
  This may force you to add more type or level annotations to your programs.

Non-backwards compatible changes
--------------------------------

* The internal build utilities package `lib.cabal` has been renamed
  `agda-stdlib-utils.cabal` to avoid potential conflict or confusion.
  Please note that the package is not intended for external use.

* The module `Algebra.Construct.Zero` and `Algebra.Module.Construct.Zero`
  are now level-polymorphic, each taking two implicit level parameters.

* The orders on strings are now using propositional equality as the notion
  of equivalence on characters rather than the equivalent but less inference-friendly
  variant defined by conversion of characters to natural numbers.
  This is in line with our effort to deprecate this badly-behaved equivalence
  relation on characters.

* Previously `_⊖_` in `Data.Integer.Base` was defined inductively as:
  ```agda
  _⊖_ : ℕ → ℕ → ℤ
  m       ⊖ ℕ.zero  = + m
  ℕ.zero  ⊖ ℕ.suc n = -[1+ n ]
  ℕ.suc m ⊖ ℕ.suc n = m ⊖ n
  ```
  which meant that it had to recursively evaluate its unary arguments.
  The definition has been changed as follows to use operations on `ℕ` that are backed
  by builtin operations, greatly improving its performance:
  ```agda
  _⊖_ : ℕ → ℕ → ℤ
  m ⊖ n with m ℕ.<ᵇ n
  ... | true  = - + (n ℕ.∸ m)
  ... | false = + (m ℕ.∸ n)
  ```

* The proofs `↭⇒∼bag` and `∼bag⇒↭` have been moved from
  `Data.List.Relation.Binary.Permutation.Setoid.Properties`
  to `Data.List.Relation.Binary.BagAndSetEquality` as their current location
  were causing cyclic import dependencies.

* Clean up of `IO` to make it more friendly:
  + Renamed `_>>=_` and `_>>_` to `bind` and `seq` respectively to free up the names
    for `do`-notation friendly combinators.
  + Introduced `Colist` and `List` modules for the various `sequence` and `mapM` functions.
    This breaks code that relied on the `Colist`-specific function being exported as part of `IO`.


Deprecated modules
------------------

* The module `TransitiveClosure` in `Induction.WellFounded` has been deprecated.
  You should instead use the standard definition of transitive closure and the
  accompanying proof of well-foundness defined in `Relation.Binary.Construct.Closure.Transitive`.

* The module `Relation.Binary.OrderMorphism` has been deprecated, as the new
  `(Homo/Mono/Iso)morphism` infrastructure in `Algebra.Morphism.Structures` is now
  complete. The new definitions are parameterised by raw bundles instead of bundles
  meaning they are much more flexible to work with.

* The module `Algebra.Operations.CommutativeMonoid` has been deprecated. The definition
  of multiplication and the associated properties have been moved to
  `Algebra.Properties.CommutativeMonoid.Multiplication`. The definition of summation
  which was defined over the deprecated `Data.Table` has been redefined in terms of
  `Data.Vec.Functional` and been moved to `Algbra.Properties.CommutativeMonoid.Summation`.
  The properties of summation in `Algebra.Properties.CommutativeMonoid` have likewise
  been deprecated and moved to `Algebra.Properties.CommutativeMonoid.Summation`.

* The module `Algebra.Operations.Semiring` has been deprecated. The contents has
  been moved to `Algebra.Properties.Semiring.(Multiplication/Exponentiation)`.

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

* In `Data.Char.Properties`, deprecated all of the `_≈_`-related content: this
  relation is equivalent to propositional equality but has worse inference. So
  we are moving towards not using it anymore.

* In `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  mono            ↦ Any-resp-⊆
  map-mono        ↦ map⁺
  concat-mono     ↦ concat⁺
  >>=-mono        ↦ >>=⁺
  _⊛-mono_        ↦ ⊛⁺
  _⊗-mono_        ↦ ⊗⁺
  any-mono        ↦ any⁺
  map-with-∈-mono ↦ map-with-∈⁺
  filter⁺         ↦ filter-⊆
  ```

* In `Data.List.Relation.Binary.Subset.Setoid.Properties`:
    ```agda
  filter⁺         ↦ filter-⊆
  ```

* In `Data.Integer`:
    ```agda
  show ↦ Data.Integer.Show.show
  ```

* In `Data.Rational`:
    ```agda
  show ↦ Data.Rational.Show.show
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

* Generic summation over algebraic structures
  ```
  Algebra.Properties.Monoid.Summation
  Algebra.Properties.CommutativeMonoid.Summation
  ```

* Generic multiplication over algebraic structures
  ```
  Algebra.Properties.Monoid.Multiplication
  Algebra.Properties.Semiring.Multiplication
  ```

* Generic exponentiation over algebraic structures
  ```
  Algebra.Properties.Semiring.Exponentiation
  ```

* Setoid equality over vectors:
  ```
  Data.Vec.Functional.Relation.Binary.Equality.Setoid
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

* Added the following `Show` modules:
  ```agda
  Data.Fin.Show
  Data.Integer.Show
  Data.Rational.Show
  ```

* Added bindings for Haskell's `System.Exit`:
  ```
  System.Exit
  System.Exit.Primitive
  ```

* New morphisms
  ```
  Algebra.Morphism.LatticeMonomorphism
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

* Added new relations in `Data.List.Relation.Binary.Subset.(Propositional/Setoid)`:
  ```agda
  xs ⊇ ys = ys ⊆ xs
  xs ⊉ ys = ¬ xs ⊇ ys
  ```

* Added new proofs in `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  ⊆-respʳ-≋      : _⊆_ Respectsʳ _≋_
  ⊆-respˡ-≋      : _⊆_ Respectsˡ _≋_

  ↭⇒⊆            : _↭_ ⇒ _⊆_
  ⊆-respʳ-↭      : _⊆_ Respectsʳ _↭_
  ⊆-respˡ-↭      : _⊆_ Respectsˡ _↭_
  ⊆-↭-isPreorder : IsPreorder _↭_ _⊆_
  ⊆-↭-preorder   : Preorder _ _ _

  Any-resp-⊆     : P Respects _≈_ → (Any P) Respects _⊆_
  All-resp-⊇     : P Respects _≈_ → (All P) Respects _⊇_

  xs⊆xs++ys      : xs ⊆ xs ++ ys
  xs⊆ys++xs      : xs ⊆ ys ++ xs
  ++⁺ʳ           : xs ⊆ ys → zs ++ xs ⊆ zs ++ ys
  ++⁺ˡ           : xs ⊆ ys → xs ++ zs ⊆ ys ++ zs
  ++⁺            : ws ⊆ xs → ys ⊆ zs → ws ++ ys ⊆ xs ++ zs
  ```

* Added new proofs in `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  ↭⇒⊆            : _↭_ ⇒ _⊆_
  ⊆-respʳ-↭      : _⊆_ Respectsʳ _↭_
  ⊆-respˡ-↭      : _⊆_ Respectsˡ _↭_
  ⊆-↭-isPreorder : IsPreorder _↭_ _⊆_
  ⊆-↭-preorder   : Preorder _ _ _

  Any-resp-⊆     : (Any P) Respects _⊆_
  All-resp-⊇     : (All P) Respects _⊇_

  xs⊆xs++ys      : xs ⊆ xs ++ ys
  xs⊆ys++xs      : xs ⊆ ys ++ xs
  ++⁺ʳ           : xs ⊆ ys → zs ++ xs ⊆ zs ++ ys
  ++⁺ˡ           : xs ⊆ ys → xs ++ zs ⊆ ys ++ zs
  ```

* Added new proof in `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  ++↭ʳ++ : xs ++ ys ↭ xs ʳ++ ys
  ```

* Added new proof in `Data.List.Relation.Binary.Permutation.Setoi.Properties`:
  ```agda
  ++↭ʳ++ : xs ++ ys ↭ xs ʳ++ ys
  ```

* Added new definition in `Data.Nat.Base`:
  ```agda
  _≤ᵇ_ : (m n : ℕ) → Bool
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  ≤∧≮⇒≡ : m ≤ n → m ≮ n → m ≡ n
  ≤ᵇ⇒≤ : T (m ≤ᵇ n) → m ≤ n
  ≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)

  <ᵇ-reflects-< : Reflects (m < n) (m <ᵇ n)
  ≤ᵇ-reflects-≤ : Reflects (m ≤ n) (m ≤ᵇ n)

  *-distribˡ-⊔          : _*_ DistributesOverˡ _⊔_
  *-distribʳ-⊔          : _*_ DistributesOverʳ _⊔_
  *-distrib-⊔           : _*_ DistributesOver _⊔_
  *-distribˡ-⊓          : _*_ DistributesOverˡ _⊓_
  *-distribʳ-⊓          : _*_ DistributesOverʳ _⊓_
  *-distrib-⊓           : _*_ DistributesOver _⊓_
  ```

* Added new proofs in `Data.Sign.Properties`:
  ```agda
  s*opposite[s]≡- : ∀ s → s * opposite s ≡ -
  opposite[s]*s≡- : ∀ s → opposite s * s ≡ -
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

* Added new definition to `Data.Char.Base`:
  ```agda
  _≉_ : Rel Char zero
  _≤_ : Rel Char zero
  ```

* Added proofs to `Data.Char.Properties`:
  ```agda
  ≉⇒≢ : _≉_ → x ≢ y

  <-trans : Transitive _<_
  <-asym  : Asymmetric _<_
  <-cmp   : Trichotomous _≡_ _<_

  _≤?_                : Decidable _≤_
  ≤-reflexive         : _≡_ ⇒ _≤_
  ≤-trans             : Transitive _≤_
  ≤-antisym           : Antisymmetric _≡_ _≤_
  ≤-isPreorder        : IsPreorder _≡_ _≤_
  ≤-isPartialOrder    : IsPartialOrder _≡_ _≤_
  ≤-isDecPartialOrder : IsDecPartialOrder _≡_ _≤_

  ≤-preorder : Preorder _ _ _
  ≤-poset    : Poset _ _ _
  ≤-decPoset : DecPoset _ _ _
  ```

* Added infix declarations to `Data.Product.∃-syntax` and `Data.Product.∄-syntax`.

* Added new function to `Data.List.Base`:
  ```agda
  unsnoc : List A → Maybe (List A × A)
  ```

* Added new definitions to `Function.Bundles`:
  ```agda
  record Func : Set _
  _⟶_ : Set a → Set b → Set _
  mk⟶ : (A → B) → A ⟶ B
  ```

* Added new proofs to `Function.Construct.Composition`:
  ```agda
  function : Func R S → Func S T → Func R T
  _∘-⟶_    : (A ⟶ B) → (B ⟶ C) → (A ⟶ C)
  ```

* Added new proofs to `Function.Construct.Identity`:
  ```agda
  function : Func S S
  id-⟶     : A ⟶ A
  ```

* Added new proofs to `Codata.Delay.Properties`:
  ```agda
  ⇓-unique            : (d⇓₁ : d ⇓) (d⇓₂ : d ⇓) → d⇓₁ ≡ d⇓₂
  bind̅₁               : bind d f ⇓ → d ⇓
  bind̅₂               : (bind⇓ : bind d f ⇓) → f (extract (bind̅₁ bind⇓)) ⇓
  extract-bind-⇓      : (d⇓ : d ⇓) (f⇓ : f (extract d⇓) ⇓) → extract (bind-⇓ d⇓ f⇓) ≡ extract f⇓
  extract-bind̅₂-bind⇓ : (bind⇓ : bind d f ⇓) → extract (bind̅₂ d bind⇓) ≡ extract bind⇓
  bind⇓-length        : (bind⇓ : bind d f ⇓) (d⇓ : d ⇓) (f⇓ : f (extract d⇓) ⇓) → toℕ (length-⇓ bind⇓) ≡ toℕ (length-⇓ d⇓) ℕ.+ toℕ (length-⇓ f⇓)
  ```

* Added new function to `Data.List.Base`:
  ```agda
  linesBy : Decidable P → List A → List (List A)
  ```

* Added new functions to `Data.String.Base`:
  ```agda
  linesBy : Decidable P → String → List String
  lines   : String → List String
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  when : Bool → A → Maybe A
  ```

* Added new function to `Data.Nat.Show`:
  ```agda
  readMaybe : (base : ℕ) → {base≤16 : True (base ≤? 16)} → String → Maybe ℕ
  ```

* Added new functions to `Data.Tree.AVL`:
  ```agda
  foldr : (∀ {k} → Val k → A → A) → A → Tree V → A
  size  : Tree V → ℕ

  intersectionWith  : (∀ {k} → Val k → Wal k → Xal k) → Tree V → Tree W → Tree X
  intersection      : Tree V → Tree V → Tree V
  intersectionsWith : (∀ {k} → Val k → Val k → Val k) → List (Tree V) → Tree V
  intersections     : List (Tree V) → Tree V
  ```

* Added new functions to `Data.Tree.AVL.Indexed`:
  ```agda
  foldr : (∀ {k} → Val k → A → A) → A → Tree V l u h → A
  size  : Tree V → ℕ
  ```

* Added new functions to `Data.Tree.AVL.IndexedMap` module:
  ```agda
  foldr : (∀ {k} → Value k → A → A) → A → Map → A
  size : Map → ℕ
  ```

* Added new functions to `Data.Tree.AVL.Map`:
  ```agda
  foldr : (Key → V → A → A) → A → Map V → A
  size  : Map V → ℕ

  intersectionWith  : (V → W → X) → Map V → Map W → Map X
  intersection      : Map V → Map V → Map V
  intersectionsWith : (V → V → V) → List (Map V) → Map V
  intersections     : List (Map V) → Map V
  ```

* Added new functions to `Data.Tree.AVL.Sets`:
  ```agda
  foldr : (A → B → B) → B → ⟨Set⟩ → B
  size  : ⟨Set⟩ → ℕ

  union  : ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
  unions : List ⟨Set⟩ → ⟨Set⟩

  intersection  : ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
  intersections : List ⟨Set⟩ → ⟨Set⟩
  ```
