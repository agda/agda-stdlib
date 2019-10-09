Version 1.2-dev
===============

The library has been tested using Agda version 2.6.0.1.

Changes since 1.1:

Highlights
----------



Bug-fixes
---------



Non-backwards compatible changes
--------------------------------

### New function hierarchy

* The main problems with the current way various types of functions are
handled are:
  1. The raw functions were wrapped in the  equality-preserving
     type `_⟶_` from `Function.Equality`. As the rest of the library
     very rarely used such wrapped functions, it was almost impossible
     to write code that interfaced neatly  between the `Function` hierarchy
     and, for example, the `Algebra` hierarchy.
  2. The symbol `_⟶_` that was used for equality preserving functions
     was almost indistinguishable from ordinary functions `_→_` in many fonts,
     leading to confusion when reading code.
  3. The hierarchy didn't follow the same pattern as the other record
     hierarchies in the standard library. Coupled with point 1., this meant
     that anecdotally people are scared away from it.
  4. There was no way of specifying a function has a specific property
     (e.g. is injective) without specifying all the properties required
     of the equality relation as well. This is in contrast to the
     `Relation.Binary` and `Algebra` hierarchies where it is perfectly
     possible to specify that for example an operation is commutative
     without providing all the proofs associated with the equality relation.

* To address these problems a new function hierarchy similar to the ones in
`Relation.Binary` and `Algebra` has been created. The new modules are as
follows:
  - `Function.Definitions` containing definitions like `Injective`,
    `Surjective` parameterised by the function and the equality relations
     over the domain and codomain.
  - `Function.Structures` containing definitions like `IsInjection`,
     `IsSurjection`, once again parameterised by the function and the equality
     relations but also wrapping up all the equality and congruence lemmas.
  - `Function.Packages` containing definitions like `Injection`, `Surjection`
     which provides essentially the same top-level interface as currently exists,
     i.e. parameterised by setoids but hiding the function.
  - The old file `Function` has been moved to `Function.Core` and `Function`
    now exports the whole of this hierarchy, just like `Relation.Binary`.

* These changes are nearly entirely backwards compatible. The only problem will occur
is when code imports both `Function` and e.g. `Function.Injection` in which case the
old and new definitions of `Injection` will clash. In the short term this can
immediately be fixed by importing `Function.Core` instead of `Function`. However
we would encourage to the new hierarchy in the medium to long term.

* The list of new modules is as follows:
  ```agda
  Function.Construct.Identity
  Function.Construct.Composition
  ```

* The old modules will probably be deprecated (NOT COMPLETED AS OF YET)
  ```agda
  Function.Equivalence
  Function.Equality
  Function.Bijection
  Function.Injection
  Function.Surjection
  Function.LeftInverse
  ```

* Minor change: the propositional package for left inverses has been renamed
from `_↞_` to `_↩_` in order to make room for the new package for right inverse `_↪_`.

### Re-implementation of `Data.Bin`

* The current implementation of naturals represented natively in Agda in `Data.Bin`
  has proven hard to work with. Therefore a new, simpler implementation which avoids
  using `List` has been added as `Data.Nat.Binary`. This representation was inspired
  by the letter by Martin Escardo to the Agda mailing list. The original code resides at
  http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html

* The existing modules `Data.Bin` and `Data.Bin.Properties` still exist but have been
  deprecated and may be removed in some future release of the library.

### Other breaking changes

#### Harmonizing `List.All` and `Vec` in their role as finite maps.

`Data.List.Relation.Unary.All.updateAt` is analogous to
`Data.Vec.updateAt` and thus, the API for `All` has been changed to
match the one for `Vec`:

* The "points-to" relation `_[_]=_` for vectors has been ported to `All`.

* The property
  `Data.List.Relation.Unary.All.Properties.updateAt-updates` is now
  formulated in terms of the new "points-to" relation `_[_]=_` rather than
  the `lookup` function.  The old property is (in a minor variant)
  available under the name `lookup∘updateAt`.

* `updateAt-cong` has been renamed to `updateAt-cong-relative`, and a new
  `updateAt-cong` has been ported from `Vec`.

* Further properties of `Vec` have been ported to `All`:
  ```
  []=lookup
  []=⇒lookup
  lookup⇒[]=
  updateAt-minimal
  updateAt-id-relative
  updateAt-compose-relative
  updateAt-commutes
  ```


#### Other

* The proofs `isPreorder` and `preorder` have been moved from the `Setoid`
  record to the module `Relation.Binary.Properties.Setoid`.

New modules
-----------
The following new modules have been added to the library:

  ```
  Algebra.Morphism.RawMagma
  Algebra.Morphism.RawMonoid

  Algebra.Properties.Semigroup
  Algebra.Properties.CommutativeSemigroup

  Data.AVL.Map

  Data.Empty.Polymorphic

  Data.Nat.Binary
  Data.Nat.Binary.Base
  Data.Nat.Binary.Induction
  Data.Nat.Binary.Properties

  Data.Integer.GCD
  Data.Integer.LCM

  Data.List.Fresh
  Data.List.Fresh.Properties
  Data.List.Fresh.Relation.Unary.All
  Data.List.Fresh.Relation.Unary.All.Properties
  Data.List.Fresh.Relation.Unary.Any
  Data.List.Fresh.Relation.Unary.Any.Properties
  Data.List.Fresh.Membership
  Data.List.Fresh.Membership.Properties

  Data.List.Kleene
  Data.List.Kleene.AsList
  Data.List.Kleene.Base

  Data.List.Relation.Binary.Sublist.Propositional.Disjoint

  Data.Rational.Unnormalised
  Data.Rational.Unnormalised.Properties

  Data.Vec.Functional
  Data.Vec.Functional.Relation.Binary.Pointwise
  Data.Vec.Functional.Relation.Unary.All
  Data.Vec.Functional.Relation.Unary.Any

  Function.Definitions
  Function.Packages
  Function.Structures

  Foreign.Haskell.Coerce
  Foreign.Haskell.Either

  Relation.Binary.Properties.Setoid
  Relation.Binary.Reasoning.Base.Partial
  Relation.Binary.Reasoning.PartialSetoid
  ```

Relocated modules
-----------------
The following modules have been moved as part of a drive to improve
usability and consistency across the library. The old modules still exist and
therefore all existing code should still work, however they have been deprecated
and, although not anticipated any time soon, they may eventually
be removed in some future release of the library. After the next release of Agda
automated warnings will be attached to these modules to discourage their use.


Deprecated names
----------------
The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.

* In `Data.Integer.Properties`:
  ```agda
  [1+m]*n≡n+m*n ↦ suc-*
  ```

* In `Data.Nat.Properties`:
  ```agda
  +-*-suc ↦ *-suc

  ```

* In `Relation.Binary.Properties.Poset`:
  ```agda
  invIsPartialOrder  ↦ ≥-isPartialOrder
  invPoset           ↦ ≥-poset
  strictPartialOrder ↦ <-strictPartialOrder
  ```

* In `Relation.Binary.Properties.DecTotalOrder`:
  ```agda
  strictTotalOrder ↦ <-strictTotalOrder
  ```

* In `Relation.Nullary.Decidable.Core`:
  ```agda
  ⌊_⌋ ↦ isYes
  ```

Other minor additions
---------------------

* Added new bundles to `Data.Char.Properties`:
  ```agda
  <-isStrictPartialOrder-≈ : IsStrictPartialOrder _≈_ _<_
  <-isStrictTotalOrder-≈   : IsStrictTotalOrder _≈_ _<_
  <-strictPartialOrder-≈   : StrictPartialOrder _ _ _
  ```

* Added new constants to `Data.Integer.Base`:
  ```agda
  -1ℤ = -[1+ 0 ]
   0ℤ = +0
   1ℤ = +[1+ 0 ]
  ```

* Added new proof to `Data.Integer.Properties`:
  ```agda
  *-suc : m * sucℤ n ≡ m + m * n
  ```

* Added to `Data.List` the reverse-append function `_ʳ++_`
  which is `reverseAcc` with the intuitive argument order.
  Generalized the properties of `reverse` to `_ʳ++_`.

* Added new definitions to `Data.List.Relation.Unary.All`:
  ```agda
  Null = All (λ _ → ⊥)
  ```

* Generalized type of `Data.List.Relation.Binary.Sublist.Heterogeneous.toAny` to
  `Sublist R (a ∷ as) bs → Any (R a) bs`.

* Added new relations to `Data.List.Relation.Binary.Sublist.Heterogeneous`:
  ```agda
  Disjoint (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs)
  DisjointUnion (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) (τ : xys ⊆ zs)
  ```
  Some of their properties have been added to
  `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`.

* Added new relations to `Data.List.Relation.Binary.Sublist.Setoid`:
  ```agda
  xs ⊇ ys = ys ⊆ xs
  xs ⊈ ys = ¬ (xs ⊆ ys)
  xs ⊉ ys = ¬ (xs ⊇ ys)
  ```

* Added new definitions to `Data.List.Relation.Binary.Sublist.Setoid`:
  ```agda
  UpperBound (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs)
  ⊆-disjoint-union : Disjoint τ σ → UpperBound τ σ
  ```

* Added new proofs to `Data.List.Relation.Binary.Sublist.Setoid.Properties`:
  ```agda
  shrinkDisjointˡ : Disjoint τ₁ τ₂ → Disjoint (⊆-trans σ τ₁) τ₂
  shrinkDisjointʳ : Disjoint τ₁ τ₂ → Disjoint τ₁ (⊆-trans σ τ₂)
  ```

* Added new definitions to `Data.List.Relation.Binary.Sublist.Propositional`:
  ```agda
  separateˡ : (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → Separation τ₁ τ₂
  ```

* Added new proofs to `Data.List.Relation.Binary.Sublist.Propositional.Properties`:
  ```agda
  ⊆-trans-idˡ      : ⊆-trans ⊆-refl τ ≡ τ
  ⊆-trans-idʳ      : ⊆-trans τ ⊆-refl ≡ τ
  ⊆-trans-assoc    : ⊆-trans τ₁ (⊆-trans τ₂ τ₃) ≡ ⊆-trans (⊆-trans τ₁ τ₂) τ₃
  All-resp-⊆       : (All P) Respects _⊇_
  Any-resp-⊆       : (Any P) Respects _⊆_
  All-resp-⊆-refl  : All-resp-⊆ ⊆-refl ≗ id
  All-resp-⊆-trans : All-resp-⊆ (⊆-trans τ τ′) ≗ All-resp-⊆ τ ∘ All-resp-⊆ τ′
  Any-resp-⊆-refl  : Any-resp-⊆ ⊆-refl ≗ id
  Any-resp-⊆-trans : Any-resp-⊆ (⊆-trans τ τ′) ≗ Any-resp-⊆ τ′ ∘ Any-resp-⊆ τ
  lookup-injective : lookup τ i ≡ lookup τ j → i ≡ j
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  0≢1+n          : 0 ≢ suc n
  1+n≢n          : suc n ≢ n
  even≢odd       : 2 * m ≢ suc (2 * n)

  0<1+n          : 0 < suc n
  n<1+n          : n < suc n
  m<m+n          : n > 0 → m < m + n
  m<n⇒n≢0        : m < n → n ≢ 0
  m<n⇒m≤1+n      : m < n → m ≤ suc n
  m≤n⇒m<n∨m≡n    : m ≤ n → m < n ⊎ m ≡ n
  ∀[m≤n⇒m≢o]⇒o<n : (∀ {m} → m ≤ n → m ≢ o) → n < o
  ∀[m<n⇒m≢o]⇒o≤n : (∀ {m} → m < n → m ≢ o) → n ≤ o

  +-rawMagma     : RawMagma 0ℓ 0ℓ
  *-rawMagma     : RawMagma 0ℓ 0ℓ
  +-0-rawMonoid  : RawMonoid 0ℓ 0ℓ
  *-1-rawMonoid  : RawMonoid 0ℓ 0ℓ

  1+m≢m∸n        : suc m ≢ m ∸ n
  ∸-monoʳ-<      : o < n → n ≤ m → m ∸ n < m ∸ o
  ∸-cancelʳ-≤    : m ≤ o → o ∸ n ≤ o ∸ m → m ≤ n
  ∸-cancelʳ-<    : o ∸ m < o ∸ n → n < m
  ∸-cancelˡ-≡    : n ≤ m → o ≤ m → m ∸ n ≡ m ∸ o → n ≡ o
  m<n⇒0<n∸m      : m < n → 0 < n ∸ m
  m>n⇒m∸n≢0      : m > n → m ∸ n ≢ 0

  ∣-∣-identityˡ  : LeftIdentity 0 ∣_-_∣
  ∣-∣-identityʳ  : RightIdentity 0 ∣_-_∣
  ∣-∣-identity   : Identity 0 ∣_-_∣
  m≤n+∣n-m∣      : m ≤ n + ∣ n - m ∣
  m≤n+∣m-n∣      : m ≤ n + ∣ m - n ∣
  m≤∣m-n∣+n      : m ≤ ∣ m - n ∣ + n
  ```

* Added new bundles to `Data.String.Properties`:
  ```agda
  <-isStrictPartialOrder-≈ : IsStrictPartialOrder _≈_ _<_
  <-isStrictTotalOrder-≈   : IsStrictTotalOrder _≈_ _<_
  <-strictPartialOrder-≈   : StrictPartialOrder _ _ _
  ```

* Added new functions to `Data.Sum.Base`:
  ```agda
  fromInj₁ : (B → A) → A ⊎ B → A
  fromInj₂ : (A → B) → A ⊎ B → B
  ```

* Added new proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  isMagma : (_∙_ : Op₂ A) → IsMagma _≡_ _∙_
  magma   : (_∙_ : Op₂ A) → Magma a a
  ```

* Added new functions to `Data.Level`.
  ```agda
  levelOfType : ∀ {a} → Set a → Level
  levelOfTerm : ∀ {a} {A : Set a} → A → Level
  ```

* Added new definition to `Relation.Binary.Structures`:
  ```agda
  record IsPartialEquivalence {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      sym   : Symmetric _≈_
      trans : Transitive _≈_
  ```

* Added new definition to `Relation.Binary.Packages`:
  ```agda
  record PartialSetoid a ℓ : Set (suc (a ⊔ ℓ)) where
    field
      Carrier         : Set a
      _≈_             : Rel Carrier ℓ
      isPartialEquivalence : IsPartialEquivalence _≈_
  ```

* Added new proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  isDecEquivalence : Decidable _≡_ → IsDecEquivalence _≡_
  ```

* Added new proofs to `Relation.Binary.Construct.NonStrictToStrict`:
  ```agda
  <⇒≉   : x < y → x ≉ y
  ≤∧≉⇒< : x ≤ y → x ≉ y → x < y
  <⇒≱   : Antisymmetric _≈_ _≤_ → ∀ {x y} → x < y → ¬ (y ≤ x)
  ≤⇒≯   : Antisymmetric _≈_ _≤_ → ∀ {x y} → x ≤ y → ¬ (y < x)
  ≰⇒>   : Symmetric _≈_ → (_≈_ ⇒ _≤_) → Total _≤_ → ∀ {x y} → ¬ (x ≤ y) → y < x
  ≮⇒≥   : Symmetric _≈_ → Decidable _≈_ → _≈_ ⇒ _≤_ → Total _≤_ → ∀ {x y} → ¬ (x < y) → y ≤ x
  ```

* Each module in the following list now re-export relevant proofs and relations from the previous modules.
  ```
  Relation.Binary.Properties.Preorder
  Relation.Binary.Properties.Poset
  Relation.Binary.Properties.TotalOrder
  Relation.Binary.Properties.DecTotalOrder
  ```

* Added new relations and proofs to `Relation.Binary.Properties.Poset`:
  ```agda
  x ≥ y = y ≤ x
  x < y = ¬ (y ≈ x)

  <⇒≉   : x < y → x ≉ y
  ≤∧≉⇒< : x ≤ y → x ≉ y → x < y
  <⇒≱   : x < y → ¬ (y ≤ x)
  ≤⇒≯   : x ≤ y → ¬ (y < x)
  ```

* Added new proof to `Relation.Binary.Properties.TotalOrder`:
  ```agda
  ≰⇒> : ¬ (x ≤ y) → y < x
  ```

* Added new proof to `Relation.Binary.Properties.DecTotalOrder`:
  ```agda
  ≮⇒≥ : ¬ (x < y) → y ≤ x
  ```

* Added new definitions to `Relation.Nary`:
  ```agda
  apply⊤ₙ  : Π[ R ] → (vs : Product⊤ n as) → uncurry⊤ₙ n R vs
  applyₙ   : Π[ R ] → (vs : Product n as) → uncurry⊤ₙ n R (toProduct⊤ n vs)
  iapply⊤ₙ : ∀[ R ] → {vs : Product⊤ n as} → uncurry⊤ₙ n R vs
  iapplyₙ  : ∀[ R ] → {vs : Product n as} → uncurry⊤ₙ n R (toProduct⊤ n vs)

  Decidable   : as ⇉ Set r → Set (r ⊔ ⨆ n ls)
  ⌊_⌋         : Decidable R → as ⇉ Set r
  fromWitness : (R : as ⇉ Set r) (R? : Decidable R) → ∀[ ⌊ R? ⌋ ⇒ R ]
  toWitness   : (R : as ⇉ Set r) (R? : Decidable R) → ∀[ R ⇒ ⌊ R? ⌋ ]
  ```

* Added new definitions to `Relation.Unary`:
  ```agda
  ⌊_⌋ : {P : Pred A ℓ} → Decidable P → Pred A ℓ
  ```

* Re-exported the maximum function for sizes in `Size`
  ```agda
  _⊔ˢ_ : Size → Size → Size
  ```
