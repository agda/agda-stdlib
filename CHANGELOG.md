Version 1.2
===========

The library has been tested using Agda version 2.6.0.1.

Highlights
----------

* New function hierarchy.

* New (homo/mono/iso)morphism infrastructure for algebraic and relational structures.

* Fresh lists.

* First proofs of algebraic properties for operations over ℚ.

* Improved reduction behaviour for all decidability proofs.

Bug-fixes
---------

* The record `RawRing` from `Algebra` now includes an equality relation to
  make it consistent with the othor `Raw` bundles.

* In `Relation.Binary`:
  - `IsStrictTotalOrder`      now exports `isDecStrictPartialOrder`
  - `IsDecStrictPartialOrder` now re-exports the contents of `IsStrictPartialOrder`.

* Due to bug #3879 in Agda, the pattern synonyms `0F`, `1F`, ... added to
  `Data.Fin.Base` in version 1.1 resulted in unavoidable and undesirable behaviour
  when case splitting on `ℕ` when `Data.Fin` has been imported. These pattern
  synonyms have therefore been moved to the new module `Data.Fin.Patterns`.

Non-backwards compatible changes
--------------------------------

### Standardisation of record hierarchies

* The modules containing the record hierarchies for algebra, binary relations,
  and functions are currently inconsistently structured. For example:
  - in the binary relation record hierarchy the module `Relation.Binary`
  exports all parts of the hierarchy, e.g. `Reflexive`, `IsPreorder` and
  `Preorder`.
  - in contrast the algebra record hierarchy `Associative` is exported
  from `Algebra.FunctionProperties`, `IsSemigroup` from `Algebra.Structures`
  and `Semigroup` from `Algebra`.
  - the function hiearchy doesn't have a notion of `Injective` and `IsInjective`
  at all, and `Injection` is exported from `Function.Injection`.

* Consequently all hierarchies have been re-organised to follow the
  same standard pattern:
  ```agda
  X.Core         -- Contains: Rel, Op₂, Fun etc.
  X.Definitions  -- Contains: Reflexive, Associative, Injective etc.
  X.Structures   -- Contains: IsEquivalence, IsSemigroup, IsInjection etc.
  X.Bundles      -- Contains: Setoid, Semigroup, Injection etc.
  X              -- Publicly re-exports all of the above
  ```

* In `Relation.Binary` this means:
  * New module `Relation.Binary.Bundles`
  * New module `Relation.Binary.Definitions`
  * Fully backwards compatible.

* In `Algebra` this means:
  * `Algebra.FunctionProperties.Core` has been deprecated in favour of `Algebra.Core`.
  * `Algebra.FunctionProperties` has been deprecated in favour of `Algebra.Definitions`.
  * The contents of `Algebra` has been moved to `Algebra.Bundles`.
  * `Algebra` now re-exports the contents of `Algebra.Definitions` and `Algebra.Structures`,
  not just that of `Algebra.Bundles`.
  * **Compatibility:** Modules which previously imported both `Algebra` and
  `Algebra.FunctionProperties` and/or `Algebra.Structures` will need small changes.
          - If either of `FunctionProperties` or `Structures` are explicitly parameterised by an
          equality relation then import `Algebra.Bundles` instead of `Algebra`.
          - Otherwise just remove the `FunctionProperties` and `Structures` imports entirely.

### New function hierarchy

* The problems with the current function hierarchy run deeper problems than the other two:
  1. The raw functions are wrapped in the equality-preserving
     type `_⟶_` from `Function.Equality`. As the rest of the library
     rarely uses such wrapped functions, it is very difficult
     to write code that interfaces neatly between the `Function` hierarchy
     and, for example, the `Algebra` hierarchy.
  2. The hierarchy doesn't follow the same pattern as the other record
     hierarchies in the standard library, e.g. `Injective`, `IsInjection`
     and `Injection`. Coupled with point 1., anecdotally this means that
     people find it difficult to understand and use.
  3. There is no way of specifying a function has a specific property
     (e.g. injectivity) without specifying all the properties required
     of the equality relation as well. This is in contrast to the
     `Relation.Binary` and `Algebra` hierarchies where it is perfectly
     possible to specify that for example an operation is commutative
     without providing all the proofs associated with the equality relation.
  4. In many fonts the symbol `_⟶_` used for equality preserving functions
     is almost indistinguishable from the symbol for ordinary functions `_→_`,
     leading to confusion when reading code.

* To address these problems a new standardised function hierarchy has been
  created that follows the same structure found in `Relation.Binary` and `Algebra`.
  In particular:
  - The `Fun1` and `Fun2` from `Function` have been moved to `Function.Core`.
  - The rest of the old contents of `Function` have been moved to `Function.Base`.
  - Added a new module `Function.Definitions` containing definitions like
        `Injective`, `Surjective` which are parameterised by the equality relations
    over the domain and codomain.
  - Added a new module `Function.Structures` containing definitions like
    `IsInjection`, `IsSurjection`, once again parameterised the equality relations.
  - New module `Function.Bundles` containing definitions like `Injection`, `Surjection`
    which provide essentially the same top-level interface as currently exists,
    i.e. parameterised by setoids but hiding the function.
  - The module `Function` now re-exports all of the above.

* For the moment the existing modules containing the old hierarchy still exist,
  as not all existing functionality has been reimplemented using the new hierarchy.
  However it is expected that they will be deprecated at some point in the future
  when contents this transfer is complete.
  ```agda
  Function.Equivalence
  Function.Equality
  Function.Bijection
  Function.Injection
  Function.Surjection
  Function.LeftInverse
  ```

* **Compatibility:** As most of changes involve adding new modules, the only problem
  that occurs is when importing both `Function` and e.g. `Function.Injection`. In this
  case the old and new definitions of `Injection` will clash. In the short term this
  can be fixed immediately by importing `Function.Base` instead of `Function`.
  However in the longer term it is encouraged to migrate away from `Function.Injection`
  and to use the new hierarchy instead.

* Finally the propositional bundle for left inverses in `Function.Bundles` has been
  renamed in the new hierarchy from `_↞_` to `_↩_`. This is in order to make room for
  the new bundle for right inverse `_↪_`.

#### Harmonizing `List.All` and `Vec` in their role as finite maps.

* The function `updateAt` in `Data.List.Relation.Unary.All` is analogous
  to `updateAt` in `Data.Vec.Base` and hence the API for the former has
  been refactored to match the latter.

* Added a new "points-to" relation `_[_]=_` in `Data.List.Relation.Unary.All`:
  ```agda
  _[_]=_ : All P xs → x ∈ xs → P x → Set _
  ```

* In `Data.List.Relation.Unary.All.Properties` the proofs `updateAt-cong`
  and `updateAt-updates` are now formulated in terms of the new `_[_]=_`
  relation rather than the function `lookup`. The old proofs are available with
  minor variations under the names `lookup∘updateAt` and `updateAt-cong-relative`.

#### Other

* Version 1.1 in the library added irrelevance to various places in the library.
  Unfortunately this exposed the library to several irrelevance-related bugs.
  The decision has therefore been taken to roll-back these additions until
  irrelevance is more stable. In particular it has been removed from
  `_%_`, `_/_`, `_div_`, `_mod_` in `Data.Nat.DivMod` and from `fromℕ≤`, `inject≤`
  in `Data.Fin.Base`.

* The proofs `isPreorder` and `preorder` have been moved from the `Setoid`
  record to the module `Relation.Binary.Properties.Setoid`.

* The function `normalize` in `Data.Rational.Base` has been reimplemented
  in terms of a direct division of the numerator and denominator by their
  GCD. Although less elegant than the previous implementation, it's
  reduction behaviour is much easier to reason about.

Re-implementations and deprecations
-------------------------------

### `Data.Bin` → `Data.Nat.Binary`

* The current implementation of binary naturals in Agda has proven hard to work with.
  Therefore a new, simpler implementation which avoids using `List` has been added
  as `Data.Nat.Binary`.
  ```agda
  Data.Nat.Binary
  Data.Nat.Binary.Base
  Data.Nat.Binary.Induction
  Data.Nat.Binary.Properties
  ```

* The old modules still exist but have been deprecated and may be removed in
  some future release of the library.
  ```agda
  Data.Bin
  Data.Bin.Properties
  ```

### `Data.Table` → `Data.Vec.Functional`

* As well as having a non-standard name, the definition of `Table` in `Data.Table`
  has proved very difficult to work with due to the wrapping of the type in a record.
  It has therefore been renamed and reimplemented without the record wrapper as the
  `Vector` type in the new module `Data.Vec.Functional`,
  ```agda
  Data.Vec.Functional
  Data.Vec.Functional.Relation.Binary.Pointwise
  Data.Vec.Functional.Relation.Unary.All
  Data.Vec.Functional.Relation.Unary.Any
  ```

* The old modules still exist but have been deprecated and may be removed in
  some future release of the library.
  ```agda
  Data.Table
  Data.Table.Base
  Data.Table.Properties
  Data.Table.Relation.Equality
  ```

### `Data.BoundedVec(.Inefficient)` → `Data.Vec.Bounded`

* `Data.BoundedVec` and `Data.BoundedVec.Inefficient` have been deprecated
  in favour of `Data.Vec.Bounded` introduced in version 1.1.
  ```agda
  Data.Vec.Bounded
  Data.Vec.Bounded.Base
  ```

* The old modules still exist but have been deprecated and may be removed in
  some future release of the library.
  ```agda
  Data.BoundedVec
  Data.BoundedVec.Inefficient
  ```

Other major additions
---------------------

### `Reflects` idiom for decidability proofs

* A version of the `Reflects` idiom, as seen in SSReflect, has been introduced
  in `Relation.Nullary`. Some properties of it have been added in the new module
  `Relation.Nullary.Reflects`. The definition is as follows
  ```agda
  data Reflects {p} (P : Set p) : Bool → Set p where
    ofʸ : ( p :   P) → Reflects P true
    ofⁿ : (¬p : ¬ P) → Reflects P false
  ```

* `Dec` has been redefined in terms of `Reflects`.
  ```agda
  record Dec {p} (P : Set p) : Set p where
    constructor _because_
    field
      does : Bool
      proof : Reflects P does

  open Dec public
  ```
  which is entirely backwards compatible thanks to the introduction of
  the pattern synonyms in `Relation.Nullary`:
  ```agda
  pattern yes p =  true because ofʸ  p
  pattern no ¬p = false because ofⁿ ¬p
  ```

* These changes mean that decision procedures can be defined so as to provide a
  boolean result that is independent of the proof that it is the correct decision.
  For example, a proof of decidability of `_≤_` on natural numbers:
    ```agda
  _≤?_ : (m n : ℕ) → Dec (m ≤ n)
  zero  ≤? n     = yes z≤n
  suc m ≤? zero  = no λ ()
  suc m ≤? suc n with m ≤? n
  ... | yes p = yes (s≤s p)
  ... | no ¬p = no  (¬p ∘ ≤-pred)
  ```
  can now be rewritten as:
  ```agda
  _≤?_ : (m n : ℕ) → Dec (m ≤ n)
  zero  ≤? n    = yes z≤n
  suc m ≤? zero = no λ ()
  does  (suc m ≤? suc n) = does (m ≤? n)
  proof (suc m ≤? suc n) with m ≤? n
  ... | yes p = ofʸ (s≤s p)
  ... | no ¬p = ofⁿ (¬p ∘ ≤-pred)
  ```
  Notice that projecting the `does` field, returns a function whose reduction
  behaviour is identically to what we would expect of a boolean test. This has
  significant advantages for both performance and reasoning in situations where
  only a decision is required and the proof itself is not needed.

* Functions and lemmas about `Dec` have been rewritten to reflect these changes.
  - The lemmas `map′` and `map` in `Relation.Nullary.Decidable` produce their
  `does` result without any pattern matching, and `isYes` matches only on the
  `does` field, and not the `proof` field. For example this means that
  `does (map f X?)` is definitionally equal to `does X?`.
  - All of the connective lemmas like `_×-dec_` have a `does`
  field written in terms of boolean functions like `_∧_`. As well as being
  less strict than the previous definitions, this should improve readability
  when only the `does` field is involved.

* The function `⌊_⌋` still exists to be used in conjunction with `toWitness`
  and similar (e.g. in proof automation), but doesn't require the immediate
  evaluation of the `proof` part.

* The rest of the `Relation.Nullary` subtree has been updated to reflect the
  changes to `Dec`.

### Other new modules

* Properties for `Semigroup` and `CommutativeSemigroup`. Contains all the
  non-trivial 3 element permutations. Useful for equational reasoning.
  ```agda
  Algebra.Properties.Semigroup
  Algebra.Properties.CommutativeSemigroup
  ```


* A map interface for AVL trees.
  ```agda
  Data.AVL.Map
  ```

* Level polymorphic versions for the bottom and top types. Useful in
  getting rid of the need to use `Lift`.
  ```agda
  Data.Unit.Polymorphic
  Data.Unit.Polymorphic.Properties
  Data.Empty.Polymorphic
  ```


* Greatest common divisor and least common multiples for integers:
  ```agda
  Data.Integer.GCD
  Data.Integer.LCM
  ```

* Fresh lists.
  ```agda
  Data.List.Fresh
  Data.List.Fresh.Properties
  Data.List.Fresh.Relation.Unary.All
  Data.List.Fresh.Relation.Unary.All.Properties
  Data.List.Fresh.Relation.Unary.Any
  Data.List.Fresh.Relation.Unary.Any.Properties
  Data.List.Fresh.Membership
  Data.List.Fresh.Membership.Properties
  ```

* Kleene lists. Useful when needing to distinguish between empty and non-empty lists.
  ```agda
  Data.List.Kleene
  Data.List.Kleene.AsList
  Data.List.Kleene.Base
  ```


* Predicate over lists in which every neighbouring pair of elements is related.
  Useful for implementing paths in graphs.
  ```agda
  Data.List.Relation.Unary.Linked
  Data.List.Relation.Unary.Linked.Properties
  ```

* Disjoint sublists.
  ```agda
  Data.List.Relation.Binary.Sublist.Propositional.Disjoint
  ```

* Rationals whose numerator and denominator are not necessarily normalised (i.e. coprime).
  ```
  Data.Rational.Unnormalised
  Data.Rational.Unnormalised.Properties
  ```
  In this formalisation every number has an infinite number of multiple representations
  and that evaluation is inefficient as the top and the bottom will inevitably
  blow up. However they are significantly easier to reason about then the existing
  normalised implementation in `Data.Rational`. The new monomorphism infrastructure
  (see below) is used to transfer proofs from these new unnormalised rationals
  to the existing normalised implementation.

* Basic constructions for the new funciton hierarchy.
  ```agda
  Function.Construct.Identity
  Function.Construct.Composition
  ```

* New interfaces for using Haskell datatypes:
  ```
  Foreign.Haskell.Coerce
  Foreign.Haskell.Either
  ```

* Properties of setoids.
  ```agda
  Relation.Binary.Properties.Setoid
  ```

* Reasoning over partial setoids.
  ```
  Relation.Binary.Reasoning.Base.Partial
  Relation.Binary.Reasoning.PartialSetoid
  ```

* Morphisms between algebraic and relational structures. See
  `Data.Rational.Properties` for how these can be used to easily transfer
  algebraic properties from unnormalised to normalised rationals.
  ```agda
  Algebra.Morphism.Definitions
  Algebra.Morphism.Structures
  Algebra.Morphism.MagmaMonomorphism
  Algebra.Morphism.MonoidMonomorphism

  Relation.Binary.Morphism
  Relation.Binary.Morphism.Definitions
  Relation.Binary.Morphism.Structures
  Relation.Binary.Morphism.RelMonomorphism
  Relation.Binary.Morphism.OrderMonomorphism
  ```

Deprecated names
----------------

The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.

* In `Data.Fin`:
  ```agda
  fromℕ≤  ↦ fromℕ<
  fromℕ≤″ ↦ fromℕ<″
  ```

* In `Data.Fin.Properties`
  ```agda
  fromℕ≤-toℕ       ↦ fromℕ<-toℕ
  toℕ-fromℕ≤       ↦ toℕ-fromℕ<
  fromℕ≤≡fromℕ≤″   ↦ fromℕ<≡fromℕ<″
  toℕ-fromℕ≤″      ↦ toℕ-fromℕ<″
  isDecEquivalence ↦ ≡-isDecEquivalence
  preorder         ↦ ≡-preorder
  setoid           ↦ ≡-setoid
  decSetoid        ↦ ≡-decSetoid
  ```

* In `Data.Integer.Properties`:
  ```agda
  [1+m]*n≡n+m*n ↦ suc-*
  ```

* In `Data.Nat.Coprimality`:
  ```agda
  coprime-gcd ↦ coprime⇒GCD≡1
  gcd-coprime ↦ GCD≡1⇒coprime
  ```

* In `Data.Nat.Properties`:
  ```agda
  +-*-suc ↦ *-suc
  n∸m≤n   ↦ m∸n≤m
  ```
  (Note that the latter will require the arguments to be reversed)

* In `Data.Unit` the definition `_≤_` is unnecessary as it is isomorphic to `_≡_`
  and has therefore been deprecated.

* In `Data.Unit.Properties` the associated proofs have therefore been renamed as follows:
  ```agda
  ≤-total           ↦ ≡-total
  _≤?_              ↦ _≟_
  ≤-isPreorder      ↦ ≡-isPreorder
  ≤-isPartialOrder  ↦ ≡-isPartialOrder
  ≤-isTotalOrder    ↦ ≡-isTotalOrder
  ≤-isDecTotalOrder ↦ ≡-isDecTotalOrder
  ≤-poset           ↦ ≡-poset
  ≤-decTotalOrder   ↦ ≡-decTotalOrder
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

Other minor additions
---------------------

* Added new definition to `Algebra.Bundles`:
  ```agda
  record CommutativeSemigroup c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new definition to `Algebra.Structures`:
  ```agda
  record IsCommutativeSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ)
  ```

* The function `tail` in `Codata.Stream` has a new, more general type:
  ```agda
  tail : ∀ {i} {j : Size< i} → Stream A i → Stream A j
  ```

* Added new proofs to `Data.Char.Properties`:
  ```agda
  <-isStrictPartialOrder-≈ : IsStrictPartialOrder _≈_ _<_
  <-isStrictTotalOrder-≈   : IsStrictTotalOrder _≈_ _<_
  <-strictPartialOrder-≈   : StrictPartialOrder 0ℓ 0ℓ 0ℓ
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  ∀-cons-⇔ : (P zero × Π[ P ∘ suc ]) ⇔ Π[ P ]
  ∃-here   : P zero → ∃⟨ P ⟩
  ∃-there  : ∃⟨ P ∘ suc ⟩ → ∃⟨ P ⟩
  ∃-toSum  : ∃⟨ P ⟩ → P zero ⊎ ∃⟨ P ∘ suc ⟩
  ⊎⇔∃      : (P zero ⊎ ∃⟨ P ∘ suc ⟩) ⇔ ∃⟨ P ⟩
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  out⊆          : p ⊆ q → outside ∷ p ⊆      y ∷ q
  out⊆-⇔        : p ⊆ q ⇔ outside ∷ p ⊆      y ∷ q
  in⊆in         : p ⊆ q →  inside ∷ p ⊆ inside ∷ q
  in⊆in-⇔       : p ⊆ q ⇔  inside ∷ p ⊆ inside ∷ q

  ∃-Subset-zero : ∃⟨ P ⟩ → P []
  ∃-Subset-[]-⇔ : P [] ⇔ ∃⟨ P ⟩
  ∃-Subset-suc  : ∃⟨ P ⟩ → ∃⟨ P ∘ (inside ∷_) ⟩ ⊎ ∃⟨ P ∘ (outside ∷_) ⟩
  ∃-Subset-∷-⇔  : (∃⟨ P ∘ (inside ∷_) ⟩ ⊎ ∃⟨ P ∘ (outside ∷_) ⟩) ⇔ ∃⟨ P ⟩
  ```

* Added new constants to `Data.Integer.Base`:
  ```agda
  -1ℤ = -[1+ 0 ]
   0ℤ = +0
   1ℤ = +[1+ 0 ]
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  *-suc : m * sucℤ n ≡ m + m * n

  +-isCommutativeSemigroup : IsCommutativeSemigroup _+_
  *-isCommutativeSemigroup : IsCommutativeSemigroup _*_
  +-commutativeSemigroup   : CommutativeSemigroup 0ℓ 0ℓ
  *-commutativeSemigroup   : CommutativeSemigroup 0ℓ 0ℓ
  ```

* Added new function to `Data.List.Base`:
  ```agda
  _ʳ++_ = flip reverseAcc
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  filter-accept : P x → filter P? (x ∷ xs) ≡ x ∷ (filter P? xs)
  filter-reject : ¬ P x → filter P? (x ∷ xs) ≡ filter P? xs
  filter-idem   : filter P? ∘ filter P? ≗ filter P?
  filter-++     : filter P? (xs ++ ys) ≡ filter P? xs ++ filter P? ys

  ʳ++-defn   : xs ʳ++ ys ≡ reverse xs ++ ys
  ʳ++-++     : (xs ++ ys) ʳ++ zs ≡ ys ʳ++ xs ʳ++ zs
  ʳ++-ʳ++    : (xs ʳ++ ys) ʳ++ zs ≡ ys ʳ++ xs ++ zs
  length-ʳ++ : length (xs ʳ++ ys) ≡ length xs + length ys
  map-ʳ++    : map f (xs ʳ++ ys) ≡ map f xs ʳ++ map f ys
  foldr-ʳ++  : foldr f b (xs ʳ++ ys) ≡ foldl (flip f) (foldr f b ys) xs
  foldl-ʳ++  : foldl f b (xs ʳ++ ys) ≡ foldl f (foldr (flip f) b xs) ys
  ```

* Added new definitions to `Data.List.Relation.Binary.Lex.Core`:
  ```agda
  []<[]-⇔ : P ⇔ [] < []
  toSum   : (x ∷ xs) < (y ∷ ys) → (x ≺ y ⊎ (x ≈ y × xs < ys))
  ∷<∷-⇔   : (x ≺ y ⊎ (x ≈ y × xs < ys)) ⇔ (x ∷ xs) < (y ∷ ys)
  ```

* The proof `toAny` in `Data.List.Relation.Binary.Sublist.Heterogeneous` has a new more general type:
  ```agda
  toAny : Sublist R (a ∷ as) bs → Any (R a) bs
  ```

* Added new relations to `Data.List.Relation.Binary.Sublist.Heterogeneous`:
  ```agda
  Disjoint (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs)
  DisjointUnion (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) (τ : xys ⊆ zs)
  ```

* Added new relations and definitions to `Data.List.Relation.Binary.Sublist.Setoid`:
  ```agda
  xs ⊇ ys = ys ⊆ xs
  xs ⊈ ys = ¬ (xs ⊆ ys)
  xs ⊉ ys = ¬ (xs ⊇ ys)

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

* Added new definition to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  uncons : Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y × Pointwise _∼_ xs ys
  ```

* Added new definitions to `Data.List.Relation.Unary.All`:
  ```agda
  Null = All (λ _ → ⊥)
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  Null⇒null     : Null xs → T (null xs)
  null⇒Null     : T (null xs) → Null xs

  []=-injective : pxs [ i ]= px → pxs [ i ]= qx → px ≡ qx
  []=lookup     : (i : x ∈ xs) → pxs [ i ]= lookup pxs i
  []=⇒lookup    : pxs [ i ]= px → lookup pxs i ≡ px
  lookup⇒[]=    : lookup pxs i ≡ px → pxs [ i ]= px

  updateAt-minimal          : i ≢∈ j → pxs [ i ]= px → updateAt j f pxs [ i ]= px
  updateAt-id-relative      : f (lookup pxs i) ≡ lookup pxs i → updateAt i f pxs ≡ pxs
  updateAt-compose-relative : f (g (lookup pxs i)) ≡ h (lookup pxs i) → updateAt i f (updateAt i g pxs) ≡ updateAt i h pxs
  updateAt-commutes         : i ≢∈ j → updateAt i f ∘ updateAt j g ≗ updateAt j g ∘ updateAt i f
  ```

* The proof `All-swap` in `Data.List.Relation.Unary.All.Properties` has been generalised to work over `_~_ : REL A B ℓ` instead of just `_~_ : REL (List A) B ℓ`.

* Added new definition to `Data.List.Relation.Unary.AllPairs`:
  ```agda
  uncons : AllPairs R (x ∷ xs) → All (R x) xs × AllPairs R xs
  ```

* Added new proofs to `Data.Nat.Coprimality`:
  ```agda
  coprime⇒gcd≡1 : Coprime m n → gcd m n ≡ 1
  gcd≡1⇒coprime : gcd m n ≡ 1 → Coprime m n
  coprime-/gcd  : Coprime (m / gcd m n) (n / gcd m n)
  ```

* Added new proof to `Data.Nat.Divisibility`:
  ```agda
  >⇒∤ : m > suc n → m ∤ suc n
  ```

* Added new proofs to `Data.Nat.DivMod`:
  ```agda
  /-congˡ   : m ≡ n → m / o ≡ n / o
  /-congʳ   : n ≡ o → m / n ≡ m / o
  /-mono-≤  : m ≤ n → o ≥ p → m / o ≤ n / p
  /-monoˡ-≤ : m ≤ n → m / o ≤ n / o
  /-monoʳ-≤ : n ≥ o → m / n ≤ m / o
  m≥n⇒m/n>0 : m ≥ n → m / n > 0
  ```

* Added new proofs to `Data.Nat.GCD`:
  ```agda
  gcd[m,n]≡0⇒m≡0 : gcd m n ≡ 0 → m ≡ 0
  gcd[m,n]≡0⇒n≡0 : gcd m n ≡ 0 → n ≡ 0
  gcd[m,n]≤n     : gcd m (suc n) ≤ suc n
  n/gcd[m,n]≢0   : {n≢0 gcd≢0} → n / gcd m n ≢ 0
  GCD-*          : GCD (m * suc c) (n * suc c) (d * suc c) → GCD m n d
  GCD-/          : c ∣ m → c ∣ n → c ∣ d → GCD m n d → GCD (m / c) (n / c) (d / c)
  GCD-/gcd       : GCD (m / gcd m n) (n / gcd m n) 1
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

  *-cancelˡ-≤    : suc o * m ≤ suc o * n → m ≤ n

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

  +-isCommutativeSemigroup : IsCommutativeSemigroup _+_
  +-commutativeSemigroup   : CommutativeSemigroup 0ℓ 0ℓ
  ```

* Added new bundles to `Data.String.Properties`:
  ```agda
  <-isStrictPartialOrder-≈ : IsStrictPartialOrder _≈_ _<_
  <-isStrictTotalOrder-≈   : IsStrictTotalOrder _≈_ _<_
  <-strictPartialOrder-≈   : StrictPartialOrder 0ℓ 0ℓ 0ℓ
  ```

* Added new functions to `Data.Rational.Base`:
  ```agda
  mkℚ+   : ∀ n d → .{d≢0 : d ≢0} → .(Coprime n d) → ℚ
  toℚᵘ   : ℚ → ℚᵘ
  fromℚᵘ : ℚᵘ → ℚ
  ```

* Added new proofs to `Data.Rational.Properties`:
  ```agda
  mkℚ-cong          : n₁ ≡ n₂ → d₁ ≡ d₂ → mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
  mkℚ+-cong         : n₁ ≡ n₂ → d₁ ≡ d₂ → mkℚ+ n₁ d₁ c₁ ≡ mkℚ+ n₂ d₂ c₂
  normalize-coprime : .(c : Coprime n (suc d-1)) → normalize n (suc d-1) ≡ mkℚ (+ n) d-1 c

  ↥-mkℚ+            : ↥ (mkℚ+ n d c)                      ≡ + n
  ↧-mkℚ+            : ↧ (mkℚ+ n d c)                      ≡ + d
  ↥-neg             : ↥ (- p)                             ≡ - (↥ p)
  ↧-neg             : ↧ (- p)                             ≡ ↧ p
  ↥-normalise       : ↥ (normalize i n) * gcd (+ i) (+ n) ≡ + i
  ↧-normalise       : ↧ (normalize i n) * gcd (+ i) (+ n) ≡ + n
  ↥-/               : ↥ (i / n)         * gcd i (+ n)     ≡ i
  ↧-/               : ↧ (i / n)         * gcd i (+ n)     ≡ + n
  ↥-+               : ↥ (p + q)         * gcd (...) (...) ≡ ↥ p * ↧ q ℤ.+ ↥ q * ↧ p
  ↧-+               : ↧ (p + q)         * gcd (...) (...) ≡ ↧ p * ↧ q

  ↥p/↧p≡p           : ↥ p / ↧ₙ p ≡ p
  0/n≡0             : 0ℤ / n ≡ 0ℚ

  toℚᵘ-cong         : toℚᵘ Preserves _≡_ ⟶ _≃ᵘ_
  toℚᵘ-injective    : Injective _≡_ _≃ᵘ_ toℚᵘ
  fromℚᵘ-toℚᵘ       : fromℚᵘ (toℚᵘ p) ≡ p

  toℚᵘ-homo-+                : Homomorphic₂ toℚᵘ _+_ ℚᵘ._+_
  toℚᵘ-+-isRawMagmaMorphism  : IsRawMagmaMorphism +-rawMagma ℚᵘ.+-rawMagma toℚᵘ
  toℚᵘ-+-isRawMonoidMorphism : IsRawMonoidMorphism +-rawMonoid ℚᵘ.+-rawMonoid toℚᵘ

  +-assoc                    : Associative _+_
  +-comm                     : Commutative _+_
  +-identityˡ                : LeftIdentity 0ℚ _+_
  +-identityʳ                : RightIdentity 0ℚ _+_
  +-identity                 : Identity 0ℚ _+_
  +-isMagma                  : IsMagma _+_
  +-isSemigroup              : IsSemigroup _+_
  +-0-isMonoid               : IsMonoid _+_ 0ℚ
  +-0-isCommutativeMonoid    : IsCommutativeMonoid _+_ 0ℚ
  +-rawMagma                 : RawMagma 0ℓ 0ℓ
  +-rawMonoid                : RawMonoid 0ℓ 0ℓ
  +-magma                    : Magma 0ℓ 0ℓ
  +-semigroup                : Semigroup 0ℓ 0ℓ
  +-0-monoid                 : Monoid 0ℓ 0ℓ
  +-0-commutativeMonoid      : CommutativeMonoid 0ℓ 0ℓ
  ```

* Added new functions to `Data.Sum.Base`:
  ```agda
  fromInj₁ : (B → A) → A ⊎ B → A
  fromInj₂ : (A → B) → A ⊎ B → B
  ```

* Added new definition to `Data.These.Properties`:
  ```agda
  these-injective : these x a ≡ these y b → x ≡ y × a ≡ b
  ```

* Added new definition to `Data.Vec.Relation.Binary.Pointwise.Inductive`:
  ```agda
  uncons : Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y × Pointwise _∼_ xs ys
  ```

* Added new definition to `Data.Vec.Relation.Unary.All`:
  ```agda
  uncons : All P (x ∷ xs) → P x × All P xs
  ```

* Added new functions to `Level`.
  ```agda
  levelOfType : ∀ {a} → Set a → Level
  levelOfTerm : ∀ {a} {A : Set a} → A → Level
  ```

* Added new proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  isMagma : (_∙_ : Op₂ A) → IsMagma _≡_ _∙_
  magma   : (_∙_ : Op₂ A) → Magma a a
  ```

* Added new definition to `Relation.Binary.Structures`:
  ```agda
  record IsPartialEquivalence (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ)
  ```

* Added new definition to `Relation.Binary.Bundles`:
  ```agda
  record PartialSetoid a ℓ : Set (suc (a ⊔ ℓ))
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

* Each of the following modules now re-export relevant proofs and relations from the previous modules in the list.
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

* Added new proof to `Relation.Binary.PropositionalEquality`:
  ```agda
  isDecEquivalence : Decidable _≡_ → IsDecEquivalence _≡_
  ```

* Added new definitions to `Relation.Nary`:
  ```agda
  apply⊤ₙ     : Π[ R ] → (vs : Product⊤ n as) → uncurry⊤ₙ n R vs
  applyₙ      : Π[ R ] → (vs : Product n as)  → uncurry⊤ₙ n R (toProduct⊤ n vs)
  iapply⊤ₙ    : ∀[ R ] → {vs : Product⊤ n as} → uncurry⊤ₙ n R vs
  iapplyₙ     : ∀[ R ] → {vs : Product n as}  → uncurry⊤ₙ n R (toProduct⊤ n vs)

  Decidable   : as ⇉ Set r → Set (r ⊔ ⨆ n ls)
  ⌊_⌋         : Decidable R → as ⇉ Set r
  fromWitness : (R : as ⇉ Set r) (R? : Decidable R) → ∀[ ⌊ R? ⌋ ⇒ R ]
  toWitness   : (R : as ⇉ Set r) (R? : Decidable R) → ∀[ R ⇒ ⌊ R? ⌋ ]
  ```

* Added new definitions to `Relation.Unary`:
  ```agda
  ⌊_⌋ : {P : Pred A ℓ} → Decidable P → Pred A ℓ
  ```

* Added new definitions to `Relation.Binary.Construct.Closure.Reflexive.Properties`:
  ```agda
  fromSum :  a ≡ b ⊎ a ~ b  → Refl _~_ a b
  toSum   :  Refl _~_ a b   → a ≡ b ⊎ a ~ b
  ⊎⇔Refl  : (a ≡ b ⊎ a ~ b) ⇔ Refl _~_ a b
  ```

* Added new definitions to `Relation.Nullary.Decidable`:
  ```agda
  dec-true  : (p? : Dec P) →   P → does p? ≡ true
  dec-false : (p? : Dec P) → ¬ P → does p? ≡ false
  ```

* Added new definition to `Relation.Nullary.Implication`:
  ```agda
  _→-reflects_ : Reflects P bp → Reflects Q bq → Reflects (P → Q) (not bp ∨ bq)
  ```

* Added new definition to `Relation.Nullary.Negation`:
  ```agda
  ¬-reflects : Reflects P b → Reflects (¬ P) (not b)
  ```

* Added new definition to `Relation.Nullary.Product`:
  ```agda
  _×-reflects_ : Reflects P bp → Reflects Q bq → Reflects (P × Q) (bp ∧ bq)
  ```

* Added new definition to `Relation.Nullary.Sum`:
  ```agda
  _⊎-reflects_ : Reflects P bp → Reflects Q bq → Reflects (P ⊎ Q) (bp ∨ bq)
  ```

* The module `Size` now re-exports the built-in function:
  ```agda
  _⊔ˢ_ : Size → Size → Size
  ```
