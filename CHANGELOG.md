Version 1.1
===========

The library has been tested using Agda version 2.6.0.1.

Changes since 1.0.1:

Highlights
----------

* Large increases in performance for `Nat`, `Integer` and `Rational` datatypes,
  particularly in compiled code.

* Generic n-ary programming (`projₙ`, `congₙ`, `substₙ` etc.)

* General argmin/argmax/min/max over `List`.

* New `Trie` datatype

Bug-fixes
---------

#### `_<_` in `Data.Integer`

* The definition of `_<_` in `Data.Integer` often resulted in unsolved metas
  when Agda had to infer the first argument. This was because it was
  previously implemented in terms of `suc` -> `_+_` -> `_⊖_`.

* To fix this problem the implementation has therefore changed to:
  ```agda
  data _<_ : ℤ → ℤ → Set where
    -<+ : ∀ {m n} → -[1+ m ] < + n
    -<- : ∀ {m n} → (n<m : n ℕ.< m) → -[1+ m ] < -[1+ n ]
    +<+ : ∀ {m n} → (m<n : m ℕ.< n) → + m < + n
  ```
  which should allow many implicit parameters which previously had
  to be given explicitly to be removed.

* All proofs involving `_<_` have been updated correspondingly

* For backwards compatibility the old relations still exist as primed versions
  `_<′_` as do all the old proofs, e.g. `+-monoˡ-<` has become `+-monoˡ-<′`,
  but these have all been deprecated and may be removed in some future version.

#### Fixed wrong queries being exported by `Data.Rational`

* `Data.Rational` previously accidently exported queries from `Data.Nat.Base`
  instead of `Data.Rational.Base`. This has now been fixed.

#### Fixed inaccurate name in `Data.Nat.Properties`

* The proof `m+n∸m≡n` in `Data.Nat.Properties` was incorrectly named as
  it proved `m + (n ∸ m) ≡ n` rather than `m + n ∸ m ≡ n`. It has
  therefore been renamed `m+[n∸m]≡n` and the old name now refers to a new
  proof of the correct type.

#### Fixed operator precedents in `Ring`-like structures

* The infix precedence of `_-_` in the record `Group` from `Algebra.Structures`
  was previously set such that when it was inherited by the records `Ring`,
  `CommutativeRing` etc. it had the same predence as `_*_` rather than `_+_`.
  This lead to `x - x * x` being ambigous instead of being parsed as `x - (x * x)`.
  To fix this, the precedence of `_-_` has been reduced from 7 to 6.

#### Fixed operator precedents in `Reasoning` modules

* The infix precedence of the generic order reasoning combinators (`_∼⟨_⟩_`,
  `_≈⟨_⟩_`, etc.) in `Relation.Binary.Reasoning.Base.Double/Triple` were
  accidentally lowered when implementing new style reasoning in `v1.0`.
  This lead to inconsistencies in modules that add custom combinators (e.g.
  `StarReasoning` from `Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties`)
  using the original fixity.  The old fixity has now been restored.

Other non-backwards compatible changes
--------------------------------------

#### Improved performance of arithmetic decision procedures & operations

* The functions `_≤?_` and `<-cmp` in `Data.Nat.Properties` have been
  reimplemented uses only built-in primitives. Consequently this should
  result in a significant performance increase when these functions are
  compiled or when the generated proof is ignored.

* The function `show` in `Data.Nat.Show` has been reimplemented and,
  when compiled, now runs in time `O(log₁₀(n))` rather than `O(n)`.

* The functions `gcd` and `lcm` in `Data.Nat.GCD` and `Data.Nat.LCM`
  have been reimplemented via the built-ins `_/_` and `mod` so that
  they run much faster when compiled and normalised. Their types have also
  been changed to `ℕ → ℕ → ℕ` instead of `(m n : ℕ) → ∃ λ d → GCD/LCM m n d`.
  The old functions still exist and have been renamed `mkGCD`/`mkLCM`.
  The alternative `gcd′` in `Data.Nat.Coprimality` has been deprecated.

* As a consequence of the above, the performance of all decidability procedures
  in `Data.Integer` and `Data.Rational` should also have improved. Normalisation
  speed in `Data.Rational` should receive a significant boost.

#### Better reduction behaviour for conversion functions in `Data.Fin`

* The implementation of the functions `fromℕ≤` and `inject≤` in `Data.Fin.Base`
  has been changed so as to avoid pattern matching on the `m ≤ n` proof. This
  makes them significantly easier to use, as often it is inconvenient to
  pattern match on the `m ≤ n` proof directly.

#### Consistent field names in `IsDistributiveLattice`

* In order to match the conventions found elsewhere in the library, the module
  `IsDistributiveLattice` in `Algebra.Structures` has had its field renamed
  from `∨-∧-distribʳ` to `∨-distribʳ-∧` . To maximise backwards compatability,
  the record still exports `∨-∧-distribʳ` but the name is deprecated.

#### Making categorical traversal functions easier to use

* Previously the functions `sequenceA`, `mapA`, `forA`, `sequenceM`,
  `mapM` and `forM` in the `Data.X.Categorical` modules required the
  `Applicative`/`Monad` to be passed each time they were used. To avoid this
  they have now been placed in parameterised modules named `TraversableA` and
  `TraversableM`. To recover the old behaviour simply write `open TraversableA`.
  However you may now, for example, avoid passing the applicative every time
  by writing `open TraversableA app`. The change has occured in the following
  modules:
  ```adga
  Data.Maybe.Categorical
  Data.List.Categorical
  Data.List.NonEmpty.Categorical
  Data.Product.Categorical.(Left/Right)
  Data.Sum.Categorical.(Left/Right)
  Data.Vec.Categorical
  ```

#### Moved `#_` within `Data.Fin`.

* The function `#_` has been moved from `Data.Fin.Base` to `Data.Fin`
  to break dependency cycles following the introduction of the module
  `Data.Product.N-ary.Heterogeneous`.

New modules
-----------
The following new modules have been added to the library:

* An algebraic construction for choosing between `x` and `y` based on a
  comparison of `f x` and `f y`.
  ```
  Algebra.Constructs.LiftedChoice
  ```

* The reader monad.
  ```
  Category.Monad.Reader
  ```

* Non-empty AVL trees.
  ```
  Data.AVL.NonEmpty
  Data.AVL.NonEmpty.Propositional
  ```

* Implementations of `argmin`, `argmax`, `min` and `max` for lists over
  arbitrary `TotalOrder`s.
  ```
  Data.List.Extrema
  Data.List.Extrema.Nat
  Data.List.Extrema.Core
  ```

* Additional properties of membership with the `--with-k` option enabled.
  ```
  Data.List.Membership.Propositional.Properties.WithK
  ```

* A relation for lists that share no elements in common.
  ```
  Data.List.Relation.Binary.Disjoint.Propositional
  Data.List.Relation.Binary.Disjoint.Setoid
  Data.List.Relation.Binary.Disjoint.Setoid.Properties
  ```

* A relation for lists that are permutations of one another with respect to a `Setoid`.
  ```
  Data.List.Relation.Binary.Permutation.Homogeneous
  Data.List.Relation.Binary.Permutation.Setoid
  Data.List.Relation.Binary.Permutation.Setoid.Properties
  ```

* A predicate for lists in which every pair of elements is related.
  ```
  Data.List.Relation.Unary.AllPairs
  Data.List.Relation.Unary.AllPairs.Properties
  ```

* A predicate for lists in which every element is unique.
  ```
  Data.List.Relation.Unary.Unique.Propositional
  Data.List.Relation.Unary.Unique.Propositional.Properties
  Data.List.Relation.Unary.Unique.Setoid
  Data.List.Relation.Unary.Unique.Setoid.Properties
  ```

* New generic n-ary programming primitives.
  ```
  Data.Product.Nary.NonDependent
  Function.Nary.NonDependent
  Function.Nary.NonDependent.Base
  Relation.Nary
  ```

* Properties of the unit type.
  ```
  Data.Unit.Properties
  ```

* Implementation of tries.
  ```
  Data.Trie
  Data.Trie.NonEmpty
  ```

* New implementation of vectors of no more than length `n`.
  ```
  Data.Vec.Bounded.Base
  Data.Vec.Bounded
  ```

* Data types that are compiled to their Haskell equivalents.
  ```
  Foreign.Haskell.Pair
  Foreign.Haskell.Maybe
  ```

* Properties of closures over binary relations.
  ```
  Relation.Binary.Construct.Closure.Reflexive.Properties
  Relation.Binary.Construct.Closure.Reflexive.Properties.WithK
  Relation.Binary.Construct.Closure.Equivalence.Properties
  ```

* A formalisation of rewriting theory/transition systems.
  ```
  Relation.Binary.Rewriting
  ```

* Utilities for formatting and printing strings.
  ```
  Text.Format
  Text.Printf
  ```

Relocated modules
-----------------
The following modules have been moved as part of a drive to improve
usability and consistency across the library. The old modules still exist and
therefore all existing code should still work, however they have been deprecated
and, although not anticipated any time soon, they may eventually
be removed in some future release of the library. After the next release of Agda
automated warnings will be attached to these modules to discourage their use.

* The induction machinery for `Nat` was commonly held to be one of the hardest
  modules to find in the library. Therefore the module `Induction.Nat` has been
  split into two new modules: `Data.Nat.Induction` and `Data.Fin.Induction`.
  This should improve findability and better matches the design of the rest of
  the library. The new modules also publicly re-export `Acc` and `acc`, meaning
  that users no longer need to import `Data.Induction.WellFounded` as well.

* The module `Record` has been moved to `Data.Record`.

* The module `Universe` has been split into `Data.Universe` and
  `Data.Universe.Indexed`. In the latter `Indexed-universe` has been
  renamed to `IndexedUniverse` to better follow the library conventions.

* The `Data.Product.N-ary` modules and their content have been moved to
  `Data.Vec.Recursive` to make place for properly heterogeneous n-ary products
  in `Data.Product.Nary`.

* The modules `Data.List.Relation.Binary.Permutation.Inductive(.Properties)`
  have been renamed `Data.List.Relation.Binary.Permutation.Propositional(.Properties)`
  to match the rest of the library.

Deprecated names
----------------
The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.

* In `Algebra.Properties.BooleanAlgebra`:
  ```agda
  ¬⊥=⊤              ↦ ⊥≉⊤
  ¬⊤=⊥              ↦ ⊤≉⊥
  ⊕-¬-distribˡ      ↦ ¬-distribˡ-⊕
  ⊕-¬-distribʳ      ↦ ¬-distribʳ-⊕
  isCommutativeRing ↦ ⊕-∧-isCommutativeRing
  commutativeRing   ↦ ⊕-∧-commutativeRing
  ```

* In `Algebra.Properties.DistributiveLattice`:
  ```agda
  ∨-∧-distribˡ ↦ ∨-distribˡ-∧
  ∨-∧-distrib  ↦ ∨-distrib-∧
  ∧-∨-distribˡ ↦ ∧-distribˡ-∨
  ∧-∨-distribʳ ↦ ∧-distribʳ-∨
  ∧-∨-distrib  ↦ ∧-distrib-∨
  ```

* In `Algebra.Properties.Group`:
  ```agda
  left-identity-unique  ↦ identityˡ-unique
  right-identity-unique ↦ identityʳ-unique
  left-inverse-unique   ↦ inverseˡ-unique
  right-inverse-unique  ↦ inverseʳ-unique
  ```

* In `Algebra.Properties.Lattice`:
  ```agda
  ∧-idempotent            ↦ ∧-idem
  ∨-idempotent            ↦ ∨-idem
  isOrderTheoreticLattice ↦ ∨-∧-isOrderTheoreticLattice
  orderTheoreticLattice   ↦ ∨-∧-orderTheoreticLattice
  ```

* In `Algebra.Properties.Ring`:
  ```agda
  -‿*-distribˡ ↦ -‿distribˡ-*
  -‿*-distribʳ ↦ -‿distribʳ-*
  ```
  NOTE: the direction of the equality is flipped for the new names and
  so you will need to replace `-‿*-distribˡ ...` with `sym (-‿distribˡ-* ...)`.

* In `Algebra.Properties.Semilattice`:
  ```agda
  isOrderTheoreticMeetSemilattice ↦ ∧-isOrderTheoreticMeetSemilattice
  isOrderTheoreticJoinSemilattice ↦ ∧-isOrderTheoreticJoinSemilattice
  orderTheoreticMeetSemilattice   ↦ ∧-orderTheoreticMeetSemilattice
  orderTheoreticJoinSemilattice   ↦ ∧-orderTheoreticJoinSemilattice
  ```

* In `Relation.Binary.Core`:
  ```agda
  Conn  ↦  Connex
  ```

* In `Codata.Stream.Properties`:
  ```agda
  repeat-ap-identity  ↦  ap-repeatˡ
  ap-repeat-identity  ↦  ap-repeatʳ
  ap-repeat-commute   ↦  ap-repeat
  map-repeat-commute  ↦  map-repeat
  ```

* In `Data.Bool` (with the new name in `Data.Bool.Properties`):
  ```agda
  decSetoid   ↦  ≡-decSetoid
  ```

* In `Data.Fin.Properties` the operator `_+′_` has been deprecated entirely
  as it was difficult to use, had unpredictable reduction behaviour and
  was very rarely used.

* In `Data.Nat.Divisibility`:
  ```agda
  poset   ↦  ∣-poset
  *-cong  ↦  *-monoʳ-∣
  /-cong  ↦  *-cancelˡ-∣
  ```

* In `Data.Nat.DivMod`:
  ```agda
  a≡a%n+[a/n]*n  ↦  m≡m%n+[m/n]*n
  a%1≡0          ↦  n%1≡0
  a%n%n≡a%n      ↦  m%n%n≡m%n
  [a+n]%n≡a%n    ↦  [m+n]%n≡m%n
  [a+kn]%n≡a%n   ↦  [m+kn]%n≡m%n
  kn%n≡0         ↦  m*n%n≡0
  a%n<n          ↦  m%n<n
  ```

* In `Data.Nat.Properties`:
  ```agda
  m≢0⇒suc[pred[m]]≡m  ↦  suc[pred[n]]≡n

  i+1+j≢i             ↦  m+1+n≢m
  i+j≡0⇒i≡0           ↦  m+n≡0⇒m≡0
  i+j≡0⇒j≡0           ↦  m+n≡0⇒n≡0
  i+1+j≰i             ↦  m+1+n≰m
  i*j≡0⇒i≡0∨j≡0       ↦  m*n≡0⇒m≡0∨n≡0
  i*j≡1⇒i≡1           ↦  m*n≡1⇒m≡1
  i*j≡1⇒j≡1           ↦  m*n≡1⇒n≡1
  i^j≡0⇒i≡0           ↦  m^n≡0⇒m≡0
  i^j≡1⇒j≡0∨i≡1       ↦  m^n≡1⇒n≡0∨m≡1
  [i+j]∸[i+k]≡j∸k     ↦  [m+n]∸[m+o]≡n∸o

  n≡m⇒∣n-m∣≡0         ↦  m≡n⇒∣m-n∣≡0
  ∣n-m∣≡0⇒n≡m         ↦  ∣m-n∣≡0⇒m≡n
  ∣n-m∣≡n∸m⇒m≤n       ↦  ∣m-n∣≡m∸n⇒n≤m
  ∣n-n+m∣≡m           ↦  ∣m-m+n∣≡n
  ∣n+m-n+o∣≡∣m-o|     ↦  ∣m+n-m+o∣≡∣n-o|
  n∸m≤∣n-m∣           ↦  m∸n≤∣m-n∣
  ∣n-m∣≤n⊔m           ↦  ∣m-n∣≤m⊔n

  n≤m+n               ↦  m≤n+m
  n≤m+n∸m             ↦  m≤n+m∸n
  ∣n-m∣≡[n∸m]∨[m∸n]   ↦  ∣m-n∣≡[m∸n]∨[n∸m]
  ```
  Note that in the case of the last three proofs, the order of the
  arguments will need to be swapped.

* In `Data.Unit` (with the new names in `Data.Unit.Properties`):
  ```agda
  setoid        ↦ ≡-setoid
  decSetoid     ↦ ≡-decSetoid
  total         ↦ ≤-total
  poset         ↦ ≤-poset
  decTotalOrder ↦ ≤-decTotalOrder
  ```

* In `Data.Unit` the proof `preorder` has also been deprecated, but
  as it erroneously proved that `_≡_` rather than `_≤_` is a preorder
  with respect to `_≡_` it does not have a new name in `Data.Unit.Properties`.

* In `Foreign.Haskell` the terms `Unit` and `unit` have been deprecated in
  favour of `⊤` and `tt` from `Data.Unit`, as it turns out that the latter
  have been automatically mapped to the Haskell equivalent for quite some time.

* In `Reflection`:
  ```agda
  returnTC ↦ return
  ```

* Renamed functions in `Data.Char.Base`:
  ```agda
  fromNat         ↦ fromℕ
  toNat           ↦ toℕ
  ```

* In `Data.(Char/String).Properties`:
  ```agda
  setoid           ↦ ≡-setoid
  decSetoid        ↦ ≡-decSetoid
  strictTotalOrder ↦ <-strictTotalOrder-≈
  toNat-injective  ↦ toℕ-injective
  ```

* In `Data.Vec.Properties`:
  ```agda
  lookup-++-inject+ ↦ lookup-++ˡ
  lookup-++-+′      ↦ lookup-++ʳ
  ```

* In `Data.Product.Relation.Binary.Pointwise.NonDependent` (with the
  new name in `Data.Product.Properties`).:
  ```agda
  ≡?×≡?⇒≡? ↦ ≡-dec
  ```

Other minor additions
---------------------

* Added new proofs in Data.Fin.Substitution.Lemmas:
  ```agda
  weaken-↑    : weaken t / (ρ ↑)     ≡ weaken (t / ρ)
  weaken-∷    : weaken t₁ / (t₂ ∷ ρ) ≡ t₁ / ρ
  weaken-sub  : weaken t₁ / sub t₂   ≡ t₁
  wk-⊙-∷      : wk ⊙ (t ∷ ρ)         ≡ ρ
  ```

* Added new record to `Algebra`:
  ```agda
  SelectiveMagma c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new record to `Algebra.Structure`:
  ```agda
  IsSelectiveMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  ```

* Added new proof to `Algebra.Properties.AbelianGroup`:
  ```agda
  xyx⁻¹≈y : x ∙ y ∙ x ⁻¹ ≈ y
  ```

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ε⁻¹≈ε     : ε ⁻¹ ≈ ε
  ∙-cancelˡ : LeftCancellative _∙_
  ∙-cancelʳ : RightCancellative _∙_
  ∙-cancel  : Cancellative _∙_
  ```

* Added new proofs to `Algebra.Properties.Lattice`:
  ```agda
  ∧-isMagma     : IsMagma _∧_
  ∧-isSemigroup : IsSemigroup _∧_
  ∧-isBand      : IsBand _∧_
  ∨-isMagma     : IsMagma _∨_
  ∨-isSemigroup : IsSemigroup _∨_
  ∨-isBand      : IsBand _∨_
  ```

* Added new proofs to `Codata.Stream.Properties`:
  ```agda
  splitAt-repeat-identity : splitAt n (repeat a) ≡ (Vec.replicate a , repeat a)
  replicate-repeat        : i ⊢ List.replicate n a ++ repeat a ≈ repeat a
  cycle-replicate         : i ⊢ cycle (List⁺.replicate n n≢0 a) ≈ repeat a
  map-cycle               : i ⊢ map f (cycle as) ≈ cycle (List⁺.map f as)
  map-⁺++                 : i ⊢ map f (as ⁺++ xs) ≈ List⁺.map f as ⁺++ Thunk.map (map f) xs
  map-++                  : i ⊢ map f (as ++ xs) ≈ List.map f as ++ map f xs
  ```

* Added new function to `Data.AVL.Indexed`:
  ```agda
  toList : Tree V l u h → List (K& V)
  ```

* Added new relations to `Data.Bool`:
  ```agda
  _≤_ : Rel Bool 0ℓ
  _<_ : Rel Bool 0ℓ
  ```

* Added new proofs to `Data.Bool.Properties`:
  ```agda
  ≡-setoid               : Setoid 0ℓ 0ℓ

  ≤-reflexive            : _≡_ ⇒ _≤_
  ≤-refl                 : Reflexive _≤_
  ≤-antisym              : Antisymmetric _≡_ _≤_
  ≤-trans                : Transitive _≤_
  ≤-total                : Total _≤_
  _≤?_                   : Decidable _≤_
  ≤-minimum              : Minimum _≤_ false
  ≤-maximum              : Maximum _≤_ true
  ≤-irrelevant           : B.Irrelevant _≤_
  ≤-isPreorder           : IsPreorder      _≡_ _≤_
  ≤-isPartialOrder       : IsPartialOrder  _≡_ _≤_
  ≤-isTotalOrder         : IsTotalOrder    _≡_ _≤_
  ≤-isDecTotalOrder      : IsDecTotalOrder _≡_ _≤_
  ≤-poset                : Poset         0ℓ 0ℓ 0ℓ
  ≤-preorder             : Preorder      0ℓ 0ℓ 0ℓ
  ≤-totalOrder           : TotalOrder    0ℓ 0ℓ 0ℓ
  ≤-decTotalOrder        : DecTotalOrder 0ℓ 0ℓ 0ℓ

  <-irrefl               : Irreflexive _≡_ _<_
  <-asym                 : Asymmetric _<_
  <-trans                : Transitive _<_
  <-transʳ               : Trans _≤_ _<_ _<_
  <-transˡ               : Trans _<_ _≤_ _<_
  <-cmp                  : Trichotomous _≡_ _<_
  _<?_                   : Decidable _<_
  <-resp₂-≡              : _<_ Respects₂ _≡_
  <-irrelevant           : B.Irrelevant _<_
  <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
  <-isStrictTotalOrder   : IsStrictTotalOrder   _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder 0ℓ 0ℓ 0ℓ
  <-strictTotalOrder     : StrictTotalOrder   0ℓ 0ℓ 0ℓ
  ```

* Added new definitions to `Data.Char.Base`:
  ```agda
  _≈_ : Rel Char 0ℓ
  _<_ : Rel Char 0ℓ
  ```

* Added new properties to `Data.Char.Properties`:
  ```agda
  ≈⇒≡                : _≈_ ⇒ _≡_
  ≈-reflexive        : _≡_ ⇒ _≈_
  ≈-refl             : Reflexive _≈_
  ≈-sym              : Symmetric _≈_
  ≈-trans            : Transitive _≈_
  ≈-subst            : Substitutive _≈_ ℓ
  _≈?_               : Decidable _≈_
  ≈-isEquivalence    : IsEquivalence _≈_
  ≈-setoid           : Setoid _ _
  ≈-isDecEquivalence : IsDecEquivalence _≈_
  ≈-decSetoid        : DecSetoid _ _

  _<?_               : Decidable _<_
  ```

* Added new function to `Data.Digit`:
  ```agda
  toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
  ```

* Added new patterns to `Data.Fin.Base`:
  ```agda
  pattern 0F = zero
  pattern 1F = suc 0F
  pattern 2F = suc 1F
  pattern 3F = suc 2F
  pattern 4F = suc 3F
  pattern 5F = suc 4F
  pattern 6F = suc 5F
  pattern 7F = suc 6F
  pattern 8F = suc 7F
  pattern 9F = suc 8F
  ```

* Added new proof to `Data.Fin.Properties`:
  ```agda
  inject≤-idempotent : inject≤ (inject≤ i m≤n) n≤k ≡ inject≤ i m≤k
  ```

* Added new pattern synonyms to `Data.Integer`:
  ```agda
  pattern +0       = + 0
  pattern +[1+_] n = + (suc n)
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  ≡-setoid            : Setoid 0ℓ 0ℓ
  ≤-totalOrder        : TotalOrder 0ℓ 0ℓ 0ℓ
  _<?_                : Decidable _<_

  +[1+-injective      : +[1+ m ] ≡ +[1+ n ] → m ≡ n
  drop‿+<+            : + m < + n → m ℕ.< n
  drop‿-<-            : -[1+ m ] < -[1+ n ] → n ℕ.< m

  -◃<+◃               : 0 < m → Sign.- ◃ m < Sign.+ ◃ n
  +◃≮-                : Sign.+ ◃ m ≮ -[1+ n ]
  +◃-mono-<           : m ℕ.< n → Sign.+ ◃ m < Sign.+ ◃ n
  +◃-cancel-<         : Sign.+ ◃ m < Sign.+ ◃ n → m ℕ.< n
  neg◃-cancel-<       : Sign.- ◃ m < Sign.- ◃ n → n ℕ.< m

  m⊖n≤m               : m ⊖ n ≤ + m
  m⊖n<1+m             : m ⊖ n < +[1+ m ]
  m⊖1+n<m             : m ⊖ suc n < + m
  -[1+m]≤n⊖m+1        : -[1+ m ] ≤ n ⊖ suc m
  ⊖-monoʳ->-<         : (p ⊖_) Preserves ℕ._>_ ⟶ _<_
  ⊖-monoˡ-<           : (_⊖ p) Preserves ℕ._<_ ⟶ _<_

  *-distrib-+         : _*_ DistributesOver _+_
  *-monoˡ-<-pos       : (+[1+ n ] *_) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos       : (_* +[1+ n ]) Preserves _<_ ⟶ _<_
  *-cancelˡ-<-non-neg : + m * n < + m * o → n < o
  *-cancelʳ-<-non-neg : m * + o < n * + o → m < n
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  foldr-forcesᵇ    : (P (f x y) → P x × P y) → P (foldr f e xs) → All P xs
  foldr-preservesᵇ : (P x → P y → P (f x y)) → P e → All P xs   → P (foldr f e xs)
  foldr-preservesʳ : (P y → P (f x y))       → P e              → P (foldr f e xs)
  foldr-preservesᵒ : (P x ⊎ P y → P (f x y)) → P e ⊎ Any P xs   → P (foldr f e xs)
  ```

* Added a new proof in `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  shifts : xs ++ ys ++ zs ↭ ys ++ xs ++ zs
  ```

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  ++-cancelˡ : Pointwise _∼_ (xs ++ ys) (xs ++ zs) → Pointwise _∼_ ys zs
  ++-cancelʳ : Pointwise _∼_ (ys ++ xs) (zs ++ xs) → Pointwise _∼_ ys zs
  ```

* Added new proof to `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`:
  ```agda
  concat⁺ : Sublist (Sublist R) ass bss → Sublist R (concat ass) (concat bss)
  ```

* Added new proof to `Data.List.Membership.Setoid.Properties`:
  ```agda
  unique⇒irrelevant : Irrelevant _≈_ → Unique xs → Irrelevant (_∈ xs)
  ```

* Added new proofs to `Data.List.Relation.Binary.Sublist.Propositional.Properties`:
  ```agda
  All-resp-⊆ : (All P) Respects (flip _⊆_)
  Any-resp-⊆ : (Any P) Respects _⊆_
  ```

* Added new operations to `Data.List.Relation.Unary.All`:
  ```agda
  lookupAny  : All P xs → (i : Any Q xs) → (P ∩ Q) (lookup i)
  lookupWith : ∀[ P ⇒ Q ⇒ R ] → All P xs → (i : Any Q xs) → R (lookup i)
  uncons     : All P (x ∷ xs) → P x × All P xs
  reduce     : (f : ∀ {x} → P x → B) → ∀ {xs} → All P xs → List B
  construct  : (f : B → ∃ P) (xs : List B) → ∃ (All P)
  fromList   : (xs : List (∃ P)) → All P (List.map proj₁ xs)
  toList     : All P xs → List (∃ P)
  self       : All (const A) xs
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-swap        : All (λ xs → All (xs ~_) ys) xss → All (λ y → All (_~ y) xss) ys
  applyDownFrom⁺₁ : (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₂ : (∀ i → P (f i)) → All P (applyDownFrom f n)
  ```

* Added new proofs to `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  Any-Σ⁺ʳ : (∃ λ x → Any (_~ x) xs) → Any (∃ ∘ _~_) xs
  Any-Σ⁻ʳ : Any (∃ ∘ _~_) xs → ∃ λ x → Any (_~ x) xs
  gmap    : P ⋐ Q ∘ f → Any P ⋐ Any Q ∘ map f
  ```

* Added new functions to `Data.Maybe.Base`:
  ```agda
  ap        : Maybe (A → B) → Maybe A → Maybe B
  _>>=_     : Maybe A → (A → Maybe B) → Maybe B
  ```

* Added new proofs to `Data.Nat.Divisibility`:
  ```agda
  ∣m∸n∣n⇒∣m   : n ≤ m → i ∣ m ∸ n → i ∣ n → i ∣ m
  ∣n∣m%n⇒∣m   : d ∣ n → d ∣ (m % n) → d ∣ m
  *-monoˡ-∣   : i ∣ j → i * k ∣ j * k
  %-presˡ-∣   : d ∣ m → d ∣ n → d ∣ (m % n)
  m/n∣m       : n ∣ m → m / n ∣ m
  m*n∣o⇒m∣o/n : m * n ∣ o → m ∣ o / n
  m*n∣o⇒n∣o/m : m * n ∣ o → n ∣ o / m
  m∣n/o⇒m*o∣n : o ∣ n → m ∣ n / o → m * o ∣ n
  m∣n/o⇒o*m∣n : o ∣ n → m ∣ n / o → o * m ∣ n
  m/n∣o⇒m∣o*n : n ∣ m → m / n ∣ o → m ∣ o * n
  m∣n*o⇒m/n∣o : n ∣ m → m ∣ o * n → m / n ∣ o
  ```

* Added new operator and proofs to `Data.Nat.DivMod`:
  ```agda
  _/_ = _div_

  m%n≤m               : m % n ≤ m
  m≤n⇒m%n≡m           : m ≤ n → m % n ≡ m
  %-remove-+ˡ         : d ∣ m → (m + n) % d ≡ n % d
  %-remove-+ʳ         : d ∣ n → (m + n) % d ≡ m % d
  %-pred-≡0           : suc m % n ≡ 0 → m % n ≡ n ∸ 1
  m<[1+n%d]⇒m≤[n%d]   : m < suc n % d → m ≤ n % d
  [1+m%d]≤1+n⇒[m%d]≤n : 0 < suc m % d → suc m % d ≤ suc n → m % d ≤ n

  0/n≡0               : 0 / n ≡ 0
  n/1≡n               : n / 1 ≡ n
  n/n≡1               : n / n ≡ 1
  m*n/n≡m             : m * n / n ≡ m
  m/n*n≡m             : n ∣ m → m / n * n ≡ m
  m*[n/m]≡n           : m ∣ n → m * (n / m) ≡ n
  m/n*n≤m             : m / n * n ≤ m
  m/n<m               : m ≥ 1 → n ≥ 2 → m / n < m
  *-/-assoc           : d ∣ n → (m * n) / d ≡ m * (n / d)
  +-distrib-/         : m % d + n % d < d → (m + n) / d ≡ m / d + n / d
  +-distrib-/-∣ˡ      : d ∣ m → (m + n) / d ≡ m / d + n / d
  +-distrib-/-∣ʳ      : d ∣ n → (m + n) / d ≡ m / d + n / d
  ```
  Additionally the `{≢0 : False (divisor ℕ.≟ 0)}` argument to all the
  division and modulus functions has been marked irrelevant. One useful consequence
  of this is that the operations `_%_`, `_/_` etc. can now be used with `cong`.

* Added new proofs to `Data.Nat.GCD`:
  ```agda
  gcd[m,n]∣m            : gcd m n ∣ m
  gcd[m,n]∣n            : gcd m n ∣ n
  gcd-greatest          : c ∣ m → c ∣ n → c ∣ gcd m n
  gcd[0,0]≡0            : gcd 0 0 ≡ 0
  gcd[m,n]≢0            : m ≢ 0 ⊎ n ≢ 0 → gcd m n ≢ 0
  gcd-comm              : gcd m n ≡ gcd n m
  gcd-universality      : (∀ {d} → d ∣ m × d ∣ n → d ∣ g) → (∀ {d} → d ∣ g → d ∣ m × d ∣ n) → g ≡ gcd m n
  gcd[cm,cn]/c≡gcd[m,n] : gcd (c * m) (c * n) / c ≡ gcd m n
  c*gcd[m,n]≡gcd[cm,cn] : c * gcd m n ≡ gcd (c * m) (c * n)
  ```

* Added new proofs to `Data.Nat.LCM`:
  ```agda
  m∣lcm[m,n] : m ∣ lcm m n
  n∣lcm[m,n] : n ∣ lcm m n
  lcm-least  : m ∣ c → n ∣ c → lcm m n ∣ c
  lcm[0,n]≡0 : lcm 0 n ≡ 0
  lcm[n,0]≡0 : lcm n 0 ≡ 0
  lcm-comm   : lcm m n ≡ lcm n m
  gcd*lcm    : gcd m n * lcm m n ≡ m * n
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  ≤-<-connex : Connex _≤_ _<_
  ≥->-connex : Connex _≥_ _>_
  <-≤-connex : Connex _<_ _≤_
  >-≥-connex : Connex _>_ _≥_

  1+n≢0     : suc n ≢ 0
  <ᵇ⇒<      : T (m <ᵇ n) → m < n
  <⇒<ᵇ      : m < n → T (m <ᵇ n)
  n≢0⇒n>0   : n ≢ 0 → n > 0
  m≤m*n     : 0 < n → m ≤ m * n
  m<m*n     : 0 < m → 1 < n → m < m * n
  m∸n≢0⇒n<m : m ∸ n ≢ 0 → n < m

  *-cancelʳ-< : RightCancellative _<_ _*_
  *-cancelˡ-< : LeftCancellative _<_ _*_
  *-cancel-<  : Cancellative _<_ _*_

  ⊔-least    : m ≤ o → n ≤ o → m ⊔ n ≤ o
  ⊓-greatest : m ≥ o → n ≥ o → m ⊓ n ≥ o
  ```

* Added new function to `Data.Product`:
  ```agda
  zip′ : (A → B → C) → (D → E → F) → A × D → B × E → C × F
  ```

* Added new proofs to `Data.Product.Properties`:
  ```agda
  ,-injectiveʳ : (a , b) ≡ (c , d) → b ≡ d
  ,-injective  : (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ≡-dec        : Decidable {A} _≡_ → Decidable {B} _≡_ → Decidable {A × B} _≡_
  ```

* Added new relations to `Data.Rational.Base`:
  ```agda
  _<_ : Rel ℚ 0ℓ
  _≥_ : Rel ℚ 0ℓ
  _>_ : Rel ℚ 0ℓ
  _≰_ : Rel ℚ 0ℓ
  _≱_ : Rel ℚ 0ℓ
  _≮_ : Rel ℚ 0ℓ
  _≯_ : Rel ℚ 0ℓ
  ```

* Added new proofs and modules to `Data.Rational.Properties`:
  ```agda
  ≡-setoid     : Setoid 0ℓ 0ℓ
  ≡-decSetoid  : DecSetoid 0ℓ 0ℓ

  drop-*<*     : p < q → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p)
  <⇒≤          : _<_ ⇒ _≤_
  <-irrefl     : Irreflexive _≡_ _<_
  <-asym       : Asymmetric _<_
  <-≤-trans    : Trans _<_ _≤_ _<_
  ≤-<-trans    : Trans _≤_ _<_ _<_
  <-trans      : Transitive _<_
  _<?_         : Decidable _<_
  <-cmp        : Trichotomous _≡_ _<_
  <-irrelevant : Irrelevant _<_
  <-respʳ-≡    : _<_ Respectsʳ _≡_
  <-respˡ-≡    : _<_ Respectsˡ _≡_
  <-resp-≡     : _<_ Respects₂ _≡_

  <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
  <-isStrictTotalOrder   : IsStrictTotalOrder _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder 0ℓ 0ℓ 0ℓ
  <-strictTotalOrder     : StrictTotalOrder 0ℓ 0ℓ 0ℓ

  module ≤-Reasoning
  ```

* Added new proofs to `Data.Sign.Properties`:
  ```agda
  ≡-setoid    : Setoid 0ℓ 0ℓ
  ≡-decSetoid : DecSetoid 0ℓ 0ℓ
  ```

* Added new definitions and functions to `Data.String.Base`:
  ```agda
  _≈_ : Rel String 0ℓ
  _<_ : Rel String 0ℓ

  fromChar : Char → String
  ```

* Added new properties to `Data.String.Properties`:
  ```agda
  ≈⇒≡                : _≈_ ⇒ _≡_
  ≈-reflexive        : _≡_ ⇒ _≈_
  ≈-refl             : Reflexive _≈_
  ≈-sym              : Symmetric _≈_
  ≈-trans            : Transitive _≈_
  ≈-subst            : Substitutive _≈_ ℓ
  _≈?_               : Decidable _≈_
  ≈-isEquivalence    : IsEquivalence _≈_
  ≈-setoid           : Setoid _ _
  ≈-isDecEquivalence : IsDecEquivalence _≈_
  ≈-decSetoid        : DecSetoid _ _

  _<?_               : Decidable _<_
  ```

* Added new functions to `Data.Vec.Base`:
  ```agda
  restrictWith : (A → B → C) → Vec A m → Vec B n → Vec C (m ⊓ n)
  restrict     : Vec A m → Vec B n → Vec (A × B) (m ⊓ n)
  ```

* Added new functions to `Data.Vec`:
  ```agda
  filter    : Decidable P → Vec A n → Vec≤ A n
  takeWhile : Decidable P → Vec A n → Vec≤ A n
  dropWhile : Decidable P → Vec A n → Vec≤ A n
  ```

* The special term `Setω` is now exported by `Level`.

* Added new types, functions and proofs to `Reflection`:
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

* Added new definition to `Setoid` in `Relation.Binary`:
  ```agda
  x ≉ y = ¬ (x ≈ y)
  ```

* Added new definitions in `Relation.Binary.Core`:
  ```agda
  Universal _∼_    = ∀ x y → x ∼ y
  Recomputable _~_ = ∀ {x y} → .(x ~ y) → x ~ y
  ```

* Added new proof to `Relation.Binary.Consequences`:
  ```agda
  dec⟶recomputable : Decidable R → Recomputable R
  flip-Connex      : Connex P Q → Connex Q P
  ```

* Added new proofs to `Relation.Binary.Construct.Add.(Infimum/Supremum/Extrema).NonStrict`:
  ```agda
  ≤±-reflexive-≡         : (_≡_ ⇒ _≤_) → (_≡_ ⇒ _≤±_)
  ≤±-antisym-≡           : Antisymmetric _≡_ _≤_ → Antisymmetric _≡_ _≤±_
  ≤±-isPreorder-≡        : IsPreorder _≡_ _≤_ → IsPreorder _≡_ _≤±_
  ≤±-isPartialOrder-≡    : IsPartialOrder _≡_ _≤_ → IsPartialOrder _≡_ _≤±_
  ≤±-isDecPartialOrder-≡ : IsDecPartialOrder _≡_ _≤_ → IsDecPartialOrder _≡_ _≤±_
  ≤±-isTotalOrder-≡      : IsTotalOrder _≡_ _≤_ → IsTotalOrder _≡_ _≤±_
  ≤±-isDecTotalOrder-≡   : IsDecTotalOrder _≡_ _≤_ → IsDecTotalOrder _≡_ _≤±_
  ```

* Added new proofs to `Relation.Binary.Construct.Add.(Infimum/Supremum/Extrema).Strict`:
  ```agda
  <±-respˡ-≡                   : _<±_ Respectsˡ _≡_
  <±-respʳ-≡                   : _<±_ Respectsʳ _≡_
  <±-resp-≡                    : _<±_ Respects₂ _≡_
  <±-cmp-≡                     : Trichotomous _≡_ _<_ → Trichotomous _≡_ _<±_
  <±-irrefl-≡                  : Irreflexive _≡_ _<_ → Irreflexive _≡_ _<±_
  <±-isStrictPartialOrder-≡    : IsStrictPartialOrder _≡_ _<_ → IsStrictPartialOrder _≡_ _<±_
  <±-isDecStrictPartialOrder-≡ : IsDecStrictPartialOrder _≡_ _<_ → IsDecStrictPartialOrder _≡_ _<±_
  <±-isStrictTotalOrder-≡      : IsStrictTotalOrder _≡_ _<_ → IsStrictTotalOrder _≡_ _<±_
  ```

* In `Relation.Binary.HeterogeneousEquality` the relation `_≅_` has
  been generalised so that the types of the two equal elements need not
  be at the same universe level.

* Added new proof to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  ≢-sym : Symmetric _≢_
  ```

* Added new proofs to `Relation.Nullary.Construct.Add.Point`:
  ```agda
  ≡-dec        : Decidable {A = A} _≡_ → Decidable {A = Pointed A} _≡_
  []-injective : [ x ] ≡ [ y ] → x ≡ y
  ```

* Added new type and syntax to `Relation.Unary`:
  ```agda
  Recomputable P = ∀ {x} → .(P x) → P x
  syntax Satisfiable P = ∃⟨ P ⟩
  ```

* Added new proof to `Relation.Unary.Consequences`:
  ```agda
  dec⟶recomputable : Decidable R → Recomputable R
  ```

* Added new aliases for `IdempotentCommutativeMonoid` in `Algebra`:
  ```agda
  BoundedLattice   = IdempotentCommutativeMonoid
  IsBoundedLattice = IsIdempotentCommutativeMonoid
  ```

* Added new functions to `Function`:
  ```agda
  _$- : ((x : A) → B x) → ({x : A} → B x)
  λ-  : ({x : A} → B x) → ((x : A) → B x)
  ```

* Added new definition and proof to `Axiom.Extensionality.Propositional`:
  ```agda
  ExtensionalityImplicit  = (∀ {x} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  implicit-extensionality : Extensionality a b → ExtensionalityImplicit a b
  ```

* Added new definition in `Relation.Nullary`:
  ```agda
  Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
  ```

* Added new proofs to `Relation.Nullary.Decidable.Core`:
  ```agda
  dec-yes     : (p? : Dec P) → P → ∃ λ p′ → p? ≡ yes p′
  dec-no      : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
  dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
  ```
