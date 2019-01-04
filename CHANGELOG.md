Version TODO
============

The library has been tested using Agda version 2.5.4.1.

Important changes since 0.17:

Non-backwards compatible changes
--------------------------------

#### Support for `--without-K`

The `--without-K` flag has been enabled in a number of files. An
attempt has been made to only do this in files that do not depend on
any file in which this flag is not enabled.

Agda uses different rules for the target universe of data types when
the `--without-K` flag is used, and because of this a number of type
families now target a possibly larger universe:

* `Codata.Delay.Bisimilarity.Bisim`.
* `Codata.Musical.Covec._≈_`.
* `Codata.Musical.Covec._∈_`.
* `Codata.Musical.Covec._⊑_`.
* `Codata.Stream.Bisimilarity.Bisim`.
* `Data.List.All.All`.
* `Data.List.First.First`.
* `Data.List.Relation.Prefix.Heterogeneous.Prefix`.
* `Data.List.Relation.Prefix.Heterogeneous.PrefixView`.
* `Data.List.Relation.Equality.Setoid._≋_`.
* `Data.List.Relation.Lex.NonStrict.Lex-<`.
* `Data.List.Relation.Lex.NonStrict.Lex-≤`.
* `Data.List.Relation.Lex.Strict.Lex-<`.
* `Data.List.Relation.Lex.Strict.Lex-≤`.
* `Data.List.Relation.Pointwise.Pointwise`.
* `Data.Maybe.Is-just`.
* `Data.Maybe.Is-nothing`.
* `Data.Maybe.Any.Any`.
* `Data.Maybe.All.All`.
* `Data.Maybe.Relation.Pointwise.Pointwise`.

Because of this change the texts of some type signatures were changed
(some inferred parts of other type signatures may also have changed):

* `Data.List.All.forA`.
* `Data.List.All.forM`.
* `Data.List.All.mapA`.
* `Data.List.All.mapM`.
* `Data.List.All.sequenceA`.
* `Data.List.All.sequenceM`.
* `Data.List.Relation.Equality.DecSetoid.≋-decSetoid`.
* `Data.Maybe.All.forA`.
* `Data.Maybe.All.forM`.
* `Data.Maybe.All.mapA`.
* `Data.Maybe.All.mapM`.
* `Data.Maybe.All.sequenceA`.
* `Data.Maybe.All.sequenceM`.
* `Data.Maybe.Relation.Pointwise.decSetoid`.
* `Data.Maybe.Relation.Pointwise.setoid`.

Some code that relies on the K rule or uses heterogeneous equality has
been moved to new files:

* `Data.AVL.Indexed.node-injective-bal` to `Data.AVL.Indexed.WithK`.
* `Data.AVL.Indexed.node-injectiveʳ` to `Data.AVL.Indexed.WithK`.
* `Data.AVL.Indexed.node-injectiveˡ` to `Data.AVL.Indexed.WithK`.
* `Data.Container.Indexed.Eq` to `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.Map.composition` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.Map.identity` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.PlainMorphism.NT` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.PlainMorphism.Natural` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.PlainMorphism.complete` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.PlainMorphism.natural` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.PlainMorphism.∘-correct` to
  `Data.Container.Indexed.WithK`.
* `Data.Container.Indexed.setoid` to `Data.Container.Indexed.WithK`.
* `Data.Product.Properties.,-injectiveʳ` to
  `Data.Product.Properties.WithK`.
* `Data.Product.Relation.Pointwise.Dependent.Pointwise-≡↔≡` to
  `Data.Product.Relation.Pointwise.Dependent.WithK`.
* `Data.Product.Relation.Pointwise.Dependent.Pointwise-≡⇒≡` to
  `Data.Product.Relation.Pointwise.Dependent.WithK`.
* `Data.Product.Relation.Pointwise.Dependent.inverse` to
  `Data.Product.Relation.Pointwise.Dependent.WithK`.
* `Data.Product.Relation.Pointwise.Dependent.↣` to
  `Data.Product.Relation.Pointwise.Dependent.WithK`. (The name
  `Data.Product.Relation.Pointwise.Dependent.↣` now refers to a new
  definition with another type signature.)
* `Data.Product.Relation.Pointwise.Dependent.≡⇒Pointwise-≡` to
  `Data.Product.Relation.Pointwise.Dependent.WithK`.
* `Data.Vec.Properties.++-assoc` to `Data.Vec.Properties.WithK`.
* `Data.Vec.Properties.[]=-irrelevance` to `Data.Vec.Properties.WithK`.
* `Data.Vec.Properties.foldl-cong` to `Data.Vec.Properties.WithK`.
* `Data.Vec.Properties.foldr-cong` to `Data.Vec.Properties.WithK`.
* `Data.Vec.Relation.Equality.Propositional.≋⇒≅` to
  `Data.Vec.Relation.Equality.Propositional.WithK`.
* `Data.W.sup-injective₂` to `Data.W.WithK`.
* `Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.◅-injectiveʳ`
  to
  `Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.WithK`.
* `Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.◅-injectiveˡ`
  to
  `Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.WithK`.
* `Relation.Binary.Construct.Closure.Transitive.∼⁺⟨⟩-injectiveʳ` to
  `Relation.Binary.Construct.Closure.Transitive.WithK`.
* `Relation.Binary.Construct.Closure.Transitive.∼⁺⟨⟩-injectiveˡ` to
  `Relation.Binary.Construct.Closure.Transitive.WithK`.
* `Relation.Binary.PropositionalEquality.≡-irrelevance` to
  `Relation.Binary.PropositionalEquality.WithK`.

Other code has been changed to avoid use of the K rule. As part of
such changes the texts of the following type signatures have been
changed:

* `Data.AVL.Indexed.node-injective-key`.
* `Data.List.Relation.Sublist.Propositional.Properties.∷⁻`.
* `Data.Product.Relation.Pointwise.Dependent.↣`. (The old definition
  was moved to `Data.Product.Relation.Pointwise.Dependent.WithK`.)
* `Relation.Binary.PropositionalEquality.≡-≟-identity`.

The following definitions have been removed:

* `Relation.Binary.PropositionalEquality._≅⟨_⟩_`.

Some deprecated names have also been removed:

* `Data.Product.Relation.Pointwise.Dependent.Rel↔≡`.
* `Data.Vec.Properties.proof-irrelevance-[]=`.
* `Relation.Binary.PropositionalEquality.proof-irrelevance`.

Finally some new, supporting code has been added:

* The module `Function.HalfAdjointEquivalence`.
* In `Relation.Binary.PropositionalEquality`: `cong-id`, `cong-∘`,
  `cong-≡id`, `naturality`, `subst-application`, `subst-subst`,
  `subst-subst-sym`, `subst-sym-subst`, `subst-∘`, `trans-assoc`,
  `trans-reflʳ`, `trans-symʳ` and `trans-symˡ`.

#### Overhaul of `Data.Maybe`

Splitting up `Data.Maybe` into the standard hierarchy.

* Moved `Data.Maybe.Base`'s `Is-just`, `Is-nothing`, `to-witness`,
  and `to-witness-T` to `Data.Maybe` (they rely on `All` and `Any`
  which are now outside of `Data.Maybe.Base`).

* Moved `Data.Maybe.Base`'s `All` and `Data.Maybe`'s `allDec` to
  `Data.Maybe.All` and renamed some proofs:
  ```agda
  allDec ↦ dec
  ```

* Moved `Data.Maybe.Base`'s `Any` and `Data.Maybe`'s `anyDec` to
  `Data.Maybe.Any` and renamed some proofs:
  ```agda
  anyDec ↦ dec
  ```

* Created `Data.Maybe.Properties`, moved `Data.Maybe.Base`'s `just-injective`
  there and added new results.

* Moved `Data.Maybe`'s `Eq` to `Data.Maybe.Relation.Pointwise`, made the
  relation heterogeneously typed and renamed the following proofs:
  ```agda
  Eq                  ↦ Pointwise
  Eq-refl             ↦ refl
  Eq-sym              ↦ sym
  Eq-trans            ↦ trans
  Eq-dec              ↦ dec
  Eq-isEquivalence    ↦ isEquivalence
  Eq-isDecEquivalence ↦ isDecEquivalence
  ```

#### Changes to the algebra hierarchy

* Over time the algebra inheritance hierarchy has become a little
  wonky due to poorly structured additions. This attempts to straighten
  the hierarchy out and new policies have been put in place so that
  the need for additional such changes will be minimised in the future.

* Added `Magma` and `IsMagma` to the algebra hierarchy.

* The name `RawSemigroup` in `Algebra` has been deprecated in favour
  of `RawMagma`.

* The fields `isEquivalence` and `∙-cong` in `IsSemigroup` have been
  replaced with `isMagma`.

* The record `BooleanAlgebra` now exports `∨-isSemigroup`, `∧-isSemigroup`
  directly  so `Algebra.Properties.BooleanAlgebra` no longer does so.

* The proof that every algebraic lattice induces a partial order has been
  moved from `Algebra.Properties.Lattice` to
  `Algebra.Properties.Semilattice`.  The corresponding `poset` instance is
  re-exported in `Algebra.Properties.Lattice`.

* All algebraic structures now export left and right congruence properties.
  e.g. `∙-cong refl x≈y` can be replaced with `∙-congˡ y≈z`

#### Relaxation of ring solvers requirements

* In the ring solvers below, the assumption that equality is `Decidable`
  has been replaced by a strictly weaker assumption that it is `WeaklyDecidable`.
  This allows the solvers to be used when equality is not fully decidable.
  ```
  Algebra.Solver.Ring
  Algebra.Solver.Ring.NaturalCoefficients
  ```

* Created a module `Algebra.Solver.Ring.NaturalCoefficients.Default` that
  instantiates the solver for any `CommutativeSemiring`.

#### Overhaul of `Data.AVL`

* AVL trees now work over arbitrary equalities, rather than just
  propositional equality.

* Consequently the family of `Value`s stored in the tree now need
  to respect the `Key` equivalence

* The module parameter for `Data.AVL`, `Data.AVL.Indexed`, `Data.AVL.Key`,
  `Data.AVL.Sets` is now a `StrictTotalOrder` rather than a
  `IsStrictTotalOrder`, and the module parameter for `Data.AVL.Value` is
  now takes a `Setoid` rather than an `IsEquivalence`.

* It was noticed that `Data.AVL.Indexed`'s lookup & delete didn't use
  a range to guarantee that the recursive calls were performed in the
  right subtree. The types have been made more precise.

* The functions (insert/union)With now take a function of type
  `Maybe Val -> Val` rather than a value together with a merging function
  `Val -> Val -> Val` to handle the case where a value is already present
  at that key.

* Various functions have been made polymorphic which makes their biases
  & limitations clearer. e.g. we have:
  `unionWith : (V -> Maybe W -> W) -> Tree V -> Tree W -> Tree W`
  but ideally we would like to have:
  `unionWith : (These V W -> X) -> Tree V -> Tree W -> Tree X`

#### Other

* The proof `sel⇒idem` has been moved from `Algebra.FunctionProperties.Consequences` to
  `Algebra.FunctionProperties.Consequences.Propositional` as it does not rely on equality.

* Moved `_≟_` from `Data.Bool.Base` to `Data.Bool.Properties`. Backwards
  compatibility has been (nearly completely) preserved by having `Data.Bool`
  publicly re-export `_≟_`.

* In `Data.List.Membership.Propositional.Properties`:
    - Made the `Set` argument implicit in `∈-++⁺ˡ`, `∈-++⁺ʳ`, `∈-++⁻`, `∈-insert`, `∈-∃++`.
    - Made the `A → B` argument explicit in `∈-map⁺`, `∈-map⁻`, `map-∈↔`.

* The type `Coprime` and proof `coprime-divisor` have been moved from `Data.Integer.Divisibility`
  to `Data.Integer.Coprimality`.

* The proofs `drop-*≤*`, `≃⇒≡` and `≡⇒≃` have been moved from `Data.Rational`
  to `Data.Rational.Properties`.

* Fixed bug in `Data.Nat.Properties` where the type of `m⊓n≤m⊔n` was `∀ m n → m ⊔ n ≤ m ⊔ n`,
  the type is now correctly `∀ m n → m ⊓ n ≤ m ⊔ n`.

* The proofs `toList⁺` and `toList⁻` in `Data.Vec.All.Properties` have been swapped
  as they were the opposite way round to similar properties in the rest of the library.

Other major changes
-------------------

* Added new modules `Algebra.Construct.NaturalChoice.(Min/Max)`

* Added new module `Algebra.Properties.Semilattice`

* Added new module `Algebra.FunctionProperties.Consequences.Propositional`

* Added new module `Codata.Cowriter`

* Added new modules `Codata.M.Properties` and `Codata.M.Bisimilarity`

* Added new modules `Data.Integer.Divisibility.Properties`,
  `Data.Integer.Divisibility.Signed` and `Data.Integer.DivMod`.

* Added new modules `Data.List.Relation.Prefix.Heterogeneous(.Properties)`

* Added new modules `Data.List.First` and `Data.List.First.Properties` for a
  generalization of the notion of "first element in the list to satisfy a
  predicate".

* Added new modules `Data.List.Relation.Prefix.Heterogeneous(.Properties)`

* Added new modules `Data.List.Relation.Interleaving(.Setoid/Propositional)`
  and `Data.List.Relation.Interleaving(.Setoid/Propositional).Properties`.

* Added new module `Data.Vec.Any.Properties`

* Added new modules `Data.Vec.Membership.(Setoid/DecSetoid/DecPropositional)`

* Added new modules `Relation.Binary.Construct.Intersection/Union`

* Added new modules `Relation.Binary.Construct.NaturalOrder.(Left/Right)`

* Added new module `Relation.Binary.Properties.BoundedLattice`

* Added new module `Debug.Trace`

Deprecated features
-------------------

* In `Data.Integer.Properties`:
  ```agda
  ≰→> ↦ ≰⇒>
  ```

* In `Data.Rational`:
  ```agda
  drop-*≤*
  ≃⇒≡
  ≡⇒≃
  ```
  (moved to `Data.Rational.Properties`)

Other minor additions
---------------------

* Added new proof to `Data.Nat.Properties`:
  ```agda
  ≤′-trans : Transitive _≤′_
  ```

* Added new records to `Algebra`:
  ```agda
  record RawMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Magma    c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new types to `Algebra.FunctionProperties`:
  ```agda
  LeftCongruent  _∙_ = ∀ {x} → (_∙ x) Preserves _≈_ ⟶ _≈_
  RightCongruent _∙_ = ∀ {x} → (x ∙_) Preserves _≈_ ⟶ _≈_
  ```

* Added new proof to `Algebra.FunctionProperties.Consequences`:
  ```agda
  wlog : Commutative f → Total _R_ → (∀ a b → a R b → P (f a b)) → ∀ a b → P (f a b)
  ```

* Added new proofs to `Algebra.Properties.Lattice`:
  ```agda
  ∧-isSemilattice : IsSemilattice _≈_ _∧_
  ∧-semilattice : Semilattice l₁ l₂
  ∨-isSemilattice : IsSemilattice _≈_ _∨_
  ∨-semilattice : Semilattice l₁ l₂
  ```

* Added new operator to `Algebra.Solver.Ring`.
  ```agda
  _:×_
  ```

* Added new records to `Algebra.Structures`:
  ```agda
  record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  ```

* Added new functions to `Codata.Colist`:
  ```agda
  fromCowriter : Cowriter W A i → Colist W i
  toCowriter   : Colist A i → Cowriter A ⊤ i
  [_]          : A → Colist A ∞
  chunksOf     : (n : ℕ) → Colist A ∞ → Cowriter (Vec A n) (BoundedVec A n) ∞
  ```

* Added new functions to `Codata.Stream`:
  ```agda
  splitAt    : (n : ℕ) → Stream A ∞ → Vec A n × Stream A ∞
  drop       : ℕ → Stream A ∞ → Stream A ∞
  interleave : Stream A i → Thunk (Stream A) i → Stream A i
  chunksOf   : (n : ℕ) → Stream A ∞ → Stream (Vec A n) ∞
  ```

* Added new proof to `Codata.Stream.Properties`:
  ```agda
  splitAt-map : splitAt n (map f xs) ≡ map (map f) (map f) (splitAt n xs)
  lookup-iterate-identity : lookup n (iterate f a) ≡ fold a f n
  ```

* Added new proofs to `Data.Bool.Properties`:
  ```agda
  ∧-isMagma       : IsMagma _∧_
  ∨-isMagma       : IsMagma _∨_
  ∨-isBand        : IsBand _∨_
  ∨-isSemilattice : IsSemilattice _∨_
  ∧-isBand        : IsBand _∧_
  ∧-isSemilattice : IsSemilattice _∧_

  ∧-magma         : Magma 0ℓ 0ℓ
  ∨-magma         : Magma 0ℓ 0ℓ
  ∨-band          : Band 0ℓ 0ℓ
  ∧-band          : Band 0ℓ 0ℓ
  ∨-semilattice   : Semilattice 0ℓ 0ℓ
  ∧-semilattice   : Semilattice 0ℓ 0ℓ
  ```

* Added new function to `Data.Fin.Base`:
  ```agda
  cast : m ≡ n → Fin m → Fin n
  ```

* Added new proof to `Data.Fin.Properties`:
  ```agda
  toℕ-cast    : toℕ (cast eq k) ≡ toℕ k
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  ∩-isMagma       : IsMagma _∩_
  ∪-isMagma       : IsMagma _∪_
  ∩-isBand        : IsBand _∩_
  ∪-isBand        : IsBand _∪_
  ∩-isSemilattice : IsSemilattice _∩_
  ∪-isSemilattice : IsSemilattice _∪_

  ∩-magma         : Magma _ _
  ∪-magma         : Magma _ _
  ∩-band          : Band _ _
  ∪-band          : Band _ _
  ∩-semilattice   : Semilattice _ _
  ∪-semilattice   : Semilattice _ _
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  suc-pred      : sucℤ (pred m) ≡ m
  pred-suc      : pred (sucℤ m) ≡ m
  neg-suc       : - + suc m ≡ pred (- + m)
  suc-+         : + suc m + n ≡ sucℤ (+ m + n)
  +-pred        : m + pred n ≡ pred (m + n)
  pred-+        : pred m + n ≡ pred (m + n)
  minus-suc     : m - + suc n ≡ pred (m - + n)
  [1+m]*n≡n+m*n : sucℤ m * n ≡ n + m * n

  ⊓-comm    : Commutative _⊓_
  ⊓-assoc   : Associative _⊓_
  ⊓-idem    : Idempotent _⊓_
  ⊓-sel     : Selective _⊓_
  m≤n⇒m⊓n≡m : m ≤ n → m ⊓ n ≡ m
  m⊓n≡m⇒m≤n : m ⊓ n ≡ m → m ≤ n
  m≥n⇒m⊓n≡n : m ≥ n → m ⊓ n ≡ n
  m⊓n≡n⇒m≥n : m ⊓ n ≡ n → m ≥ n
  m⊓n≤n     : m ⊓ n ≤ n
  m⊓n≤m     : m ⊓ n ≤ m

  ⊔-comm    : Commutative _⊔_
  ⊔-assoc   : Associative _⊔_
  ⊔-idem    : Idempotent _⊔_
  ⊔-sel     : Selective _⊔_
  m≤n⇒m⊔n≡n : m ≤ n → m ⊔ n ≡ n
  m⊔n≡n⇒m≤n : m ⊔ n ≡ n → m ≤ n
  m≥n⇒m⊔n≡m : m ≥ n → m ⊔ n ≡ m
  m⊔n≡m⇒m≥n : m ⊔ n ≡ m → m ≥ n
  m≤m⊔n     : m ≤ m ⊔ n
  n≤m⊔n     : n ≤ m ⊔ n

  neg-distrib-⊔-⊓ : - (m ⊔ n) ≡ - m ⊓ - n
  neg-distrib-⊓-⊔ : - (m ⊓ n) ≡ - m ⊔ - n

  pred-mono         : pred Preserves _≤_ ⟶ _≤_
  suc-mono          : sucℤ Preserves _≤_ ⟶ _≤_
  ⊖-monoʳ-≥-≤       : (p ⊖_) Preserves ℕ._≥_ ⟶ _≤_
  ⊖-monoˡ-≤         : (_⊖ p) Preserves ℕ._≤_ ⟶ _≤_
  +-monoʳ-≤         : (_+_ n) Preserves _≤_ ⟶ _≤_
  +-monoˡ-≤         : (_+ n) Preserves _≤_ ⟶ _≤_
  +-monoˡ-<         : (_+ n) Preserves _<_ ⟶ _<_
  +-monoʳ-<         : (_+_ n) Preserves _<_ ⟶ _<_
  *-monoˡ-≤-pos     : (+ suc n *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-non-neg : (_* + n) Preserves _≤_ ⟶ _≤
  *-monoˡ-≤-non-neg : (+ n *_) Preserves _≤_ ⟶ _≤_
  +-mono-≤          : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-mono-<          : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-mono-≤-<        : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
  +-mono-<-≤        : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  neg-mono-≤-≥      : -_ Preserves _≤_ ⟶ _≥_
  neg-mono-<->      : -_ Preserves _<_ ⟶ _>_

  *-cancelˡ-≡     : i ≢ + 0 → i * j ≡ i * k → j ≡ k
  *-cancelˡ-≤-pos : + suc m * n ≤ + suc m * o → n ≤ o

  neg-≤-pos     : - (+ m) ≤ + n
  0⊖m≤+         : 0 ⊖ m ≤ + n
  m≤n⇒m-n≤0     : m ≤ n → m - n ≤ + 0
  m-n≤0⇒m≤n     : m - n ≤ + 0 → m ≤ n
  m≤n⇒0≤n-m     : m ≤ n → + 0 ≤ n - m
  0≤n-m⇒m≤n     : + 0 ≤ n - m → m ≤ n
  m≤pred[n]⇒m<n : m ≤ pred n → m < n
  m<n⇒m≤pred[n] : m < n → m ≤ pred n
  m≤m+n         : m ≤ m + + n
  n≤m+n         : n ≤ + m + n
  m-n≤m         : m - + n ≤ m

  ≤-<-trans : Trans _≤_ _<_ _<_
  <-≤-trans : Trans _<_ _≤_ _<_
  >→≰       : x > y → x ≰ y
  >-irrefl  : Irreflexive _≡_ _>_

  <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder _ _ _

  pos-+-commute  : Homomorphic₂ +_ ℕ._+_ _+_
  neg-distribˡ-* : - (x * y) ≡ (- x) * y
  neg-distribʳ-* : - (x * y) ≡ x * (- y)
  *-distribˡ-+   : _*_ DistributesOverˡ _+_
  ≤-steps        : m ≤ n → m ≤ + p + n
  ≤-step-neg     : m ≤ n → pred m ≤ n
  ≤-steps-neg    : m ≤ n → m - + p ≤ n
  m≡n⇒m-n≡0      : m ≡ n → m - n ≡ + 0
  m-n≡0⇒m≡n      : m - n ≡ + 0 → m ≡ n
  0≤n⇒+∣n∣≡n     : + 0 ≤ n → + ∣ n ∣ ≡ n
  +∣n∣≡n⇒0≤n     : + ∣ n ∣ ≡ n → + 0 ≤ n
  ◃-≡            : sign m ≡ sign n → ∣ m ∣ ≡ ∣ n ∣ → m ≡ n

  +-isMagma   : IsMagma _+_
  *-isMagma   : IsMagma _*_

  +-magma     : Magma 0ℓ 0ℓ
  *-magma     : Magma 0ℓ 0ℓ
  +-semigroup : Semigroup 0ℓ 0ℓ
  *-semigroup : Semigroup 0ℓ 0ℓ
  +-0-monoid  : Monoid 0ℓ 0ℓ
  *-1-monoid  : Monoid 0ℓ 0ℓ
  +-*-ring    : Ring 0ℓ 0ℓ
  ```

* Added new operations to `Data.List.All`:
  ```agda
  zipWith   : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q

  sequenceA : All (F ∘′ P) ⊆ F ∘′ All P
  sequenceM : All (M ∘′ P) ⊆ M ∘′ All P
  mapA      : (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  mapM      : (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forA      : All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  forM      : All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  ```

* Added new operators to `Data.List.Base`:
  ```agda
  _[_]%=_ : (xs : List A) → Fin (length xs) → (A → A) → List A
  _[_]∷=_ : (xs : List A) → Fin (length xs) → A → List A
  _─_     : (xs : List A) → Fin (length xs) → List A

  reverseAcc : List A → List A → List A
  ```

* Added new proofs to `Data.List.All.Properties`:
  ```agda
  respects : P Respects _≈_ → (All P) Respects _≋_
  ```
  A generalization of single point overwrite `_[_]≔_`
  to single-point modification `_[_]%=_`
  (alias with different argument order: `updateAt`):
  ```agda
  _[_]%=_   : Vec A n → Fin n → (A → A) → Vec A n
  updateAt  : Fin n → (A → A) → Vec A n → Vec A n
  ```

* Added new functions to `Data.List.Base`:
  ```agda
  intercalate       : List A → List (List A) → List A
  partitionSumsWith : (A → B ⊎ C) → List A → List B × List C
  partitionSums     : List (A ⊎ B) → List A × List B
  ```

* Added new proofs to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-allFin : (k : Fin n) → k ∈ allFin n
  []∈inits : [] ∈ inits as
  ```

* Added new function to `Data.List.Membership.(Setoid/Propositional)`:
  ```agda
  _∷=_    : x ∈ xs → A → List A
  _─_     : (xs : List A) → x ∈ xs → List A
  ```
  Added laws for `updateAt`.
  Now laws for `_[_]≔_` are special instances of these.

* Added new proofs to `Data.List.Membership.Setoid.Properties`:
  ```agda
  length-mapWith∈ : length (mapWith∈ xs f) ≡ length xs

  ∈-∷=⁺-updated   : v ∈ (x∈xs ∷= v)
  ∈-∷=⁺-untouched : x ≉ y → y ∈ xs → y ∈ (x∈xs ∷= v)
  ∈-∷=⁻           : y ≉ v → y ∈ (x∈xs ∷= v) → y ∈ xs

  map-∷=          : map f (x∈xs ∷= v) ≡ ∈-map⁺ f≈ pr ∷= f v
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  ++-isMagma : IsMagma _++_

  length-%=  : length (xs [ k ]%= f) ≡ length xs
  length-∷=  : length (xs [ k ]∷= v) ≡ length xs
  map-∷=     : map f (xs [ k ]∷= v) ≡ map f xs [ cast eq k ]∷= f v
  length-─   : length (xs ─ k) ≡ pred (length xs)
  map-─      : map f (xs ─ k) ≡ map f xs ─ cast eq k
  ```

* Added new proofs to `Data.List.Relation.Permutation.Inductive.Properties`:
  ```agda
  ++-isMagma : IsMagma _↭_ _++_
  ++-magma   : Magma _ _
  ```

* Added new proofs to `Data.Maybe.All`:
  ```agda
  drop-just        : All P (just x) → P x
  just-equivalence : P x ⇔ All P (just x)
  map              : P ⊆ Q → All P ⊆ All Q
  fromAny          : Any P ⊆ All P
  zipWith          : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith        : P ⊆ Q ∩ R → All P ⊆ All Q ∩ All R
  zip              : All P ∩ All Q ⊆ All (P ∩ Q)
  unzip            : All (P ∩ Q) ⊆ All P ∩ All Q
  sequenceA        : RawApplicative F → All (F ∘′ P) ⊆ F ∘′ All P
  mapA             : RawApplicative F → (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  forA             : RawApplicative F → All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  sequenceM        : RawMonad M → All (M ∘′ P) ⊆ M ∘′ All P
  mapM             : RawMonad M → (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forM             : RawMonad M → All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  universal        : Universal P → Universal (All P)
  irrelevant       : Irrelevant P → Irrelevant (All P)
  satisfiable      : Satisfiable (All P)
  ```

* Created `Data.Maybe.All.Properties`:
  ```agda
  map⁺ : All (P ∘ f) mx → All P (map f mx)
  map⁻ : All P (map f mx) → All (P ∘ f) mx
  gmap : P ⊆ Q ∘ f → All P ⊆ All Q ∘ map f
  <∣>⁺ : All P mx → All P my → All P (mx <∣> my)
  <∣>⁻ : All P (mx <∣> my) → All P mx
  ```

* Added new proofs to `Data.Maybe.Any`:
  ```agda
  drop-just        : Any P (just x) → P x
  just-equivalence : P x ⇔ Any P (just x)
  map              : P ⊆ Q → Any P ⊆ Any Q
  satisfied        : Any P x → ∃ P
  zipWith          : P ∩ Q ⊆ R → Any P ∩ Any Q ⊆ Any R
  unzipWith        : P ⊆ Q ∩ R → Any P ⊆ Any Q ∩ Any R
  zip              : Any P ∩ Any Q ⊆ Any (P ∩ Q)
  unzip            : Any (P ∩ Q) ⊆ Any P ∩ Any Q
  irrelevant       : Irrelevant P → Irrelevant (Any P)
  satisfiable      : Satisfiable P → Satisfiable (Any P)
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  _<∣>_     : Maybe A → Maybe A → Maybe A
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  +-isMagma       : IsMagma _+_
  *-isMagma       : IsMagma _*_
  ⊔-isMagma       : IsMagma _⊔_
  ⊓-isMagma       : IsMagma _⊓_
  ⊔-isBand        : IsBand _⊔_
  ⊓-isBand        : IsBand _⊓_
  ⊔-isSemilattice : IsSemilattice _⊔_
  ⊓-isSemilattice : IsSemilattice _⊓_

  +-magma       : Magma 0ℓ 0ℓ
  *-magma       : Magma 0ℓ 0ℓ
  ⊔-magma       : Magma 0ℓ 0ℓ
  ⊓-magma       : Magma 0ℓ 0ℓ
  ⊔-band        : Band 0ℓ 0ℓ
  ⊓-band        : Band 0ℓ 0ℓ
  ⊔-semilattice : Semilattice 0ℓ 0ℓ
  ⊓-semilattice : Semilattice 0ℓ 0ℓ

  m≤n⇒m⊓o≤n : ∀ {m n} o → m ≤ n → m ⊓ o ≤ n
  m≤n⇒o⊓m≤n : ∀ {m n} o → m ≤ n → o ⊓ m ≤ n
  m<n⇒m⊓o<n : ∀ {m n} o → m < n → m ⊓ o < n
  m<n⇒o⊓m<n : ∀ {m n} o → m < n → o ⊓ m < n
  m≤n⊓o⇒m≤n : ∀ {m} n o → m ≤ n ⊓ o → m ≤ n
  m≤n⊓o⇒m≤o : ∀ {m} n o → m ≤ n ⊓ o → m ≤ o
  m<n⊓o⇒m<n : ∀ {m} n o → m < n ⊓ o → m < n
  m<n⊓o⇒m<o : ∀ {m} n o → m < n ⊓ o → m < o
  m≤n⇒m≤n⊔o : ∀ {m n} o → m ≤ n → m ≤ n ⊔ o
  m≤n⇒m≤o⊔n : ∀ {m n} o → m ≤ n → m ≤ o ⊔ n
  m<n⇒m<n⊔o : ∀ {m n} o → m < n → m < n ⊔ o
  m<n⇒m<o⊔n : ∀ {m n} o → m < n → m < o ⊔ n
  m⊔n≤o⇒m≤o : ∀ m n {o} → m ⊔ n ≤ o → m ≤ o
  m⊔n≤o⇒n≤o : ∀ m n {o} → m ⊔ n ≤ o → n ≤ o
  m⊔n<o⇒m<o : ∀ m n {o} → m ⊔ n < o → m < o
  m⊔n<o⇒n<o : ∀ m n {o} → m ⊔ n < o → n < o

  m≢0⇒suc[pred[m]]≡m : m ≢ 0 → suc (pred m) ≡ m
  ```

* Added new functions to `Data.Product.Relation.Pointwise.NonDependent`:
  ```agda
  <_,_>ₛ : A ⟶ B → A ⟶ C → A ⟶ (B ×ₛ C)
  proj₁ₛ : (A ×ₛ B) ⟶ A
  proj₂ₛ : (A ×ₛ B) ⟶ B
  swapₛ : (A ×ₛ B) ⟶ (B ×ₛ A)
  ```

* Added new functions to `Data.Rational`:
  ```agda
  norm-mkℚ : (n : ℤ) (d : ℕ) → d ≢0 → ℚ
  -_       : ℚ → ℚ
  1/_      : (p : ℚ) → .{n≢0 : ∣ ℚ.numerator p ∣ ≢0} → ℚ
  _*_      : ℚ → ℚ → ℚ
  _+_      : ℚ → ℚ → ℚ
  _-_      : ℚ → ℚ → ℚ
  _/_      : (p₁ p₂ : ℚ) → {n≢0 : ∣ ℚ.numerator p₂ ∣ ≢0} → ℚ
  show     : ℚ → String
  ```

* Added new proofs to `Data.Sign.Properties`:
  ```agda
  *-isMagma : IsMagma _*_
  *-magma   : Magma 0ℓ 0ℓ
  ```

* Added new functions to `Data.Sum.Base`:
  ```agda
  fromDec : Dec P → P ⊎ ¬ P
  toDec   : P ⊎ ¬ P → Dec P
  ```

* Added new functions to `Data.Sum.Relation.Pointwise`:
  ```agda
  inj₁ₛ : A ⟶ (A ⊎ₛ B)
  inj₂ₛ : B ⟶ (A ⊎ₛ B)
  [_,_]ₛ : (A ⟶ C) → (B ⟶ C) → (A ⊎ₛ B) ⟶ C
  swapₛ : (A ⊎ₛ B) ⟶ (B ⊎ₛ A)
  ```

* Added new function to `Data.These`:
  ```agda
  fromSum : A ⊎ B → These A B
  ```

* Added new proofs to `Data.Vec.Any.Properties`:
  ```agda
  lookup-index : (p : Any P xs) → P (lookup (index p) xs)

  lift-resp       : P Respects _≈_ → (Any P) Respects (Pointwise _≈_)
  here-injective  : here p ≡ here q → p ≡ q
  there-injective : there p ≡ there q → p ≡ q

  ¬Any[]  : ¬ Any P []
  ⊥↔Any⊥  : ⊥ ↔ Any (const ⊥) xs
  ⊥↔Any[] : ⊥ ↔ Any P []

  map-id : ∀ f → (∀ p → f p ≡ p) → ∀ p → Any.map f p ≡ p
  map-∘  : ∀ f g p → Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)

  swap       : Any (λ x → Any (x ∼_) ys) xs → Any (λ y → Any (_∼ y) xs) ys
  swap-there : ∀ p → swap (Any.map there p) ≡ there (swap p)
  swap-invol : ∀ p → swap (swap p) ≡ p
  swap↔      : Any (λ x → Any (x ∼_) ys) xs ↔ Any (λ y → Any (_∼ y) xs) ys

  Any-⊎⁺ : Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁻ : Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  ⊎↔     : (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs

  Any-×⁺ : Any P xs × Any Q ys → Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁻ : Any (λ x → Any (λ y → P x × Q y) ys) xs → Any P xs × Any Q ys

  singleton⁺            : P x → Any P [ x ]
  singleton⁻            : Any P [ x ] → P x
  singleton⁺∘singleton⁻ : singleton⁺ (singleton⁻ p) ≡ p
  singleton⁻∘singleton⁺ : singleton⁻ (singleton⁺ p) ≡ p
  singleton↔            : P x ↔ Any P [ x ]

  map⁺      : Any (P ∘ f) xs → Any P (map f xs)
  map⁻      : Any P (map f xs) → Any (P ∘ f) xs
  map⁺∘map⁻ : ∀ p → map⁺ (map⁻ p) ≡ p
  map⁻∘map⁺ : ∀ P p → map⁻ (map⁺ p) ≡ p
  map↔      : Any (P ∘ f) xs ↔ Any P (map f xs)

  ++⁺ˡ            : Any P xs → Any P (xs ++ ys)
  ++⁺ʳ            : Any P ys → Any P (xs ++ ys)
  ++⁻             : Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁺∘++⁻         : ∀ p → [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁻∘++⁺         : ∀ p → ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++-comm         : ∀ xs ys → Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm∘++-comm : ∀ p → ++-comm ys xs (++-comm xs ys p) ≡ p
  ++-insert       : ∀ xs → P x → Any P (xs ++ [ x ] ++ ys)
  ++↔             : (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔++           : ∀ xs ys → Any P (xs ++ ys) ↔ Any P (ys ++ xs)

  concat⁺         : Any (Any P) xss → Any P (concat xss)
  concat⁻         : Any P (concat xss) → Any (Any P) xss
  concat⁻∘++⁺ˡ    : ∀ xss p → concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
  concat⁻∘++⁺ʳ    : ∀ xs xss p → concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
  concat⁺∘concat⁻ : ∀ xss p → concat⁺ (concat⁻ xss p) ≡ p
  concat⁻∘concat⁺ : ∀ p → concat⁻ xss (concat⁺ p) ≡ p
  concat↔         : Any (Any P) xss ↔ Any P (concat xss)

  tabulate⁺ : ∀ i → P (f i) → Any P (tabulate f)
  tabulate⁻ : Any P (tabulate f) → ∃ λ i → P (f i)

  mapWith∈⁺ : ∀ f → (∃₂ λ x p → P (f p)) → Any P (mapWith∈ xs f)
  mapWith∈⁻ : ∀ xs f → Any P (mapWith∈ xs f) → ∃₂ λ x p → P (f p)
  mapWith∈↔ : (∃₂ λ x p → P (f p)) ↔ Any P (mapWith∈ xs f)

  toList⁺      : Any P xs → List.Any P (toList xs)
  toList⁻      : List.Any P (toList xs) → Any P xs
  fromList⁺    : List.Any P xs → Any P (fromList xs)
  fromList⁻    : Any P (fromList xs) → List.Any P xs

  ∷↔   : ∀ P → (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
  >>=↔ : Any (Any P ∘ f) xs ↔ Any P (xs >>= f)
  ```

* Added new functions to `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  fromAny : Any P xs → ∃ λ x → x ∈ xs × P x
  toAny   : x ∈ xs → P x → Any P xs
  ```

* Added new proofs to `Function.Related.TypeIsomorphisms`:
  ```agda
  ×-isMagma : ∀ k ℓ → IsMagma (Related ⌊ k ⌋) _×_
  ⊎-isMagma : ∀ k ℓ → IsMagma (Related ⌊ k ⌋) _⊎_

  ⊎-magma : Symmetric-kind → (ℓ : Level) → Semigroup _ _
  ×-magma : Symmetric-kind → (ℓ : Level) → Magma _ _
  ```

* Added new definitions to `Relation.Binary.PropositionalEquality`:
  - `_≡_↾¹_` equality of functions at a single point
  - `_≡_↾_` equality of functions at a subset of the domain

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  wlog : Total _R_ → Symmetric Q → (∀ a b → a R b → Q a b) → ∀ a b → Q a b
  ```

* Added new definitions to `Relation.Binary.Core`:
  ```agda
  Antisym R S E = ∀ {i j} → R i j → S j i → E i j
  Conn P Q = ∀ x y → P x y ⊎ Q y x
  ```

* Added new proofs to `Relation.Binary.Lattice`:
  ```agda
  Lattice.setoid        : Setoid c ℓ
  BoundedLattice.setoid : Setoid c ℓ
  ```

* Added new operations and proofs to `Relation.Binary.Properties.HeytingAlgebra`:
  ```agda
  y≤x⇨y            : y ≤ x ⇨ y
  ⇨-unit           : x ⇨ x ≈ ⊤
  ⇨-drop           : (x ⇨ y) ∧ y ≈ y
  ⇨-app            : (x ⇨ y) ∧ x ≈ y ∧ x
  ⇨-relax          : _⇨_ Preserves₂ (flip _≤_) ⟶ _≤_ ⟶ _≤_
  ⇨-cong           : _⇨_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ⇨-applyˡ         : w ≤ x → (x ⇨ y) ∧ w ≤ y
  ⇨-applyʳ         : w ≤ x → w ∧ (x ⇨ y) ≤ y
  ⇨-curry          : x ∧ y ⇨ z ≈ x ⇨ y ⇨ z
  ⇨ʳ-covariant     : (x ⇨_) Preserves _≤_ ⟶ _≤_
  ⇨ˡ-contravariant : (_⇨ x) Preserves (flip _≤_) ⟶ _≤_

  ¬_           : Op₁ Carrier
  x≤¬¬x        : x ≤ ¬ ¬ x
  de-morgan₁   : ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
  de-morgan₂-≤ : ¬ (x ∧ y) ≤ ¬ ¬ (¬ x ∨ ¬ y)
  de-morgan₂-≥ : ¬ ¬ (¬ x ∨ ¬ y) ≤ ¬ (x ∧ y)
  de-morgan₂   : ¬ (x ∧ y) ≈ ¬ ¬ (¬ x ∨ ¬ y)
  weak-lem     : ¬ ¬ (¬ x ∨ x) ≈ ⊤
  ```

* Added new proofs to `Relation.Binary.Properties.JoinSemilattice`:
  ```agda
  x≤y⇒x∨y≈y : x ≤ y → x ∨ y ≈ y
  ```

* Added new proofs to `Relation.Binary.Properties.Lattice`:
  ```agda
  ∧≤∨            : x ∧ y ≤ x ∨ y
  quadrilateral₁ : x ∨ y ≈ x → x ∧ y ≈ y
  quadrilateral₂ : x ∧ y ≈ y → x ∨ y ≈ x
  collapse₁      : x ≈ y → x ∧ y ≈ x ∨ y
  collapse₂      : x ∨ y ≤ x ∧ y → x ≈ y
  ```

* Added new proofs to `Relation.Binary.Properties.MeetSemilattice`:
  ```agda
  y≤x⇒x∧y≈y : y ≤ x → x ∧ y ≈ y
  ```

* Give `_Respectsʳ_`/`_Respectsˡ_` more general type, to support heterogenous relations.
  ```agda
  _Respectsʳ_ : REL A B ℓ₁ → Rel B ℓ₂ → Set _
  _Respectsˡ_ : REL A B ℓ₁ → Rel A ℓ₂ → Set _
  ```
