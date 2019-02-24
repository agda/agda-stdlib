Version TODO
============

The library has been tested using Agda version 2.5.4.1.

Important changes since 0.17:

Non-backwards compatible changes
--------------------------------

#### Extending the relation hierarchy for container datatypes

* This release has added many new relations over `List` (e.g. `First`,
  `Suffix`, `Prefix`, `Interleaving`) and it has become clear that the
  current hierarchy for relations in `List`,`Product`,`Sum`, `Table`
  and `Vec`is not deep enough.

* To address this the contents of `Data.X.Relation` have been moved to
  `Data.X.Relation.Binary` and new folders `Data.X.Relation.(Unary/Ternary)`
  have been created and `Data.X.(All/Any)` have been moved to
  `Data.X.Relation.Unary.(All/Any)`.

* The old modules still exist for backwards compatability but are deprecated.

#### Support for `--without-K`

* The `--without-K` flag has been enabled in as many files as possible. An
  attempt has been made to only do this in files that do not depend on
  any file in which this flag is not enabled.

* Agda uses different rules for the target universe of data types when
  the `--without-K` flag is used, and because of this a number of type
  families now target a possibly larger universe:
  - Codata.Delay.Bisimilarity                 : `Bisim`
  - Codata.Musical.Covec                      : `_≈_`, `_∈_`, `_⊑_`
  - Codata.Stream.Bisimilarity                : `Bisim`
  - Data.List.Relation.Binary.Equality.Setoid : `_≋_`
  - Data.List.Relation.Binary.Lex.NonStrict   : `Lex-<`, `Lex-≤`
  - Data.List.Relation.Binary.Lex.Strict      : `Lex-<`, `Lex-≤`
  - Data.List.Relation.Binary.Pointwise       : `Pointwise`
  - Data.List.Relation.Unary.All              : `All`
  - Data.Maybe                                : `Is-just`, `Is-nothing`
  - Data.Maybe.Relation.Unary.Any             : `Any`
  - Data.Maybe.Relation.Unary.All             : `All`
  - Data.Maybe.Relation.Binary.Pointwise      : `Pointwise`

* Because of this change the texts of some type signatures were changed
  (some inferred parts of other type signatures may also have changed):
  - Data.List.Relation.Binary.Equality.DecSetoid : `≋-decSetoid`
  - Data.Maybe.Relation.Binary.Pointwise         : `setoid`, `decSetoid`

* Some code that relies on the K rule or uses heterogeneous equality has
  been moved from the existing file `X` to a new file `X.WithK` file
  (e.g. from `Data.AVL.Indexed` to `Data.AVL.Indexed.WithK`). These are as follows:
  - Data.AVL.Indexed                                                 : `node-injective-bal, node-injectiveʳ, node-injectiveˡ`
  - Data.Container.Indexed                                           : `Eq, Map.composition, Map.identity, PlainMorphism.NT, PlainMorphism.Natural, PlainMorphism.complete, PlainMorphism.natural, PlainMorphism.∘-correct, setoid`
  - Data.Product.Properties                                          : `,-injectiveʳ`
  - Data.Product.Relation.Binary.Pointwise.Dependent                 : `Pointwise-≡⇒≡, ≡⇒Pointwise-≡, inverse, ↣`
  - Data.Vec.Properties                                              : `++-assoc, []=-irrelevance, foldl-cong, foldr-cong`
  - Data.Vec.Relation.Binary.Equality.Propositional                  : `≋⇒≅`
  - Data.W                                                           : `sup-injective₂`
  - Relation.Binary.Construct.Closure.Transitive                     : `∼⁺⟨⟩-injectiveʳ, ∼⁺⟨⟩-injectiveˡ`
  - Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties : `◅-injectiveʳ, ◅-injectiveˡ`
  - Relation.Binary.PropositionalEquality                            : `≡-irrelevance`
  (The name `↣` in Data.Product.Relation.Binary.Pointwise.Dependent` now refers to a new
  definition with another type signature.)

* Other code has been changed to avoid use of the K rule. As part of
  such changes the texts of the following type signatures have been
  changed:
  - Data.AVL.Indexed                                           : `node-injective-key`
  - Data.List.Relation.Binary.Sublist.Propositional.Properties : `∷⁻`
  - Data.Product.Relation.Binary.Pointwise.Dependent           : `↣`
  - Relation.Binary.PropositionalEquality                       : `≡-≟-identity`
  (The old definition of `↣` was moved to `Data.Product.Relation.Binary.Pointwise.Dependent.WithK`.)

* The definition `_≅⟨_⟩_` has been removed from `Relation.Binary.PropositionalEquality`.

* The following previously deprecated names have also been removed:
  - Data.Product.Relation.Binary.Pointwise.Dependent : `Rel↔≡`
  - Data.Vec.Properties                              : `proof-irrelevance-[]=`
  - Relation.Binary.PropositionalEquality            : `proof-irrelevance`

* Finally some new, supporting code has been added in the modules `Function.HalfAdjointEquivalence`
  and `Relation.Binary.PropositionalEquality`: `cong-id`, `cong-∘`,
  `cong-≡id`, `naturality`, `subst-application`, `subst-subst`,
  `subst-subst-sym`, `subst-sym-subst`, `subst-∘`, `trans-assoc`,
  `trans-reflʳ`, `trans-symʳ` and `trans-symˡ`.

#### Overhaul of `Data.Maybe`

* `Data.Maybe` has been split up into the standard hierarchy.

* Moved `Data.Maybe.Base`'s `Is-just`, `Is-nothing`, `to-witness`,
  and `to-witness-T` to `Data.Maybe` (they rely on `All` and `Any`
  which are now outside of `Data.Maybe.Base`).

* Moved `Data.Maybe.Base`'s `All` and `Data.Maybe`'s `allDec` to
  `Data.Maybe.Relation.Unary.All` and renamed some proofs:
  ```agda
  allDec ↦ dec
  ```

* Moved `Data.Maybe.Base`'s `Any` and `Data.Maybe`'s `anyDec` to
  `Data.Maybe.Relation.Unary.Any` and renamed some proofs:
  ```agda
  anyDec ↦ dec
  ```

* Created `Data.Maybe.Properties`, moved `Data.Maybe.Base`'s `just-injective`
  there and added new results.

* Moved `Data.Maybe`'s `Eq` to `Data.Maybe.Relation.Binary.Pointwise`, made the
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

#### Upgrade of all forms of Reasoning

* The core Reasoning modules have been renamed as follows:
  ```
  Relation.Binary.EqReasoning                 ↦ Relation.Binary.Reasoning.Setoid
  Relation.Binary.SetoidReasoning             ↦ Relation.Binary.Reasoning.MultiSetoid
  Relation.Binary.PreorderReasoning           ↦ Relation.Binary.Reasoning.Preorder
  Relation.Binary.PartialOrderReasoning       ↦ Relation.Binary.Reasoning.PartialOrder
  Relation.Binary.StrictPartialOrderReasoning ↦ Relation.Binary.Reasoning.StrictPartialOrder
  ```
  The old modules have been deprecated but still exist for backwards compatibility reasons.

* The way reasoning is implemented has been changed. In particular all of the above
  modules are specialised instances of the three modules
  `Relation.Binary.Reasoning.Base.(Single/Double/Triple)`. This means that if you have
  extended the reasoning modules yourself you may need to update the extensions.
  However all *uses* of the reasoning modules are fully backwards compatible.

* The new implementation allows the interleaving of both strict and non-strict links
  in proofs. For example where as before the following:
  ```agda
  begin
    a ≤⟨ x≤y ⟩
    b <⟨ y<z ⟩
    c ≤⟨ x≤y ⟩
    d ∎
  ```
  was not a valid proof that `a ≤ d` due to the `<` link in the middle, it is now accepted.

* The new implementation can now be used to prove both equalities and strict relations as
  well as the primary relation. To do so use the `begin-equality` and `begin-strict` combinators.
  For instance replacing `begin` with `begin-strict` in the example above:
  ```agda
  begin-strict
    a ≤⟨ x≤y ⟩
    b <⟨ y<z ⟩
    c ≤⟨ x≤y ⟩
    d ∎
  ```
  proves that `a < d` rather than `a ≤ d`.

* New symmetric equality combinators  `_≈˘⟨_⟩_` and `_≡˘⟨_⟩_` have been added. Consequently
  expressions of the form `x ≈⟨ sym y≈x ⟩ y` can be replaced with `x ≈˘⟨ y≈x ⟩ y`.

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

* The functions `(insert/union)With` now take a function of type
  `Maybe Val -> Val` rather than a value together with a merging function
  `Val -> Val -> Val` to handle the case where a value is already present
  at that key.

* Various functions have been made polymorphic which makes their biases
  & limitations clearer. e.g. we have:
  `unionWith : (V -> Maybe W -> W) -> Tree V -> Tree W -> Tree W`
  but ideally we would like to have:
  `unionWith : (These V W -> X) -> Tree V -> Tree W -> Tree X`

* Keys are now implemented via `Relation.(Binary/Nullary).Construct.AddExtrema`.

#### Change in implementation of binary relations for `Sum`

* The implementation of `Data.Sum.Relation.Binary.(Pointwise/LeftOrder)` have been altered
  to bring them in line with implementations of similar orders for other datatypes.
  Namely they are no longer specialised instances of some `Core` module.

* The constructor `₁∼₂` for `LeftOrder` no longer takes an argument of type `⊤`.

* The constructor `₁∼₁` and `₂∼₂` in `Pointwise` have been renamed `inj₁` and `inj₂`
  respectively. The old names still exist but have been deprecated.

#### New `Data.Sum/Product.Function` directories

* Various combinators for types of functions (injections, surjections, inverses etc.)
  over `Sum` and `Product` currently live in the `Data.(Product/Sum).Relation.Binary.Pointwise`
  modules. These are poorly placed as: a) the properties do not directly reference `Pointwise`
  and b) are very hard to locate.

* They have therefore been moved into the new `Data.(Product/Sum).Function` directory
  as follows:
  ```
  Data.Product.Relation.Binary.Pointwise.Dependent    ↦ Data.Product.Function.Dependent.Setoid
                                                      ↘ Data.Product.Function.Dependent.Propositional
  Data.Product.Relation.Binary.Pointwise.NonDependent ↦ Data.Product.Function.NonDependent.Setoid
                                                      ↘ Data.Product.Function.NonDependent.Propositional
  Data.Sum.Relation.Binary.Pointwise.Dependent        ↦ Data.Sum.Function.Setoid
                                                      ↘ Data.Sum.Function.Propositional
  ```
  All the proofs about `Pointwise` remain untouched.

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

* The proofs `toList⁺` and `toList⁻` in `Data.Vec.Relation.Unary.All.Properties` have been swapped
  as they were the opposite way round to similar properties in the rest of the library.

* Changed the type of `≡-≟-identity` to make use of the fact that equality
  being decidable implies UIP.

* Changed the implementation of _≟_ and _≤″?_ for natural numbers to use a (fast)
  boolean test.

List of new modules
-------------------

  ```
  Algebra.Construct.NaturalChoice.Min
  Algebra.Construct.NaturalChoice.Max

  Algebra.Properties.Semilattice

  Algebra.FunctionProperties.Consequences.Propositional

  Codata.Cowriter

  Codata.M.Properties
  Codata.M.Bisimilarity

  Data.Integer.Divisibility.Properties
  Data.Integer.Divisibility.Signed
  Data.Integer.DivMod

  Data.List.Relation.Unary.First
  Data.List.Relation.Unary.First.Properties
  Data.List.Relation.Binary.Prefix.Heterogeneous
  Data.List.Relation.Binary.Prefix.Heterogeneous.Properties
  Data.List.Relation.Binary.Suffix.Heterogeneous
  Data.List.Relation.Binary.Suffix.Heterogeneous.Properties
  Data.List.Relation.Ternary.Interleaving.Setoid
  Data.List.Relation.Ternary.Interleaving.Setoid.Properties
  Data.List.Relation.Ternary.Interleaving.Propositional
  Data.List.Relation.Ternary.Interleaving.Propositional.Properties

  Data.Maybe.Relation.Unary.All.Properties

  Data.These.Properties

  Data.Vec.Any.Properties
  Data.Vec.Membership.Setoid
  Data.Vec.Membership.DecSetoid
  Data.Vec.Membership.DecPropositional
  Data.Vec.Relation.Unary.Any.Properties

  Debug.Trace

  Function.Endomophism.Setoid
  Function.Endomophism.Propositional
  Function.HalfAdjointEquivalence

  Relation.Binary.Construct.Add.Extrema.Equality
  Relation.Binary.Construct.Add.Extrema.Strict
  Relation.Binary.Construct.Add.Extrema.NonStrict
  Relation.Binary.Construct.Add.Infimum.Equality
  Relation.Binary.Construct.Add.Infimum.Strict
  Relation.Binary.Construct.Add.Infimum.NonStrict
  Relation.Binary.Construct.Add.Supremum.Equality
  Relation.Binary.Construct.Add.Supremum.Strict
  Relation.Binary.Construct.Add.Supremum.NonStrict
  Relation.Binary.Construct.Add.Point.Equality
  Relation.Binary.Construct.Intersection
  Relation.Binary.Construct.Union
  Relation.Binary.Construct.NaturalOrder.Left
  Relation.Binary.Construct.NaturalOrder.Right

  Relation.Binary.Properties.BoundedLattice

  Relation.Nullary.Construct.Add.Extrema
  Relation.Nullary.Construct.Add.Infimum
  Relation.Nullary.Construct.Add.Supremum
  Relation.Nullary.Construct.Add.Point
  ```

Deprecated features
-------------------

* In `Data.Bool.Properties`:
  ```agda
  T-irrelevance ↦ T-irrelevant
  ```

* In `Data.Fin.Properties`:
  ```agda
  ≤-irrelevance ↦ ≤-irrelevant
  <-irrelevance ↦ <-irrelevant
  ```

* In `Data.Integer.Properties`:
  ```agda
  ≰→>           ↦ ≰⇒>
  ≤-irrelevance ↦ ≤-irrelevant
  <-irrelevance ↦ <-irrelevant
  ```

* In `Data.List.Relation.Binary.Pointwise`:
  ```
  decidable-≡   ↦ Data.List.Properties.≡-dec
  ```

* In `Data.Nat.Properties`:
  ```agda
  ≤-irrelevance ↦ ≤-irrelevant
  <-irrelevance ↦ <-irrelevant
  ```

* In `Data.Rational`:
  ```agda
  drop-*≤*
  ≃⇒≡
  ≡⇒≃
  ```
  (moved to `Data.Rational.Properties`)

* In `Data.Rational.Properties`:
  ```agda
  ≤-irrelevance ↦ ≤-irrelevant
  ```

* In `Data.Vec.Properties.WithK`:
  ```agda
  []=-irrelevance ↦ []=-irrelevant
  ```

* In `Relation.Binary.HeterogeneousEquality`:
  ```agda
  ≅-irrelevance                ↦ ≅-irrelevant
  ≅-heterogeneous-irrelevance  ↦ ≅-heterogeneous-irrelevant
  ≅-heterogeneous-irrelevanceˡ ↦ ≅-heterogeneous-irrelevantˡ
  ≅-heterogeneous-irrelevanceʳ ↦ ≅-heterogeneous-irrelevantʳ
  ```

* In `Relation.Binary.PropositionalEquality.WithK`:
  ```agda
  ≡-irrelevance ↦ ≡-irrelevant
  ```

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
  ∧-semilattice   : Semilattice l₁ l₂
  ∨-isSemilattice : IsSemilattice _≈_ _∨_
  ∨-semilattice   : Semilattice l₁ l₂
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
  splitAt-map             : splitAt n (map f xs) ≡ map (map f) (map f) (splitAt n xs)
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

  T?      : Decidable T
  T?-diag : T b → True (T? b)
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

* Added new operations to `Data.List.Relation.Unary.All`:
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
  A generalization of single point overwrite `_[_]≔_`
  to single-point modification `_[_]%=_`
  (alias with different argument order: `updateAt`):
  ```agda
  _[_]%=_   : Vec A n → Fin n → (A → A) → Vec A n
  updateAt  : Fin n → (A → A) → Vec A n → Vec A n
  ```

* Added new proofs to `Data.List.Relation.Binary.Equality.DecPropositional`:
  ```agda
  _≡?_        : Decidable (_≡_ {A = List A})
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  respects : P Respects _≈_ → (All P) Respects _≋_
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
  _∷=_ : x ∈ xs → A → List A
  _─_  : (xs : List A) → x ∈ xs → List A
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
  ≡-dec : Decidable _≡_ → Decidable {A = List A} _≡_

  ++-isMagma : IsMagma _++_

  length-%=  : length (xs [ k ]%= f) ≡ length xs
  length-∷=  : length (xs [ k ]∷= v) ≡ length xs
  map-∷=     : map f (xs [ k ]∷= v) ≡ map f xs [ cast eq k ]∷= f v
  length-─   : length (xs ─ k) ≡ pred (length xs)
  map-─      : map f (xs ─ k) ≡ map f xs ─ cast eq k

  length-applyUpTo     : length (applyUpTo     f n) ≡ n
  length-applyDownFrom : length (applyDownFrom f n) ≡ n
  length-upTo          : length (upTo            n) ≡ n
  length-downFrom      : length (downFrom        n) ≡ n

  lookup-applyUpTo     : lookup (applyUpTo     f n) i ≡ f (toℕ i)
  lookup-applyDownFrom : lookup (applyDownFrom f n) i ≡ f (n ∸ (suc (toℕ i)))
  lookup-upTo          : lookup (upTo            n) i ≡ toℕ i
  lookup-downFrom      : lookup (downFrom        n) i ≡ n ∸ (suc (toℕ i))

  map-tabulate : map f (tabulate g) ≡ tabulate (f ∘ g)
  ```

* Added new proofs to `Data.List.Relation.Binary.Permutation.Inductive.Properties`:
  ```agda
  ++-isMagma : IsMagma _↭_ _++_
  ++-magma   : Magma _ _
  ```

* Added new proofs to `Data.Maybe.Relation.Unary.All`:
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

* Added new proofs to `Data.Maybe.Relation.Unary.Any`:
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

* Added new proof to `Data.Maybe.Properties`:
  ```agda
  ≡-dec : Decidable _≡_ → Decidable {A = Maybe A} _≡_

* Added new proof to `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  reflexive : _≡_ ⇒ R → _≡_ ⇒ Pointwise R
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

  +-cancelˡ-< : LeftCancellative _<_ _+_
  +-cancelʳ-< : RightCancellative _<_ _+_
  +-cancel-<  : Cancellative _<_ _+_

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

  ≡ᵇ⇒≡         : T (m ≡ᵇ n) → m ≡ n
  ≡⇒≡ᵇ         : m ≡ n → T (m ≡ᵇ n)
  ≡-irrelevant : Irrelevant {A = ℕ} _≡_
  ≟-diag       : (eq : m ≡ n) → (m ≟ n) ≡ yes eq

  <ᵇ⇒<″  : T (m <ᵇ n) → m <″ n
  <″⇒<ᵇ  : m <″ n → T (m <ᵇ n)

  m<ᵇn⇒1+m+[n-1+m]≡n : T (m <ᵇ n) → suc m + (n ∸ suc m) ≡ n
  m<ᵇ1+m+n           : T (m <ᵇ suc (m + n))

  ≤″-irrelevant : Irrelevant _≤″_
  ≥″-irrelevant : Irrelevant _≥″_
  <″-irrelevant : Irrelevant _<″_
  >″-irrelevant : Irrelevant _>″_
  ```

* Added new proof to `Data.Product.Properties.WithK`:
  ```agda
  ,-injective : (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ≡-dec       : Decidable _≡_ → (∀ {a} → Decidable {A = B a} _≡_) → Decidable {A = Σ A B} _≡_
  ```

* Added new functions to `Data.Product.Relation.Binary.Pointwise.NonDependent`:
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

* Added new proof to `Data.Sum.Properties`:
  ```agda
  ≡-dec : Decidable _≡_ → Decidable _≡_ → Decidable {A = A ⊎ B} _≡_
  ```

* Added new functions to `Data.Sum.Relation.Binary.Pointwise`:
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

* Added new proofs to `Data.Vec.Relation.Unary.Any.Properties`:
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

* Added new proof to `Data.Vec.Properties`:
  ```agda
  ≡-dec : Decidable _≡_ → ∀ {n} → Decidable {A = Vec A n} _≡_
  ```

* Added new proofs to `Function.Related.TypeIsomorphisms`:
  ```agda
  ×-isMagma : ∀ k ℓ → IsMagma (Related ⌊ k ⌋) _×_
  ⊎-isMagma : ∀ k ℓ → IsMagma (Related ⌊ k ⌋) _⊎_

  ⊎-magma : Symmetric-kind → (ℓ : Level) → Semigroup _ _
  ×-magma : Symmetric-kind → (ℓ : Level) → Magma _ _
  ```

* Added new definitions to `Relation.Binary.PropositionalEquality`:
  ```agda
  module Constant⇒UIP
  module Decidable⇒UIP
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  wlog : Total _R_ → Symmetric Q → (∀ a b → a R b → Q a b) → ∀ a b → Q a b
  ```

* Added new definitions to `Relation.Binary.Core`:
  ```agda
  Antisym R S E = ∀ {i j} → R i j → S j i → E i j
  Conn P Q      = ∀ x y → P x y ⊎ Q y x
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

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  reverseAcc⁺ : Pointwise R a x → Pointwise R b y → Pointwise R (reverseAcc a b) (reverseAcc x y)
  reverse⁺    : Pointwise R as bs → Pointwise R (reverse as) (reverse bs)
  map⁺        : Pointwise (λ a b → R (f a) (g b)) as bs → Pointwise R (map f as) (map g bs)
  map⁻        : Pointwise R (map f as) (map g bs) → Pointwise (λ a b → R (f a) (g b)) as bs
  filter⁺     : Pointwise R as bs → Pointwise R (filter P? as) (filter Q? bs)
  replicate⁺  : R a b → Pointwise R (replicate n a) (replicate n b)
  irrelevant  : Irrelevant R → Irrelevant (Pointwise R)
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  length-tabulate : ∀ {n} → (f : Fin n → A) → length (tabulate f) ≡ n
  lookup-tabulate : ∀ {n} → (f : Fin n → A) →
                    ∀ i → let i′ = cast (sym (length-tabulate f)) i
                          in lookup (tabulate f) i′ ≡ f i
  ```
