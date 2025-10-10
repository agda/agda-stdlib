Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

* Fix a type error in `README.Data.Fin.Relation.Unary.Top` within the definition of `>-weakInduction`.

* Fix a typo in `Algebra.Morphism.Construct.DirectProduct`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* The type of `Relation.Nullary.Negation.Core.contradiction-irr` has been further
  weakened so that the negated hypothesis `¬ A` is marked as irrelevant. This is
  safe to do, in view of `Relation.Nullary.Recomputable.Properties.¬-recompute`.
  Furthermore, because the *eager* insertion of implicit arguments during type
  inference interacts badly with `contradiction`, we introduce an explicit name
  `contradiction′` for its `flip`ped version.

* Refactored usages of `+-∸-assoc 1` to `∸-suc` in:
  ```agda
  README.Data.Fin.Relation.Unary.Top
  Algebra.Properties.Semiring.Binomial
  Data.Fin.Subset.Properties
  Data.Nat.Binary.Subtraction
  Data.Nat.Combinatorics
  ```

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeSemigroup`:
  ```agda
  interchange  ↦   medial
  ```

New modules
-----------

* `Algebra.Properties.BooleanRing`.

* `Algebra.Properties.BooleanSemiring`.

* `Algebra.Properties.CommutativeRing`.

* `Algebra.Properties.Semiring`.

* `Data.List.Relation.Binary.Permutation.Algorithmic{.Properties}` for the Choudhury and Fiore definition of permutation, and its equivalence with `Declarative` below.

* `Data.List.Relation.Binary.Permutation.Declarative{.Properties}` for the least congruence on `List` making `_++_` commutative, and its equivalence with the `Setoid` definition.

* `Effect.Monad.Random` and `Effect.Monad.Random.Instances` for an mtl-style randomness monad constraint.

Additions to existing modules
-----------------------------

* In `Algebra.Bundles`:
  ```agda
  record BooleanSemiring _ _ : Set _
  record BooleanRing _ _     : Set _
  ```

* In `Algebra.Consequences.Propositional`:
  ```agda
  binomial-expansion : Associative _∙_ → _◦_ DistributesOver _∙_ →
    ∀ w x y z → ((w ∙ x) ◦ (y ∙ z)) ≡ ((((w ◦ y) ∙ (w ◦ z)) ∙ (x ◦ y)) ∙ (x ◦ z))
  ```

* In `Algebra.Consequences.Setoid`:
  ```agda
  binomial-expansion : Congruent₂ _∙_  → Associative _∙_ → _◦_ DistributesOver _∙_ →
    ∀ w x y z → ((w ∙ x) ◦ (y ∙ z)) ≈ ((((w ◦ y) ∙ (w ◦ z)) ∙ (x ◦ y)) ∙ (x ◦ z))
  ```

* In `Algebra.Lattice.Properties.BooleanAlgebra.XorRing`:
  ```agda
  ⊕-∧-isBooleanRing : IsBooleanRing _⊕_ _∧_ id ⊥ ⊤
  ⊕-∧-booleanRing   : BooleanRing _ _
  ```

* In `Algebra.Properties.RingWithoutOne`:
  ```agda
  [-x][-y]≈xy : ∀ x y → - x * - y ≈ x * y
  ```

* In `Algebra.Structures`:
  ```agda
  record IsBooleanSemiring + * 0# 1# : Set _
  record IsBooleanRing + * - 0# 1# : Set _
  ```
  NB. the latter is based on `IsCommutativeRing`, with the former on `IsSemiring`.

* In `Data.Fin.Permutation.Components`:
  ```agda
  transpose[i,i,j]≡j  : (i j : Fin n) → transpose i i j ≡ j
  transpose[i,j,j]≡i  : (i j : Fin n) → transpose i j j ≡ i
  transpose[i,j,i]≡j  : (i j : Fin n) → transpose i j i ≡ j
  transpose-transpose : transpose i j k ≡ l → transpose j i l ≡ k
  ```

* In `Data.Fin.Properties`:
  ```agda
  ≡-irrelevant : Irrelevant {A = Fin n} _≡_
  ≟-≡          : (eq : i ≡ j) → (i ≟ j) ≡ yes eq
  ≟-≡-refl     : (i : Fin n) → (i ≟ i) ≡ yes refl
  ≟-≢          : (i≢j : i ≢ j) → (i ≟ j) ≡ no i≢j
  inject-<     : inject j < i

  record Least⟨_⟩ (P : Pred (Fin n) p) : Set p where
    constructor least
    field
      witness : Fin n
      example : P witness
      minimal : ∀ {j} → .(j < witness) → ¬ P j

  record Least⟨¬_⟩ (P : Pred (Fin n) p) : Set p where
    constructor μ
    field
      witness : Fin n
      .contra : ¬ P witness
      minimal : ∀ {j} → .(j < witness) → P j

  search-least⟨¬_⟩ : Decidable P → Π[ P ] ⊎ Least⟨¬ P ⟩
  ¬¬least⇒least    : Decidable P → Least⟨¬ ∁ P ⟩ → Least⟨ P ⟩
  ```

* In `Data.Nat.ListAction.Properties`
  ```agda
  *-distribˡ-sum : ∀ m ns → m * sum ns ≡ sum (map (m *_) ns)
  *-distribʳ-sum : ∀ m ns → sum ns * m ≡ sum (map (_* m) ns)
  ^-distribʳ-product : ∀ m ns → product ns ^ m ≡ product (map (_^ m) ns)
  ```

* In `Data.Nat.Properties`:
  ```agda
  ≟-≢   : (m≢n : m ≢ n) → (m ≟ n) ≡ no m≢n
  ∸-suc : m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
  ^-distribʳ-* : ∀ m n o → (n * o) ^ m ≡ n ^ m * o ^ m
  ```

* In `Data.Vec.Properties`:
  ```agda
  updateAt-take : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                  updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)

  truncate-zipWith : (f : A → B → C) (m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) →
                    truncate m≤n (zipWith f xs ys) ≡ zipWith f (truncate m≤n xs) (truncate m≤n ys)

  truncate-zipWith-truncate : (f : A → B → C) (m≤n : m ≤ n) (n≤o : n ≤ o) (xs : Vec A o) (ys : Vec B n) →
                              truncate m≤n (zipWith f (truncate n≤o xs) ys) ≡
                              zipWith f (truncate (≤-trans m≤n n≤o) xs) (truncate m≤n ys)

  truncate-updateAt : (m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) (f : A → A) →
                      updateAt (truncate m≤n xs) i f ≡
                      truncate m≤n (updateAt xs (inject≤ i m≤n) f)

  updateAt-truncate : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                      updateAt (truncate (m≤m+n m n) xs) i f ≡
                      truncate (m≤m+n m n) (updateAt xs (inject≤ i (m≤m+n m n)) f)

  map-truncate : (f : A → B) (m≤n : m ≤ n) (xs : Vec A n) →
                map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)

  padRight-lookup : (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) → lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i

  padRight-map : (f : A → B) (m≤n : m ≤ n) (a : A) (xs : Vec A m) → map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)

  padRight-zipWith : (f : A → B → C) (m≤n : m ≤ n) (a : A) (b : B) (xs : Vec A m) (ys : Vec B m) →
                   zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡ padRight m≤n (f a b) (zipWith f xs ys)

  padRight-zipWith₁ : (f : A → B → C) (o≤m : o ≤ m) (m≤n : m ≤ n) (a : A) (b : B) (xs : Vec A m) (ys : Vec B o) →
                    zipWith f (padRight m≤n a xs) (padRight (≤-trans o≤m m≤n) b ys) ≡
                    padRight m≤n (f a b) (zipWith f xs (padRight o≤m b ys))

  padRight-take : (m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) → take m (cast n≡m+o (padRight m≤n a xs)) ≡ xs

  padRight-drop : (m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) → drop m (cast n≡m+o (padRight m≤n a xs)) ≡ replicate o a

  padRight-updateAt : (m≤n : m ≤ n) (x : A) (xs : Vec A m) (f : A → A) (i : Fin m) →
                    updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡ padRight m≤n x (updateAt xs i f)
  ```

* In `Relation.Nullary.Negation.Core`
  ```agda
  ¬¬-η           : A → ¬ ¬ A
  contradiction′ : ¬ A → A → Whatever
  ```

* In `System.Random`:
  ```agda
  randomIO : IO Bool
  randomRIO : RandomRIO {A = Bool} _≤_
  ```
