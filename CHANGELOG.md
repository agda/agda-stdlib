Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

* Fix a type error in `README.Data.Fin.Relation.Unary.Top` within the definition of `>-weakInduction`.

* Fix a typo in `Algebra.Morphism.Construct.DirectProduct`.

* Fix a typo in `Data.Rational.Properties`: `nonPos*nonPos⇒nonPos` erroneously named,
  corrected to `nonPos*nonPos⇒nonNeg`.

* Fix a typo in `Function.Construct.Constant`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* The function `Data.Nat.LCG.step` is now a manifest field of the record type
  `Generator`, as per the discussion on #2936 and upstream issues/PRs. This is
  consistent with a minimal API for such LCGs, and should be backwards compatible.

* The types of `Data.Vec.Base.{truncate|padRight}` have been weakened so
  that the argument of type `m ≤ n` is marked as irrelevant. This should be
  backwards compatible, but does change the intensional behaviour of these
  functions to be more eager, because no longer blocking on pattern matching
  on that argument. Corresponding changes have been made to the types of their
  properties (and their proofs). In particular, `truncate-irrelevant` is now
  deprecated, because definitionally trivial.

* The function `Data.Vec.Functional.map` is now marked with the `INLINE` pragma.
  This is consistent with the inlining of `Function.Base._∘_` for which it is
  an alias, and should be backwards compatible, but does improve the behaviour
  of the termination checker for some `Vector`-defined operations.

* The type of `Relation.Nullary.Negation.Core.contradiction-irr` has been further
  weakened so that the negated hypothesis `¬ A` is marked as irrelevant. This is
  safe to do, in view of `Relation.Nullary.Recomputable.Properties.¬-recompute`.
  Furthermore, because the *eager* insertion of implicit arguments during type
  inference interacts badly with `contradiction`, we introduce an explicit name
  `contradiction′` for its `flip`ped version.

* More generally, `Relation.Nullary.Negation.Core` has been reorganised into two
  parts: the first concerns definitions and properties of negation considered as
  a connective in *minimal logic*; the second making actual use of *ex falso* in
  the form of `Data.Empty.⊥-elim`.

* Refactored usages of `+-∸-assoc 1` to `∸-suc` in:
  ```agda
  README.Data.Fin.Relation.Unary.Top
  Algebra.Properties.Semiring.Binomial
  Data.Fin.Subset.Properties
  Data.Nat.Binary.Subtraction
  Data.Nat.Combinatorics
  ```

* In `Data.Vec.Relation.Binary.Pointwise.{Inductive,Extensional}`, the types of
  `refl`, `sym`, and `trans` have been weakened to allow relations of different
  levels to be used.

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeSemigroup`:
  ```agda
  interchange  ↦   medial
  ```

* In `Algebra.Properties.Monoid`:
  ```agda
  ε-comm  ↦   ε-central
  ```

* In `Data.Fin.Properties`:
  ```agda
  ¬∀⟶∃¬-smallest  ↦   ¬∀⇒∃¬-smallest
  ¬∀⟶∃¬-          ↦   ¬∀⇒∃¬
  ```

* In `Data.Rational.Properties`:
  ```agda
  nonPos*nonPos⇒nonPos  ↦  nonPos*nonPos⇒nonNeg
  ```

* In `Data.Vec.Properties`:
  ```agda
  truncate-irrelevant  ↦  Relation.Binary.PropositionalEquality.Core.refl
  ```

* In `Relation.Nullary.Decidable.Core`:
  ```agda
  ⊤-dec     ↦   ⊤?
  ⊥-dec     ↦   ⊥?
  _×-dec_  ↦   _×?_
  _⊎-dec_  ↦   _⊎?_
  _→-dec_  ↦   _→?_

* In `Relation.Nullary.Negation`:
  ```agda
  ∃⟶¬∀¬  ↦   ∃⇒¬∀¬
  ∀⟶¬∃¬  ↦   ∀⇒¬∃¬
  ¬∃⟶∀¬  ↦   ¬∃⇒∀¬
  ∀¬⟶¬∃  ↦   ∀¬⇒¬∃
  ∃¬⟶¬∀  ↦   ∃¬⇒¬∀
  ```

New modules
-----------

* `Algebra.Construct.Sub.Group` for the definition of subgroups.

* `Algebra.Module.Construct.Sub.Bimodule` for the definition of subbimodules.

* `Algebra.Properties.BooleanRing`.

* `Algebra.Properties.BooleanSemiring`.

* `Algebra.Properties.CommutativeRing`.

* `Algebra.Properties.Semiring`.

* `Data.List.Fresh.Membership.DecSetoid`.

* `Data.List.Relation.Binary.Permutation.Algorithmic{.Properties}` for the Choudhury and Fiore definition of permutation, and its equivalence with `Declarative` below.

* `Data.List.Relation.Binary.Permutation.Declarative{.Properties}` for the least congruence on `List` making `_++_` commutative, and its equivalence with the `Setoid` definition.

* `Effect.Monad.Random` and `Effect.Monad.Random.Instances` for an mtl-style randomness monad constraint.

* Various additions over non-empty lists:
  ```
  Data.List.NonEmpty.Relation.Binary.Pointwise
  Data.List.NonEmpty.Relation.Unary.Any
  Data.List.NonEmpty.Membership.Propositional
  Data.List.NonEmpty.Membership.Setoid
  ```

* `Relation.Binary.Morphism.Construct.On`: given a relation `_∼_` on `B`,
  and a function `f : A → B`, construct the canonical `IsRelMonomorphism`
  between `_∼_ on f` and `_∼_`, witnessed by `f` itself.

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
  identity⇒central   : Identity e _∙_ → Central _∙_ e
  zero⇒central       : Zero e _∙_ → Central _∙_ e
  ```

* In `Algebra.Consequences.Setoid`:
  ```agda
  sel⇒idem : Selective _∙_ → Idempotent _∙_
  binomial-expansion : Congruent₂ _∙_  → Associative _∙_ → _◦_ DistributesOver _∙_ →
    ∀ w x y z → ((w ∙ x) ◦ (y ∙ z)) ≈ ((((w ◦ y) ∙ (w ◦ z)) ∙ (x ◦ y)) ∙ (x ◦ z))
  identity⇒central   : Identity e _∙_ → Central _∙_ e
  zero⇒central       : Zero e _∙_ → Central _∙_ e
  ```

* In `Algebra.Definitions`:
  ```agda
  Central : Op₂ A → A → Set _
  ```

* In `Algebra.Definitions.RawMonoid` action of a Boolean on a RawMonoid:
  ```agda
  _?>₀_  : Bool → Carrier → Carrier
  _?>_∙_ : Bool → Carrier → Carrier → Carrier
  ```

* In `Algebra.Lattice.Properties.BooleanAlgebra.XorRing`:
  ```agda
  ⊕-∧-isBooleanRing : IsBooleanRing _⊕_ _∧_ id ⊥ ⊤
  ⊕-∧-booleanRing   : BooleanRing _ _
  ```

* In `Algebra.Module.Properties.LeftModule`:
  ```agda
  -1#*ₗm≈-ᴹm : ∀ m → - 1# *ₗ m ≈ᴹ -ᴹ m
  -‿distrib-*ₗ : ∀ r m → - r *ₗ m ≈ᴹ -ᴹ (r *ₗ m)
  -ᴹ‿distrib-*ₗ : ∀ r m → r *ₗ (-ᴹ m) ≈ᴹ -ᴹ (r *ₗ m)
  ```

* In `Algebra.Module.Properties.RightModule`:
  ```agda
  -1#*ₗm≈-ᴹm : m*ᵣ-1#≈-ᴹm : ∀ m → m *ᵣ (- 1#) ≈ᴹ -ᴹ m
  -‿distrib-*ᵣ : ∀ m r → m *ᵣ (- r) ≈ᴹ -ᴹ (m *ᵣ r)
  -ᴹ‿distrib-*ᵣ : ∀ m r → (-ᴹ m) *ᵣ r ≈ᴹ -ᴹ (m *ᵣ r)
  ```

* In `Algebra.Properties.Monoid.Mult` properties of the Boolean action on a RawMonoid:
  ```agda
  ?>₀-homo-true  : true ?>₀ x ≈ x
  ?>₀-assocˡ     : b ?>₀ b′ ?>₀ x ≈ (b ∧ b′) ?>₀ x
  b?>x∙y≈b?>₀x+y : b ?> x ∙ y ≈ (b ?>₀ x) + y
  b?>₀x≈b?>x∙0   : b ?>₀ x ≈ b ?> x ∙ 0#
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

  search-least⟨_⟩  : Decidable P → Π[ ∁ P ] ⊎ Least⟨ P ⟩
  search-least⟨¬_⟩ : Decidable P → Π[ P ] ⊎ Least⟨ ∁ P ⟩
  ```

* In `Data.List.NonEmpty.Relation.Unary.All`:
  ```
  map : P ⊆ Q → All P xs → All Q xs
  ```

* In `Data.Nat.Logarithm`
  ```agda
  2^⌊log₂n⌋≤n : ∀ n .{{ _ : NonZero n }} → 2 ^ ⌊log₂ n ⌋ ≤ n
  n≤2^⌈log₂n⌉ : ∀ n → n ≤ 2 ^ ⌈log₂ n ⌉
  ```

* In `Data.Nat.Logarithm.Core`
  ```agda
  2^⌊log2n⌋≤n : ∀ n .{{_ : NonZero n}} → (acc : Acc _<_ n) → 2 ^ (⌊log2⌋ n acc) ≤ n
  n≤2^⌈log2n⌉ : ∀ n → (acc : Acc _<_ n) → n ≤ 2 ^ (⌈log2⌉ n acc)
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
  2*suc[n]≡2+n+n : ∀ n → 2 * (suc n) ≡ 2 + (n + n)
  ```

* In `Data.Product.Properties`:
  ```agda
  swap-↔ : (A × B) ↔ (B × A)
  _,′-↔_ : A ↔ C → B ↔ D → (A × B) ↔ (C × D)
  ```

* In `Data.Rational.Properties`:
  ```agda
  ≤⇒≯           : _≤_ ⇒ _≯_
  p*q≡0⇒p≡0∨q≡0 : p * q ≡ 0ℚ → p ≡ 0ℚ ⊎ q ≡ 0ℚ
  p*q≢0⇒p≢0     : p * q ≢ 0ℚ → p ≢ 0ℚ
  p*q≢0⇒q≢0     : p * q ≢ 0ℚ → q ≢ 0ℚ
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```agda
  p*q≃0⇒p≃0∨q≃0 : p * q ≃ 0ℚᵘ → p ≃ 0ℚᵘ ⊎ q ≃ 0ℚᵘ
  p*q≄0⇒p≄0     : p * q ≄ 0ℚᵘ → p ≄ 0ℚᵘ
  p*q≢0⇒q≢0     : p * q ≄ 0ℚᵘ → q ≄ 0ℚᵘ
  ```

* In `Data.Vec.Properties`:
  ```agda
  map-removeAt : ∀ (f : A → B) (xs : Vec A (suc n)) (i : Fin (suc n)) →
                 map f (removeAt xs i) ≡ removeAt (map f xs) i

  updateAt-take : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                  updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)

  truncate-zipWith : (f : A → B → C) .(m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) →
                     truncate m≤n (zipWith f xs ys) ≡ zipWith f (truncate m≤n xs) (truncate m≤n ys)

  truncate-zipWith-truncate : (f : A → B → C) .(m≤n : m ≤ n) .(n≤o : n ≤ o)
                              (xs : Vec A o) (ys : Vec B n) →
                              truncate m≤n (zipWith f (truncate n≤o xs) ys) ≡
                              zipWith f (truncate (≤-trans m≤n n≤o) xs) (truncate m≤n ys)

  truncate-updateAt : .(m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) (f : A → A) →
                      updateAt (truncate m≤n xs) i f ≡
                      truncate m≤n (updateAt xs (inject≤ i m≤n) f)

  updateAt-truncate : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                      updateAt (truncate (m≤m+n m n) xs) i f ≡
                      truncate (m≤m+n m n) (updateAt xs (inject≤ i (m≤m+n m n)) f)

  map-truncate : (f : A → B) .(m≤n : m ≤ n) (xs : Vec A n) →
                 map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)

  padRight-lookup : .(m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) →
                    lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i

  padRight-map : (f : A → B) .(m≤n : m ≤ n) (a : A) (xs : Vec A m) →
                 map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)

  padRight-zipWith : (f : A → B → C) .(m≤n : m ≤ n) (a : A) (b : B)
                     (xs : Vec A m) (ys : Vec B m) →
                     zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡
                     padRight m≤n (f a b) (zipWith f xs ys)

  padRight-zipWith₁ : (f : A → B → C) .(o≤m : o ≤ m) .(m≤n : m ≤ n) (a : A) (b : B)
                      (xs : Vec A m) (ys : Vec B o) →
                      zipWith f (padRight m≤n a xs) (padRight (≤-trans o≤m m≤n) b ys) ≡
                      padRight m≤n (f a b) (zipWith f xs (padRight o≤m b ys))

  padRight-take : .(m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) →
                  take m (cast n≡m+o (padRight m≤n a xs)) ≡ xs

  padRight-drop : .(m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) →
                  drop m (cast n≡m+o (padRight m≤n a xs)) ≡ replicate o a

  padRight-updateAt : .(m≤n : m ≤ n) (x : A) (xs : Vec A m) (f : A → A) (i : Fin m) →
                      updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡
                      padRight m≤n x (updateAt xs i f)
  ```

* In `Relation.Binary.Construct.Add.Extrema.NonStrict`:
  ```agda
  ≤±-respˡ-≡ : _≤±_ Respectsˡ _≡_
  ≤±-respʳ-≡ : _≤±_ Respectsʳ _≡_
  ≤±-resp-≡ : _≤±_ Respects₂ _≡_
  ≤±-respˡ-≈± : _≤_ Respectsˡ _≈_ → _≤±_ Respectsˡ _≈±_
  ≤±-respʳ-≈± : _≤_ Respectsʳ _≈_ → _≤±_ Respectsʳ _≈±_
  ≤±-resp-≈± : _≤_ Respects₂ _≈_ → _≤±_ Respects₂ _≈±_
  ```

* In `Relation.Binary.Construct.Add.Infimum.NonStrict`:
  ```agda
  ≤₋-respˡ-≡ : _≤₋_ Respectsˡ _≡_
  ≤₋-respʳ-≡ : _≤₋_ Respectsʳ _≡_
  ≤₋-resp-≡ : _≤₋_ Respects₂ _≡_
  ≤₋-respˡ-≈₋ : _≤_ Respectsˡ _≈_ → _≤₋_ Respectsˡ _≈₋_
  ≤₋-respʳ-≈₋ : _≤_ Respectsʳ _≈_ → _≤₋_ Respectsʳ _≈₋_
  ≤₋-resp-≈₋ : _≤_ Respects₂ _≈_ → _≤₋_ Respects₂ _≈₋_
  ```

* In `Relation.Binary.Construct.Add.Extrema.Supremum.NonStrict`:
  ```agda
  ≤⁺-respˡ-≡ : _≤⁺_ Respectsˡ _≡_
  ≤⁺-respʳ-≡ : _≤⁺_ Respectsʳ _≡_
  ≤⁺-resp-≡ : _≤⁺_ Respects₂ _≡_
  ≤⁺-respˡ-≈⁺ : _≤_ Respectsˡ _≈_ → _≤⁺_ Respectsˡ _≈⁺_
  ≤⁺-respʳ-≈⁺ : _≤_ Respectsʳ _≈_ → _≤⁺_ Respectsʳ _≈⁺_
  ≤⁺-resp-≈⁺ : _≤_ Respects₂ _≈_ → _≤⁺_ Respects₂ _≈⁺_
  ```

* In `Data.Vec.Relation.Binary.Pointwise.Inductive`
  ```agda
  irrelevant : ∀ {_∼_ : REL A B ℓ} {n m} → Irrelevant _∼_ → Irrelevant (Pointwise _∼_ {n} {m})
  antisym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {R : REL A B ℓ} {m n} →
            Antisym P Q R → Antisym (Pointwise P {m}) (Pointwise Q {n}) (Pointwise R)
  ```

* In `Data.Vec.Relation.Binary.Pointwise.Extensional`
  ```agda
  antisym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {R : REL A B ℓ} {n} →
            Antisym P Q R → Antisym (Pointwise P {n}) (Pointwise Q) (Pointwise R)
  ```

* In `Relation.Nullary.Negation.Core`
  ```agda
  ¬¬-η           : A → ¬ ¬ A
  contradiction′ : ¬ A → A → Whatever
  ```

* In `Relation.Unary`
  ```agda
  ⟨_⟩⊢_ : (A → B) → Pred A ℓ → Pred B _
  [_]⊢_ : (A → B) → Pred A ℓ → Pred B _
  ```

* In `Relation.Unary.Properties`
  ```agda
  _map-⊢_   : P ⊆ Q → f ⊢ P ⊆ f ⊢ Q
  map-⟨_⟩⊢_ : P ⊆ Q → ⟨ f ⟩⊢ P ⊆ ⟨ f ⟩⊢ Q
  map-[_]⊢_ : P ⊆ Q → [ f ]⊢ P ⊆ [ f ]⊢ Q
  ⟨_⟩⊢⁻_    : ⟨ f ⟩⊢ P ⊆ Q → P ⊆ f ⊢ Q
  ⟨_⟩⊢⁺_    : P ⊆ f ⊢ Q → ⟨ f ⟩⊢ P ⊆ Q
  [_]⊢⁻_    : Q ⊆ [ f ]⊢ P → f ⊢ Q ⊆ P
  [_]⊢⁺_    : f ⊢ Q ⊆ P → Q ⊆ [ f ]⊢ P
  ```

* In `System.Random`:
  ```agda
  randomIO : IO Bool
  randomRIO : RandomRIO {A = Bool} _≤_
  ```

* In Relation.Unary.Properites
  ```agda
  ¬∃⟨P⟩⇒Π[∁P] : ¬ ∃⟨ P ⟩ → Π[ ∁ P ]
  ¬∃⟨P⟩⇒∀[∁P] : ¬ ∃⟨ P ⟩ → ∀[ ∁ P ]
  ∃⟨∁P⟩⇒¬Π[P] : ∃⟨ ∁ P ⟩ → ¬ Π[ P ]
  ∃⟨∁P⟩⇒¬∀[P] : ∃⟨ ∁ P ⟩ → ¬ ∀[ P ]
  Π[∁P]⇒¬∃[P] : Π[ ∁ P ] → ¬ ∃⟨ P ⟩
  ∀[∁P]⇒¬∃[P] : ∀[ ∁ P ] → ¬ ∃⟨ P ⟩
  ```
