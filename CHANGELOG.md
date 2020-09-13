Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

* First instance modules, which provide `Functor`, `Monad`, `Applicative`
  instances for various datatypes. Found under `Data.X.Instances`.

* New standardised numeric predicates `NonZero`, `Positive`, `Negative`,
  `NonPositive`, `NonNegative`, especially designed to work as instance
  arguments.

* A general hierarachy of metric functions/spaces, including a specialisation to ℕ.

Bug-fixes
---------

* Fixed various algebraic bundles not correctly re-exporting
  `commutativeSemigroup` proofs.

* Fix in `Induction.WellFounded.FixPoint`, where the well-founded relation `_<_` and
  the predicate `P` were required to live at the same universe level.

Non-backwards compatible changes
--------------------------------

#### Changes to the `Relation.Unary.Closure` hierarchy

* Following the study of the closure operator `◇` dual to the `□` we originally
  provided, the set of modules has been reorganised. We have

  + Added the `◇` closure operator to `.Base`
  + Moved all of the `□`-related functions in submodules called `□`
  + Added all of the corresponding `◇`-related functions in submodules called `◇`

* We also provide functions converting back and forth between `□`-based and
  `◇`-based statements in `.Base`:

  ```agda
  curry   : (∀ {x} → ◇ T x → P x) → (∀ {x} → T x → □ P x)
  uncurry : (∀ {x} → T x → □ P x) → (∀ {x} → ◇ T x → P x)
  ```
 
#### Changes to floating-point arithmetic

* The functions in `Data.Float.Base` were updated following changes upstream,
  in `Agda.Builtin.Float`, see <https://github.com/agda/agda/pull/4885>.

* The bitwise ordering on floating-point numbers, `Data.Float.Properties._<_`
  was deprecated without replacement, as it was deeply unintuitive, e.g., `forall x. x < -x`.

#### Other


* The `n` argument to `_⊜_` in `Tactic.RingSolver.NonReflective` has
  been made implict rather than explicit.

* `Data.Empty.Polymorphic` and `Data.Unit.Polymorphic` were rewritten
  to explicitly use `Lift` rather that defining new types. This means
  that these are now compatible with `⊥` and `⊤` from the rest of the
  library. This allowed them to be used in the rest of library where
  explicit `Lift` was used.

* `Data.Maybe.Base` now re-exports the definition of `Maybe` given by
  `Agda.Builtin.Maybe`. The `Foreign.Haskell` modules and definitions
  corresponding to `Maybe` have been removed.

* The representation of reflected syntax in `Reflection.Term` and
  `Reflection.Pattern` has been updated to match the new
  representation used in Agda 2.6.2. Specifically, the following changes were made:

  * The type of the `var` constructor of the `Pattern` datatype has
    been changed from `(x : String) → Pattern` to `(x : Int) →
    Pattern`.
  * The type of the `dot` constructor of the `Pattern` datatype has
    been changed from `Pattern` to `(t : Term) → Pattern`
  * The types of the `clause` and `absurd-clause` constructors of the
    `Clause` datatype now take an extra argument `(tel : Telescope)`,
    where `Telescope = List (String × Arg Type)`.

  See the release notes of Agda 2.6.2 for more information.

Deprecated modules
------------------

* `Data.AVL` and all of its submodules have been moved to `Data.Tree.AVL`

* The module `Induction.WellFounded.InverseImage` has been deprecated. The proofs
  `accessible` and `wellFounded` have been moved to `Relation.Binary.Construct.On`.

* `Reflection.TypeChecking.MonadSyntax` ↦ `Reflection.TypeChecking.Monad.Syntax`

Deprecated names
----------------

* The proofs `replace-equality` from `Algebra.Properties.(Lattice/DistributiveLattice/BooleanAlgebra)`
  have been deprecated in favour of the proofs in the new `Algebra.Construct.Subst.Equality` module.

* In order to be consistent in usage of \prime character and apostrophe in identifiers, the following three names were deprecated in favor of their replacement that ends with a \prime character.
  * `Data.List.Base.InitLast._∷ʳ'_` ↦ `Data.List.Base.InitLast._∷ʳ′_`
  * `Data.List.NonEmpty.SnocView._∷ʳ'_` ↦ `Data.List.NonEmpty.SnocView._∷ʳ′_`
  * `Relation.Binary.Construct.StrictToNonStrict.decidable'` ↦ `Relation.Binary.Construct.StrictToNonStrict.decidable′`

* In `Algebra.Morphism.Definitions` and `Relation.Binary.Morphism.Definitions`
  the type `Morphism A B` were recovered by publicly importing its
  definition from `Function.Core`. See discussion in issue #1206.

* In `Data.Nat.Properties`:
  ```
  *-+-isSemiring             ↦  +-*-isSemiring
  *-+-isCommutativeSemiring  ↦  +-*-isCommutativeSemiring
  *-+-semiring               ↦  +-*-semiring
  *-+-commutativeSemiring    ↦  +-*-commutativeSemiring
  ```

* In `Data.Nat.Binary.Properties`:
  ```
  *-+-isSemiring                         ↦  +-*-isSemiring
  *-+-isCommutativeSemiring              ↦  +-*-isCommutativeSemiring
  *-+-semiring                           ↦  +-*-semiring
  *-+-commutativeSemiring                ↦  +-*-commutativeSemiring
  *-+-isSemiringWithoutAnnihilatingZero  ↦  +-*-isSemiringWithoutAnnihilatingZero
  ```
* In ̀Function.Basè:
  ```
  *_-[_]-_  ↦  _-⟪_⟫-_
  ```

* `Data.List.Relation.Unary.Any.any` to `Data.List.Relation.Unary.Any.any?`
* `Data.List.Relation.Unary.All.all` to `Data.List.Relation.Unary.All.all?`
* `Data.Vec.Relation.Unary.Any.any` to `Data.Vec.Relation.Unary.Any.any?`
* `Data.Vec.Relation.Unary.All.all` to `Data.Vec.Relation.Unary.All.all?`

New modules
-----------

* The direct products and zeros over algebraic structures and bundles:
  ```
  Algebra.Construct.Zero
  Algebra.Construct.DirectProduct
  Algebra.Module.Construct.DirectProduct.agda
  ```

* Substituting the notion of equality for various structures
  ```
  Algebra.Construct.Subst.Equality
  Relation.Binary.Construct.Subst.Equality
  ```

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

* Predicate for lists that are sorted with respect to a total order
  ```
  Data.List.Relation.Unary.Sorted.TotalOrder
  Data.List.Relation.Unary.Sorted.TotalOrder.Properties
  ```

* Subtraction for binary naturals:
  ```
  Data.Nat.Binary.Subtraction
  ```

* A predicate for vectors in which every pair of elements is related.
  ```
  Data.Vec.Relation.Unary.AllPairs
  Data.Vec.Relation.Unary.AllPairs.Properties
  ```

* A predicate for vectors in which every element is unique.
  ```
  Data.Vec.Relation.Unary.Unique.Propositional
  Data.Vec.Relation.Unary.Unique.Propositional.Properties
  Data.Vec.Relation.Unary.Unique.Setoid
  Data.Vec.Relation.Unary.Unique.Setoid.Properties
  ```

* Properties for functional vectors:
  ```
  Data.Vec.Functional.Properties
  ```

* Symmetry for various functional properties
  ```agda
  Function.Construct.Symmetry
  ```

* Added a hierarchy for metric spaces:
  ```
  Function.Metric
  Function.Metric.Core
  Function.Metric.Definitions
  Function.Metric.Structures
  Function.Metric.Bundles
  ```
  The distance functions above are defined over an arbitrary type for the image.
  Specialisations to the natural numbers are provided in the following modules:
  ```
  Function.Metric.Nat
  Function.Metric.Nat.Core
  Function.Metric.Nat.Definitions
  Function.Metric.Nat.Structures
  Function.Metric.Nat.Bundles
  ```
  and other specialisations can be created in a similar fashion.

* Type-checking monads
  ```
  Reflection.TypeChecking.Monad
  Reflection.TypeChecking.Monad.Categorical
  Reflection.TypeChecking.Monad.Instances
  Reflection.TypeChecking.Format
  ```

* Indexed nullary relations/sets:
  ```
  Relation.Nullary.Indexed
  ```

* Symmetric transitive closures of binary relations:
  ```
  Relation.Binary.Construct.Closure.SymmetricTransitive
  ```

* Composition of binary relations:
  ```
  Relation.Binary.Construct.Composition
  ```

* Generic printf
  ```
  Text.Format.Generic
  Text.Printf.Generic
  ```

Other major changes
-------------------

* The module `Relation.Binary.PropositionalEquality` has been growing in size and
  now depends on a lot of other parts of the library, even though its basic
  functionality does not. To fix this some of its parts have been factored out.
  `Relation.Binary.PropositionalEquality.Core` already existed. Added are:
  ```agda
  Relation.Binary.PropositionalEquality.Properties
  Relation.Binary.PropositionalEquality.Algebra
  ```
  These new modules are re-exported by `Relation.Binary.PropositionalEquality`
  and so these changes should be invisble to current users, but can be useful
  to authors of large libraries.

Other minor additions
---------------------

* Add proof to `Algebra.Morphism.RingMonomorphism`:
  ```agda
  isCommutativeRing : IsCommutativeRing _≈₂_ _⊕_ _⊛_ ⊝_ 0#₂ 1#₂ →
                      IsCommutativeRing _≈₁_ _+_ _*_ -_ 0# 1#
  ```

* Added new proof to `Data.Fin.Induction`:
  ```agda
  <-wellFounded : WellFounded _<_
  ```

* Added new properties to `Data.Fin.Properties`:
  ```agda
  toℕ≤n             : (i : Fin n) → toℕ i ≤ n
  ≤fromℕ            : (i : Fin (suc n)) → i ≤ fromℕ n
  fromℕ<-irrelevant : m ≡ n → fromℕ< m<o ≡ fromℕ< n<o
  fromℕ<-injective  : fromℕ< m<o ≡ fromℕ< n<o → m ≡ n
  inject₁ℕ<         : (i : Fin n) → toℕ (inject₁ i) < n
  inject₁ℕ≤         : (i : Fin n) → toℕ (inject₁ i) ≤ n
  ≤̄⇒inject₁<        : i' ≤ i → inject₁ i' < suc i
  ℕ<⇒inject₁<       : toℕ i' < toℕ i → inject₁ i' < i
  toℕ-lower₁        : (≢p : m ≢ toℕ x) → toℕ (lower₁ x ≢p) ≡ toℕ x
  inject₁≡⇒lower₁≡  : (≢p : n ≢ toℕ i') → inject₁ i ≡ i' → lower₁ i' ≢p ≡ i
  pred<             : pred i < i

  splitAt-<         : splitAt m {n} i ≡ inj₁ (fromℕ< i<m)
  splitAt-≥         : splitAt m {n} i ≡ inj₂ (reduce≥ i i≥m)
  inject≤-injective : inject≤ x n≤m ≡ inject≤ y n≤m′ → x ≡ y
  ```

* Added new functions to `Data.Fin.Base`:
  ```agda
  quotRem  : Fin (n * k) → Fin k × Fin n
  opposite : Fin n → Fin n
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

* Added new functions to `Data.List.Base`:
  ```agda
  wordsBy              : Decidable P → List A → List (List A)
  cartesianProductWith : (A → B → C) → List A → List B → List C
  cartesianProduct     : List A → List B → List (A × B)
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  reverse-injective : reverse xs ≡ reverse ys → xs ≡ ys
  map-injective     : Injective _≡_ _≡_ f → Injective _≡_ _≡_ (map f)
  ```

* Added new proofs to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-cartesianProductWith⁺ : a ∈ xs → b ∈ ys → f a b ∈ cartesianProductWith f xs ys
  ∈-cartesianProductWith⁻ : v ∈ cartesianProductWith f xs ys → ∃₂ λ a b → a ∈ xs × b ∈ ys × v ≡ f a b
  ∈-cartesianProduct⁺     : x ∈ xs → y ∈ ys → (x , y) ∈ cartesianProduct xs ys
  ∈-cartesianProduct⁻     : xy ∈ cartesianProduct xs ys → x ∈ xs × y ∈ ys
  ```

* Added new proofs to `Data.List.Membership.Setoid.Properties`:
  ```agda
  ∈-cartesianProductWith⁺ : a ∈₁ xs → b ∈₂ ys → f a b ∈₃ cartesianProductWith f xs ys
  ∈-cartesianProductWith⁻ : v ∈₃ cartesianProductWith f xs ys → ∃₂ λ a b → a ∈₁ xs × b ∈₂ ys × v ≈₃ f a b
  ∈-cartesianProduct⁺     : x ∈₁ xs → y ∈₂ ys → (x , y) ∈₁₂ cartesianProduct xs ys
  ∈-cartesianProduct⁻     : (x , y) ∈₁₂ cartesianProduct xs ys → x ∈₁ xs
  ```

* Added new operations to `Data.List.Relation.Unary.All`:
  ```agda
  tabulateₛ : (∀ {x} → x ∈ xs → P x) → All P xs
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (f x y)) → All P (cartesianProductWith f xs ys)
  cartesianProduct⁺     : (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x , y)) → All P (cartesianProduct xs ys)
  ```

* Added new proofs to `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {x y} → P x → Q y → R (f x y)) → Any P xs → Any Q ys → Any R (cartesianProductWith f xs ys)
  cartesianProductWith⁻ : (∀ {x y} → R (f x y) → P x × Q y) → Any R (cartesianProductWith f xs ys) → Any P xs × Any Q ys
  cartesianProduct⁺     : Any P xs → Any Q ys → Any (P ⟨×⟩ Q) (cartesianProduct xs ys)
  cartesianProduct⁻     : Any (P ⟨×⟩ Q) (cartesianProduct xs ys) → Any P xs × Any Q ys
  reverseAcc⁺           : Any P acc ⊎ Any P xs → Any P (reverseAcc acc xs)
  reverseAcc⁻           : Any P (reverseAcc acc xs) -> Any P acc ⊎ Any P xs
  reverse⁺              : Any P xs → Any P (reverse xs)
  reverse⁻              : Any P (reverse xs) → Any P xs
  ```

* Added new proofs to `Data.List.Relation.Unary.Unique.Propositional.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {w x y z} → f w y ≡ f x z → w ≡ x × y ≡ z) → Unique xs → Unique ys → Unique (cartesianProductWith f xs ys)
  cartesianProduct⁺     : Unique xs → Unique ys → Unique (cartesianProduct xs ys)
  ```

* Added new proofs to `Data.List.Relation.Unary.Unique.Setoid.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {w x y z} → f w y ≈₃ f x z → w ≈₁ x × y ≈₂ z) → Unique S xs → Unique T ys → Unique U (cartesianProductWith f xs ys)
  cartesianProduct⁺     : Unique S xs → Unique T ys → Unique (S ×ₛ T) (cartesianProduct xs ys)
  ```

* Added new properties to ` Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  ↭-empty-inv     : xs ↭ [] → xs ≡ []
  ¬x∷xs↭[]        : ¬ (x ∷ xs ↭ [])
  ↭-singleton-inv : xs ↭ [ x ] → xs ≡ [ x ]
  ↭-map-inv       : map f xs ↭ ys → ∃ λ ys′ → ys ≡ map f ys′ × xs ↭ ys′
  ↭-length        : xs ↭ ys → length xs ≡ length ys
  ```

* Added new proofs to `Data.List.Relation.Unary.Linked.Properties`:
  ```agda
  map⁻    : Linked R (map f xs) → Linked (λ x y → R (f x) (f y)) xs
  filter⁺ : Transitive R → Linked R xs → Linked R (filter P? xs)
  ```

* Add new properties to `Data.Maybe.Properties`:
  ```agda
  map-injective : Injective _≡_ _≡_ f → Injective _≡_ _≡_ (map f)
  ```

* Added new proofs to `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  nothing-inv : Pointwise R nothing x → x ≡ nothing
  just-inv    : Pointwise R (just x) y → ∃ λ z → y ≡ just z × R x z
  ```

* `Data.Nat.Binary.Induction` now re-exports `Acc` and `acc` from `Induction.WellFounded`.

* Added new properties to `Data.Nat.Binary.Properties`:
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

* Added new types and constructors to `Data.Nat.Base`:
  ```agda
  NonZero   : ℕ → Set

  ≢-nonZero : n ≢ 0 → NonZero n
  >-nonZero : n > 0 → NonZero n
  ```

* The function `pred` in `Data.Nat.Base` has been redefined as `pred n = n ∸ 1`.
  Consequently proofs about `pred` are now just special cases of proofs for `_∸_`.
  The change is fully backwards compatible.

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  pred[m∸n]≡m∸[1+n]     : pred (m ∸ n) ≡ m ∸ suc n

  ∣-∣-isProtoMetric     : IsProtoMetric _≡_ ∣_-_∣
  ∣-∣-isPreMetric       : IsPreMetric _≡_ ∣_-_∣
  ∣-∣-isQuasiSemiMetric : IsQuasiSemiMetric _≡_ ∣_-_∣
  ∣-∣-isSemiMetric      : IsSemiMetric _≡_ ∣_-_∣
  ∣-∣-isMetric          : IsMetric _≡_ ∣_-_∣

  ∸-magma               : Magma 0ℓ 0ℓ
  ∣-∣-quasiSemiMetric   : QuasiSemiMetric 0ℓ 0ℓ
  ∣-∣-semiMetric        : SemiMetric 0ℓ 0ℓ
  ∣-∣-preMetric         : PreMetric 0ℓ 0ℓ
  ∣-∣-metric            : Metric 0ℓ 0ℓ
  ```

* Added new proof to `Data.Nat.Coprimality`:
  ```agda
  ¬0-coprimeTo-2+ : ¬ Coprime 0 (2 + n)
  recompute       : .(Coprime n d) → Coprime n d
  ```

* Made first argument of `[,]-∘-distr` in `Data.Sum.Properties` explicit

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

* Added new types and constructors to `Data.Rational`:
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

* Added new proofs to `Data.Rational.Properties`:
  ```agda
  +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℚ 1ℚ
  +-*-commutativeRing   : CommutativeRing 0ℓ 0ℓ

  *-zeroˡ : LeftZero 0ℚ _*_
  *-zeroʳ : RightZero 0ℚ _*_
  *-zero  : Zero 0ℚ _*_
  ```

* Added new types and constructors to `Data.Rational.Unnormalised`:
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

* Added new functions to `Data.String.Base`:
  ```agda
  wordsBy : Decidable P → String → List String
  words   : String → List String
  ```

* Added new proofs to `Data.Tree.Binary.Properties`:
  ```agda
  map-compose : map (f₁ ∘ f₂) (g₁ ∘ g₂) ≗ map f₁ g₁ ∘ map f₂ g₂
  map-cong    : f₁ ≗ f₂ → g₁ ≗ g₂ → map f₁ g₁ ≗ map f₂ g₂
  ```

* Added new proofs to `Data.Vec.Properties`:
  ```agda
  unfold-take         : take (suc n) (x ∷ xs) ≡ x ∷ take n xs
  unfold-drop         : drop (suc n) (x ∷ xs) ≡ drop n xs
  lookup-inject≤-take : lookup xs (inject≤ i m≤m+n) ≡ lookup (take m xs) i
  ```

* Added new functions to `Data.Vec.Functional`:
  ```agda
  length    : Vector A n → ℕ
  insert    : Vector A n → Fin (suc n) → A → Vector A (suc n)
  updateAt  : Fin n → (A → A) → Vector A n → Vector A n
  _++_      : Vector A m → Vector A n → Vector A (m + n)
  concat    : Vector (Vector A m) n → Vector A (n * m)
  _>>=_     : Vector A m → (A → Vector B n) → Vector B (m * n)
  unzipWith : (A → B × C) → Vector A n → Vector B n × Vector C n
  unzip     : Vector (A × B) n → Vector A n × Vector B n
  take      : Vector A (m + n) → Vector A m
  drop      : Vector A (m + n) → Vector A n
  reverse   : Vector A n → Vector A n
  init      : Vector A (suc n) → Vector A n
  last      : Vector A (suc n) → A
  transpose : Vector (Vector A n) m → Vector (Vector A m) n
  ```

* Added new functions to `Data.Vec.Relation.Unary.All`:
  ```agda
  reduce    : (f : ∀ {x} → P x → B) → All P xs → Vec B n
  ```

* Added new proofs to `Data.Vec.Relation.Unary.All.Properties`:
  ```agda
  All-swap  : All (λ x → All (x ~_) ys) xs → All (λ y → All (_~ y) xs) ys
  tabulate⁺ : (∀ i → P (f i)) → All P (tabulate f)
  tabulate⁻ : All P (tabulate f) → (∀ i → P (f i))
  drop⁺     : All P xs → All P (drop m xs)
  take⁺     : All P xs → All P (take m xs)
  ```

* Added new proofs to `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  index-∈-lookup : index (∈-lookup i xs) ≡ i
  ```

* Added new functions to `Function.Base`:
  ```agda
  _∘₂_    : (f : {x : A₁} → {y : A₂ x} → (z : B x y) → C z) →
                (g : (x : A₁) → (y : A₂ x) → B x y) →
                    ((x : A₁) → (y : A₂ x) → C (g x y))
  _∘₂′_   : (C → D) → (A → B → C) → (A → B → D)

  constᵣ  : A → B → B

  _-⟪_∣   : (A → B → C) → (C → B → D) → (A → B → D)
  ∣_⟫-_   : (A → C → D) → (A → B → C) → (A → B → D)
  _-⟨_∣   : (A → C) → (C → B → D) → (A → B → D)
  ∣_⟩-_   : (A → C → D) → (B → C) → (A → B → D)
  _-⟪_⟩-_ : (A → B → C) → (C → D → E) → (B → D) → (A → B → E)
  _-⟨_⟫-_ : (A → C) → (C → D → E) → (A → B → D) → (A → B → E)
  _-⟨_⟩-_ : (A → C) → (C → D → E) → (B → D) → (A → B → E)
  _on₂_   : (C → C → D) → (A → B → C) → (A → B → D)
  ```

* Added new operator to `Relation.Binary`:
  ```agda
  _⇔_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
  ```

* Added new proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  trans-cong  : trans (cong f p) (cong f q) ≡ cong f (trans p q)
  cong₂-reflˡ : cong₂ _∙_ refl p ≡ cong (x ∙_) p
  cong₂-reflʳ : cong₂ _∙_ p refl ≡ cong (_∙ u) p
  ```

* Added new combinators to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  pattern erefl x = refl {x = x}

  cong′  : {f : A → B} x → f x ≡ f x
  icong  : {f : A → B} {x y} → x ≡ y → f x ≡ f y
  icong′ : {f : A → B} x → f x ≡ f x
  ```
