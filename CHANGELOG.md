Version 3.0
===========

The library has been tested using Agda 2.8.0.

Highlights
----------

* Modules that previously used `--cubical-compatible` once again use `--without-K`.

* The notation for `Decidable` relations has been (partially) standardised: thus
  - `_≡?_` (at `infix 4`) for `DecidableEquality`
  - `_≈?_` (ditto.) for the general `IsDecEquivalence`

  At present, the old fieldname `_≟_` has been retained, in order to avoid
  a non-backwards compatible/breaking change of fieldname, which will plan
  to do in Version 3.0, with accompanying deprecation of that name, against
  its eventual removal in subsequent versions.

  The change leads to a number of (trivial) renamings/deprecations, others more
  substantive in `Data.{Nat|Fin}.Properties` for the concrete datatypes, which
  are summarised below, but are not each documented for all affected modules.

* Any v1.x deprecation has been removed entirely.
  This involves the removal of modules:
  - `Algebra.FunctionProperties.Consequences.Core`
  - `Algebra.FunctionProperties.Consequences.Propositional`
  - `Algebra.FunctionProperties.Consequences`
  - `Algebra.Operations.CommutativeMonoid`
  - `Algebra.Operations.Ring`
  - `Algebra.Operations.Semiring`
  - `Data.AVL.Indexed.WithK`
  - `Data.AVL.NonEmpty.Propositional`
  - `Data.AVL.Height`
  - `Data.AVL.Indexed`
  - `Data.AVL.IndexedMap`
  - `Data.AVL.Key`
  - `Data.AVL.Map`
  - `Data.AVL.NonEmpty`
  - `Data.AVL.Value`
  - `Data.AVL`
  - `Foreign.Haskell.Maybe`
  - `Relation.Binary.OrderMorphism`
  - `Text.Tree.Linear`
  - `Strict`

  Several Definitions from other modules have also been removed.


Bug-fixes
---------

* Removed unnecessary parameter `zero : Zero 0# *` from
  `Algebra.Structures.IsNonAssociativeRing`.

* Fix a bug in `Data.List.Base`'s `linesBy` (the last empty line would be dropped).

* [issue #3003](https://github.com/agda/agda-stdlib/issues/3003)
  Uncorrected, the existing axiomatisation of `Algebra.Structures.IsKleeneAlgebra`
  meant that it was possible to prove that `0# ⋆ ≈ 1#`. As a consequence, the
  axioms have been corrected so that fields `starExpansive` and `starDestructive`
  now refer to the partial order relation `_≤_`, which is defined in-place, but
  only depends on the `+-isCommutativeBand` substructure.

  As a further knock-on consequence, module `Algebra.Properties.KleeneAlgebra`
  has been completely rewritten in order to accommodate the new axiomatisation.

Non-backwards compatible changes
--------------------------------

* The notation for `Decidable` relations has been (partially) standardised: thus
  - `_≡?_` (at `infix 4`) for `DecidableEquality`
  - `_≈?_` (ditto.) for the fieldname of the general `IsDecEquivalence`

  Despite being non-backwards compatible, because a fieldname has changed, the
  old notation `_≟_` (which was used for both of the above) has been retained,
  but deprecated. This leads to a large amount of (trivial) deprecations, in
  addition to the substantive one under `Relation.Binary.Structures`, and in
  `Data.{Nat|Fin}.Properties` for the concrete datatypes. These deprecations
  are summarised below, but are not each documented for each affected module.

* [issue #1436](https://github.com/agda/agda-stdlib/issues/1436)
  The definitions of `LeftCancellative`/`RightCancellative` in `Algebra.Definitions`
  have been altered to make the quantification for each argument explicit. The
  definitions of `AlmostLeftCancellative`/`AlmostRightCancellative` have also been
  changed to rephrase them in 'positive' logical terms. These definitions have been
  propagated through the numeric types `X` in `Data.X.Properties`. As part of this
  refactoring, lemmas in `Algebra.Properties.CancellativeCommutativeSemiring` no
  longer require a `Decidable _≈_` hypothesis.

* [issue #2471](https://github.com/agda/agda-stdlib/issues/2471)
  In `Relation.Binary.Definitions`, the left/right order of the components of
  `_Respects₂_` have been swapped. Previously the position of the `_Respectsˡ_`
  (respects left) component was placed on the *right* hand side of the pair and
  `_Respectsʳ_` (respects right) was placed on the *left* hand side of the pair.
  By switching them the names are now consistent with their location.

* [issue #2547](https://github.com/agda/agda-stdlib/issues/2547)
  The names of the *implicit* binders in the following definitions have been
  rectified to be consistent with the rest of `Relation.Binary.Definitions`:
  `Transitive`, `Antisym`, and `Antisymmetric`.

* [Issue #2548](https://github.com/agda/agda-stdlib/issues/2458)
  Consistent with other names (such as `∙-cong`, `ε-homo` etc.) in
  `Algebra.*`, the field name of the basic homomorphism property `homo` in
  `Algebra.Morphism.Structures.IsMagmaHomomorphism` has been renamed to `∙-homo`.


* [Issue #3022](https://github.com/agda/agda-stdlib/issues/3022)
  The previous development of rose trees has been refactored to make
  the definitions `safe` wrt termination checking etc. by avoiding
  the use of `sized-types`, at the cost of a little extra plumbing.
  ```
  Data.Tree.Rose
  Data.Tree.Rose.Properties
  Data.Tree.Rose.Show
  ```

* `^-semigroup-morphism` and `^-monoid-morphism` in `Data.Nat.Properties`
  deprecated below as part of removing v1.x-era deprecations, have moreover had
  their definitions and signatures updated to use `IsMagmaHomomorphism` and
  `IsMonoidHomomorphism` respectively

* In `Data.List.DifferenceList.Base`: `take` and `drop` are deprecated
  because they do not have a lawful relationship to their `Data.List`
  counterparts. Consider using `viaList` if you want a lawful lifting
  of `take` or `drop`.

Minor improvements
------------------

* [Issue #2502](https://github.com/agda/agda-stdlib/issues/2502) The module
  `Algebra.Consequences.Base` now takes the underlying equality relation as
  an additional top-level parameter, with slightly improved ergonomics wrt
  subsequent imports by clients, as well as streamlined internals. Moreover,
  it now has the implicit parameters of its internal modules lifted out as
  global `variable`s.

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Definitions`:
  ```agda
  StarLeftExpansive     ↦  Relation.Binary.Definitions.KleeneAlgebra.StarLeftExpansive
  StarRightExpansive    ↦  Relation.Binary.Definitions.KleeneAlgebra.StarRightExpansive
  StarExpansive         ↦  Relation.Binary.Definitions.KleeneAlgebra.StarExpansive
  StarLeftDestructive   ↦  Relation.Binary.Definitions.KleeneAlgebra.StarLeftDestructive
  StarRightDestructive  ↦  Relation.Binary.Definitions.KleeneAlgebra.StarRightDestructive
  StarDestructive       ↦  Relation.Binary.Definitions.KleeneAlgebra.StarDestructive
  ```

* In `Algebra.Morphism.Structures`:
  ```agda
  homo  ↦  ∙-homo
  ```

* In `Data.DifferenceList.Base`:
  ```agda
  lift ↦ _++_
  ```

* In `Data.Fin.Properties`:
  ```agda
  _≟_      ↦  _≡?_
  inj⇒≟    ↦  inj⇒≡?
  ≟-≡      ↦  ≡?-≡
  ≟-≡-refl ↦  ≡?-≡-refl
  ≟-≢      ↦  ≡?-≢
  ```

* In `Data.Integer.GCD`:
  ```agda
  gcd[0,0]≡0 ↦ gcd[i,i]≡∣i∣
  ```

* In `Data.Nat.GCD`:
  ```agda
  gcd[0,0]≡0 ↦ gcd[n,n]≡n
  ```

* In `Data.Nat.Properties`:
  ```agda
  _≟_                  ↦   _≡?_
  ≟-diag               ↦   ≡?-≡
  ≟-≡                  ↦   ≡?-≢
  ≟?-≡-refl            ↦   ≡?-≡-refl
  ^-semigroup-morphism ↦   ^-isMagmaHomomorphism
  ^-monoid-morphism    ↦   ^-isMonoidHomomorphism
  ```

* In `Algebra.Properties.CancellativeCommutativeSemiring`:
  ```agda
  *-almostCancelʳ  ↦  Algebra.Structures.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
  ```

* In `Effect.Monad.Partiality`:
  ```agda
  _≟-Kind_     ↦   _≡?-Kind_
  ```

* In `Reflection.AST.AlphaEquality`:
  ```agda
  ≟⇒α     ↦   ≡?⇒α
  ```

* In `Relation.Binary.PropositionalEquality`:
  ```agda
  ≡-≟-identity     ↦   ≡-≡?-identity
  ≢-≟-identity     ↦   ≢-≡?-identity
  ```

* In `Effect.Monad.Partiality`:
  ```agda
  _≟-Kind_     ↦   _≡?-Kind_
  ```

* In `Reflection.AST.AlphaEquality`:
  ```agda
  ≟⇒α     ↦   ≡?⇒α
  ```

* In `Relation.Binary.PropositionalEquality`:
  ```agda
  ≡-≟-identity     ↦   ≡-≡?-identity
  ≢-≟-identity     ↦   ≢-≡?-identity
  ```

* In `Relation.Nary`:
  ```agda
  ≟-mapₙ     ↦   ≡?-mapₙ
  ```

New modules
-----------

* `Algebra.Properties.KleeneAlgebra` has been completely rewritten.

* `Codata.Guarded.Stream.Relation.Unary.Linked` for a proof that each pair
  of consecutive elements of a stream are related.

* `Data.Bool.ListAction.Properties` for properties of conjunction and
  disjunction of lists.

* `Data.DifferenceList` has been refactored to reexport the contents of two new modules:
  - `Data.DifferenceList.Base`
  - `Data.DifferenceList.Properties`

* A new type of lists that grow on the right.
  This is typically useful to model contexts of typing rules
  or type accumulators that need to be reversed in the base case.
  ```
  Data.SnocList.Base
  ```

* A namespace for the (unsafe) use of `sized-types` to define rose trees
  and their associated operations, previously defined under `Data.Tree`,
  with the intention of migrating all such uses of sized datatypes here.
  ```
  Data.Sized
  Data.Sized.Tree
  ```
  Correspondingly, the previous development of rose trees has been refactored
  to make the definitions `safe` wrt termination checking etc.
  ```
  Data.Tree.Rose
  Data.Tree.Rose.Properties
  Data.Tree.Rose.Show
  ```

Additions to existing modules
-----------------------------

* In `Algebra.Consequences.Base`:
  ```agda
  almost⇒exceptˡ : _AlmostLeftCancellative′_ _≈_ P _•_ →
                   Except_LeftCancellative_ _≈_ P _•_
  almost⇒exceptʳ : _AlmostRightCancellative′_ _≈_ P _•_ →
                   Except_RightCancellative_ _≈_ P _•_
  except⇒almostˡ : Decidable P → Except_LeftCancellative_ _≈_ P _•_ →
                   _AlmostLeftCancellative′_ _≈_ P _•_
  except⇒almostʳ : Decidable P → Except_RightCancellative_ _≈_ P _•_ →
                   _AlmostRightCancellative′_ _≈_ P _•_
  ```

* In `Algebra.Consequences.Setoid`:
  ```agda
  comm∧cancelAtˡ⇒cancelAtʳ : LeftCancellativeAt x _∙_ → RightCancellativeAt x _∙_
  comm∧cancelAtʳ⇒cancelAtˡ : RightCancellativeAt x _∙_ → LeftCancellativeAt x _∙_
  ```

* In `Algebra.Definitions`:
  ```agda
  LeftCancellativeAt           : A → Op₂ A → Set _
  RightCancellativeAt          : A → Op₂ A → Set _
  _AlmostLeftCancellative′_    : (P : Pred A p) → Op₂ A → Set _
  Provided_LeftCancellative_   : (P : Pred A p) → Op₂ A → Set _
  Except_LeftCancellative_     : (P : Pred A p) → Op₂ A → Set _
  _AlmostRightCancellative′_   : (P : Pred A p) → Op₂ A → Set _
  Provided_RightCancellative_  : (P : Pred A p) → Op₂ A → Set _
  Except_RightCancellative_    : (P : Pred A p) → Op₂ A → Set _
  ```

* In `Algebra.Properties.KleeneAlgebra`:
  ```agda
  ≤-reflexive    : _≈_ ⇒ _≤_
  ≤-refl         : Reflexive _≤_
  ≤-trans        : Transitive _≤_
  ≤-antisym      : Antisymmetric _≈_ _≤_
  isPreorder     : IsPreorder _≈_ _≤_
  isPartialOrder : IsPartialOrder _≈_ _≤_
  preorder       : Preorder _ _
  poset          : Poset _ _
  ```

* In `Algebra.Structures.IsKleeneAlgebra`:
  ```agda
  _≤_            : Rel A _
  ```

* In `Data.Bool.Properties`:
  ```agda
  ∨-monoid : Monoid 0ℓ 0ℓ
  ∧-monoid : Monoid 0ℓ 0ℓ
  ```

* In `Data.Char.Base`:
  ```agda
  _≉ᵇ_ : (c d : Char) → Bool
  case-insensitive : Rel Char ℓ → Rel Char ℓ
  _≈ᵢ_ : Rel Char zero
  _≉ᵢ_ : Rel Char zero
  _<ᵇ_ : (c d : Char) → Bool
  ```

* In `Data.Char.Properties`: `_≈?_` reinstated from an earlier v1.5 deprecation
  ```agda
  infix 4 _≈?_
  _≈?_ : Decidable _≈_
  ≈ᵢ-setoid : Setoid _ _
  ≈ᵢ-decSetoid : DecSetoid _ _
  ```

* In `Data.DifferenceList.Base`:
  ```agda
  viaList : (List A → List B) → (DiffList A → DiffList B)
  ```

* In `Data.DifferenceList.Properties`:
  ```agda
  viaList⁺ : (f : List A → List B) → xs ∼ ys → f xs ∼ viaList f ys
  ```

* In `Data.Integer.DivMod`:
  ```agda
  sn%d≡0⇒-[1+n]/ℕd≡-[1+n/d] : ∀ n d .{{_ : ℕ.NonZero d}} →
                              ℕ.suc n ℕ.% d ≡ 0 → -[1+ n ] /ℕ d ≡ -[1+ n ℕ./ d ]
  n<0⇒n/ℕd<0 : ∀ n d .{{_ : ℕ.NonZero d}} → n < 0ℤ → (n /ℕ d) < 0ℤ
  0/ℕd≡0 : ∀ d .{{_ : ℕ.NonZero d}} → + 0 /ℕ d ≡ + 0
  0/d≡0 : ∀ d .{{_ : NonZero d}} → + 0 / d ≡ + 0
  n/ℕ1≡n : ∀ n → n /ℕ 1 ≡ n
  n/1≡n : ∀ n → n / + 1 ≡ n
  n/ℕd≡0⇒∣n∣<d : ∀ n d .{{_ : ℕ.NonZero d}} → n /ℕ d ≡ 0ℤ → ∣ n ∣ ℕ.< d
  n/d≡0⇒n<∣d∣ : ∀ n d .{{_ : NonZero d}} → n / d ≡ 0ℤ → n < + ∣ d ∣
  n/d≡0⇒nonNeg-n : ∀ n d .{{_ : NonZero d}} → n / d ≡ 0ℤ → NonNegative n
  0≤n<d⇒n/ℕd≡0 : ∀ n d .{{_ : NonNegative n }} .{{_ : ℕ.NonZero d}} →
                 n < + d → n /ℕ d ≡ 0ℤ
  0≤n<∣d∣⇒n/d≡0 : ∀ n d .{{_ : NonNegative n }} .{{_ : NonZero d}} →
                  n < + ∣ d ∣ → n / d ≡ 0ℤ
  /ℕ-monoˡ-≤ : ∀ d .{{_ : ℕ.NonZero d}} → Monotonic₁ _≤_ _≤_ (_/ℕ d)
  /ℕ-monoʳ-≤-nonNeg : ∀ n {d₁ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}}
                      .{{_ : NonNegative n}} → d₁ ℕ.≤ d₂ → n /ℕ d₂ ≤ n /ℕ d₁
  /ℕ-monoʳ-≤-nonPos : ∀ n {d₁ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}}
                      .{{_ : NonPositive n}} → d₁ ℕ.≤ d₂ → n /ℕ d₁ ≤ n /ℕ d₂
  /-monoˡ-≤-pos : ∀ d .{{_ : NonZero d}} .{{_ : Positive d}} →
                      Monotonic₁ _≤_ _≤_ (_/ d)
  /-monoˡ-≤-neg : ∀ d .{{_ : NonZero d}} .{{_ : Negative d}} →
                  Monotonic₁ _≤_ _≥_ (_/ d)
  /-monoʳ-≤-nonNeg-eq-signs : ∀ n {d₁ d₂} .{{_ : NonZero d₁}} .{{_ : NonZero d₂}}
                              .{{_ : NonNegative n}} → {sign d₁ ≡ sign d₂} →
                              d₁ ≤ d₂ → n / d₁ ≥ n / d₂
  /-monoʳ-≤-nonPos-eq-signs : ∀ n {d₁ d₂} .{{_ : NonZero d₁}} .{{_ : NonZero d₂}}
                              .{{_ : NonPositive n}} → {sign d₁ ≡ sign d₂} →
                              d₁ ≤ d₂ → n / d₁ ≤ n / d₂
  /-monoʳ-≤-nonNeg-op-signs : ∀ n {d₁ d₂} .{{_ : NonZero d₁}} .{{_ : NonZero d₂}}
                              .{{_ : NonNegative n}} →
                              {sign d₁ ≡ opposite (sign d₂)} →
                              d₁ ≤ d₂ → n / d₁ ≤ n / d₂
  /-monoʳ-≤-nonPos-op-signs : ∀ n {d₁ d₂} .{{_ : NonZero d₁}} .{{_ : NonZero d₂}}
                              .{{_ : NonPositive n}} →
                              {sign d₁ ≡ opposite (sign d₂)} →
                              d₁ ≤ d₂ → n / d₁ ≥ n / d₂
  ```

* In `Data.Integer.GCD`:
  ```agda
  gcd[i,i]≡∣i∣ : ∀ i → gcd i i ≡ + ∣i∣
  ```

* In `Data.Integer.Properties`:
  ```agda
  i≤∣i∣ : ∀ i → i ≤ + ∣ i ∣
  ```

* In `Data.List.Membership.Propositional.Properties`:
  ```agda
  foldl-selective : Selective _≡_ _•_ → ∀ e xs →
                    (foldl _•_ e xs ≡ e) ⊎ (foldl _•_ e xs ∈ xs)
  ```

* In `Data.List.Membership.Setoid.Properties`:
  ```agda
  foldl-selective : Selective _≈_ _•_ → ∀ e xs →
                    (foldl _•_ e xs ≈ e) ⊎ (foldl _•_ e xs ∈ xs)
   ```

* In `Data.List.Relation.Ternary.Appending.Setoid.Properties`:
  ```agda
  assoc← : ∃[ ys ] Appending bs cs ys × Appending as ys ds →
           ∃[ xs ] Appending as bs xs × Appending xs cs ds
  ```

* In `Data.Nat.DivMod`:
  ```agda
  m<suc[m/n]*n : ∀ m n → m < suc (m / n) * n
  %-pred-≡suc : ∀ m d k .{{_ : NonZero d}} → suc m % d ≡ suc k → m % d ≡ k
  sn%d≡0⇒sn/d≡s[n/d] : ∀ n d .{{_ : NonZero d}} → suc n % d ≡ 0 →
                       suc n / d ≡ suc (n / d)
  sn%d>0⇒sn/d≡n/d : ∀ n d .{{_ : NonZero d}} →
                    0 < suc n % d → suc n / d ≡ n / d
  ```

* In `Data.Nat.GCD`:
  ```agda
  gcd[n,n]≡n : ∀ n → gcd n n ≡ n
  ```

* In `Data.Nat.ListAction`:
  ```agda
  minimum : ℕ → List ℕ → ℕ
  maximum : ℕ → List ℕ → ℕ
  ```

* In `Data.Nat.ListAction.Properties`:
  ```agda
  minimum-spec : ∀ n ms → minimum n ms ≡ foldl ℕ._⊓_ n ms
  minimum-selective : ∀ n ms → minimum n ms ∈ n ∷ ms
  minimum-≤ : ∀ n ms {k} → k ∈ (n ∷ ms) → minimum n ms ≤ k
  maximum-spec : ∀ n ms → maximum n ms ≡ foldl ℕ._⊔_ n ms
  maximum-selective : ∀ n ms → maximum n ms ∈ n ∷ ms
  maximum-≥ : ∀ n ms {k} → k ∈ (n ∷ ms) → maximum n ms ≥ k
  product-locate : ∀ ns → product ns ≡ 0 → 0 ∈ ns
  ```

* In `Data.Nat.Properties`:
  ```agda
  m≢0⇒m+n≢0     : ∀ m n .{{_ : NonZero m}} → NonZero (m + n)
  n≢0⇒m+n≢0     : ∀ m n .{{_ : NonZero n}} → NonZero (m + n)
  m≢0∧n≢0⇒m+n≢0 : ∀ m .{{_ : NonZero m}} n .{{_ : NonZero n}} → NonZero (m + n)
  m+n≢0⇒m≢0∨n≢0 : ∀ m n .{{_ : NonZero (m + n)} → NonZero m ⊎ NonZero n
  *-almostCancelʳ-≡ : AlmostRightCancellative 0 _*_
  ```

* In `Data.Rational.Properties`:
  ```agda
  ↥[i/1]≡i  : (i : ℤ) → ↥ (i / 1) ≡ i
  ↧ₙ[i/1]≡1 : (i : ℤ) → ↧ₙ (i / 1) ≡ 1
  n/n≡1 : ∀ (n : ℕ) .{{_ : ℕ.NonZero n}} → + n / n ≡ 1ℚ
  -i/n≡-[i/n] : ∀ (i : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n}} →
                ℤ.- i / n ≡ - (i / n)
  *-cancelˡ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (p ℕ.* r)}} →
                (+ p ℤ.* q) / (p ℕ.* r) ≡ q / r
  *-cancelʳ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (r ℕ.* p)}} →
                (q ℤ.* + p) / (r ℕ.* p) ≡ q / r
  i/n+j/n≡[i+j]/n : ∀ (i j : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n }} →
                    i / n + j / n ≡ (i ℤ.+ j) / n
  toℚᵘ-/ᵘ-≡ : ∀ q → toℚᵘ q ≡ ↥ q /ᵘ ↧ₙ q
  toℚᵘ-/ᵘ-≃ : ∀ n d .{{_ : ℕ.NonZero d}} → toℚᵘ (n / d) ≃ᵘ n /ᵘ d
  n/d≡[n/a]*[a/d] : ∀ n d a .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero a}} →
                  n / d ≡ (n / a) * (+ a / d)
  /-distribʳ-+ : ∀ d n₁ n₂ .{{_ : ℕ.NonZero d}} → (n₁ ℤ.+ n₂) / d ≡ n₁ / d + n₂ / d
  /-monoˡ-< : ∀ d .{{_ : ℕ.NonZero d}} → Monotonic₁ ℤ._<_ _<_ (_/ d)
  /-monoʳ-<-pos : ∀ n {d₁ d₂} .{{_ : ℤ.Positive n}}
                .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                d₁ ℕ.< d₂ → n / d₂ < n / d₁
  /-monoʳ-<-neg : ∀ n {d₁ d₂} .{{_ : ℤ.Negative n}}
                .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                d₁ ℕ.< d₂ → n / d₁ < n / d₂
  /-monoˡ-≤ : ∀ d .{{_ : ℕ.NonZero d}} → Monotonic₁ ℤ._≤_ _≤_ (_/ d)
  /-monoʳ-≤-nonNeg : ∀ n {d₁ d₂} .{{_ : ℤ.NonNegative n}}
                   .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                   d₁ ℕ.≤ d₂ → n / d₂ ≤ n / d₁
  /-monoʳ-≤-nonPos : ∀ n {d₁ d₂} .{{_ : ℤ.NonPositive n}}
                   .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                   d₁ ℕ.≤ d₂ → n / d₁ ≤ n / d₂
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```agda
  ↧ₙ[n/d]≡d : ∀ n d .{{_ : ℕ.NonZero d}} → ↧ₙ (n / d) ≡ d
  n/d≡[n/1]*[1/d] : ∀ n d .{{_ : ℕ.NonZero d}} → n / d ≡ (n / 1) * (1ℤ / d)
  n/d≃[n/a]*[a/d] : ∀ n d a .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero a}} →
                    n / d ≃ (n / a) * (ℤ.+ a / d)
  /-distribʳ-+ : ∀ d n₁ n₂ .{{_ : ℕ.NonZero d}} → (n₁ ℤ.+ n₂) / d ≃ n₁ / d + n₂ / d
  /-monoˡ-< : ∀ d .{{_ : ℕ.NonZero d}} → Monotonic₁ ℤ._<_ _<_ (_/ d)
  /-monoʳ-<-pos : ∀ n {d₁ d₂} .{{_ : ℤ.Positive n}}
                  .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                  d₁ ℕ.< d₂ → n / d₂ < n / d₁
  /-monoʳ-<-neg : ∀ n {d₁ d₂} .{{_ : ℤ.Negative n}}
                  .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                  d₁ ℕ.< d₂ → n / d₁ < n / d₂
  /-monoˡ-≤ : ∀ d .{{_ : ℕ.NonZero d}} → Monotonic₁ ℤ._≤_ _≤_ (_/ d)
  /-monoʳ-≤-nonNeg : ∀ n {d₁ d₂} .{{_ : ℤ.NonNegative n}}
                     .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                     d₁ ℕ.≤ d₂ → n / d₂ ≤ n / d₁
  /-monoʳ-≤-nonPos : ∀ n {d₁ d₂} .{{_ : ℤ.NonPositive n}}
                   .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}} →
                   d₁ ℕ.≤ d₂ → n / d₁ ≤ n / d₂
  ```

* In `Data.Vec.Properties`:
  ```agda
  lookup-head : (xs : Vec A (suc n)) → lookup xs zero ≡ head xs
  lookup-tail : (xs : Vec A (suc n)) → lookup xs (suc i) ≡ lookup (tail xs) i
  ```

* In `Relation.Binary.Definitions`:
  ```agda
  module KleeneAlgebra (_≤_ : Rel A ℓ₁) where
    StarLeftExpansive     : ∀ (e : A) (_+_ _*_ : Fun₂ A) (_⋆ : Fun₁ A) → Set _
    StarRightExpansive    : ∀ (e : A) (_+_ _*_ : Fun₂ A) (_⋆ : Fun₁ A) → Set _
    StarExpansive         : ∀ (e : A) (_+_ _*_ : Fun₂ A) (_⋆ : Fun₁ A) → Set _
    StarLeftDestructive   : ∀ (_+_ _*_ : Fun₂ A) (_⋆ : Fun₁ A) → Set _
    StarRightDestructive  : ∀ (_+_ _*_ : Fun₂ A) (_⋆ : Fun₁ A) → Set _
    StarDestructive       : ∀ (_+_ _*_ : Fun₂ A) (_⋆ : Fun₁ A) → Set _
  ```
