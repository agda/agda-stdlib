Version 2.0-dev
===============

The library has been tested using Agda 2.6.2.

Highlights
----------

* A golden testing library in `Test.Golden`. This allows you to run a set
  of tests and make sure their output matches an expected `golden' value.
  The test runner has many options: filtering tests by name, dumping the
  list of failures to a file, timing the runs, coloured output, etc.
  Cf. the comments in `Test.Golden` and the standard library's own tests
  in `tests/` for documentation on how to use the library.

Bug-fixes
---------

* In `System.Exit`, the `ExitFailure` constructor is now carrying an integer
  rather than a natural. The previous binding was incorrectly assuming that
  all exit codes where non-negative.

* In `/-monoˡ-≤` in `Data.Nat.DivMod` the parameter `o` was implicit but not inferrable. 
  It has been changed to be explicit.

* In `Function.Definitions` the definitions of `Surjection`, `Inverseˡ`, 
  `Inverseʳ` were not being re-exported correctly and therefore had an unsolved 
  meta-variable whenever this module was explicitly parameterised. This has
  been fixed.

Non-backwards compatible changes
--------------------------------

* In `Algebra.Morphism.Structures`, `IsNearSemiringHomomorphism`,
  `IsSemiringHomomorphism`, and `IsRingHomomorphism` have been redeisgned to
  build up from `IsMonoidHomomorphism`, `IsNearSemiringHomomorphism`, and
  `IsSemiringHomomorphism` respectively, adding a single property at each step.
  This means that they no longer need to have two separate proofs of
  `IsRelHomomorphism`. Similarly, `IsLatticeHomomorphism` is now built as
  `IsRelHomomorphism` along with proofs that `_∧_` and `_∨_` are homorphic.

  Also, `⁻¹-homo` in `IsRingHomomorphism` has been renamed to `-‿homo`.

* move definition of `_>>=_` under `Data.Vec.Base` to its submodule `CartesianBind`
  in order to keep another new definition of `_>>=_`, located in `DiagonalBind`
  which is also a submodule of `Data.Vec.Base`.

* In `Text.Pretty`, `Doc` is now a record rather than a type alias. This
  helps Agda reconstruct the `width` parameter when the module is opened
  without it being applied. In particular this allows users to write
  width-generic pretty printers and only pick a width when calling the
  renderer by using this import style:
  ```
  open import Text.Pretty using (Doc; render)
  --                      ^-- no width parameter for Doc & render
  open module Pretty {w} = Text.Pretty w hiding (Doc; render)
  --                 ^-- implicit width parameter for the combinators

  pretty : Doc w
  pretty = ? -- you can use the combinators here and there won't be any
             -- issues related to the fact that `w` cannot be reconstructed
             -- anymore

  main = do
    -- you can now use the same pretty with different widths:
    putStrLn $ render 40 pretty
    putStrLn $ render 80 pretty
  ```

* In `Text.Regex.Search` the `searchND` function finding infix matches has
  been tweaked to make sure the returned solution is a local maximum in terms
  of length. It used to be that we would make the match start as late as
  possible and finish as early as possible. It's now the reverse.

  So `[a-zA-Z]+.agdai?` run on "the path _build/Main.agdai corresponds to"
  will return "Main.agdai" when it used to be happy to just return "n.agda".

#### Removed deprecated names

* All modules and names that were deprecated prior to v1.0 have been removed.

#### Proofs of non-zeroness as instance arguments

* Many numeric operations in the library require their arguments to be non-zero.
  The previous way of constructing and passing round these proofs resulted in clunky code.
  As described on the [mailing list](https://lists.chalmers.se/pipermail/agda/2021/012693.html)
  we have converted the operations to take the proofs of non-zeroness as irrelevant 
  [instance arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).
  See the mailing list for a fuller explanation of the motivation and implementation.

* For example the type signature of division is now:
  ```
  _/_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
  ```
  which means that as long as an instance of `NonZero n` is in scope then you can write
  `m / n` without having to explicitly provide a proof as instance search will fill it in
  for you. The full list of such operations changed is as follows:
    - In `Data.Nat.DivMod`: `_/_`, `_%_`, `_div_`, `_mod_`
	- In `Data.Nat.Pseudorandom.LCG`: `Generator`
	- In `Data.Integer.DivMod`: `_divℕ_`, `_div_`, `_modℕ_`, `_mod_`
	- In `Data.Rational`: `mkℚ+`, `normalize`, `_/_`, `1/_`
	- In `Data.Rational.Unnormalised`: `_/_`, `1/_`, `_÷_`

* Consequently the definition of `_≢0` has been removed from `Data.Rational.Unnormalised.Base`
  and the following proofs about it have been removed from `Data.Rational.Unnormalised.Properties`:
  ```
  p≄0⇒∣↥p∣≢0 : ∀ p → p ≠ 0ℚᵘ → ℤ.∣ (↥ p) ∣ ≢0
  ∣↥p∣≢0⇒p≄0 : ∀ p → ℤ.∣ (↥ p) ∣ ≢0 → p ≠ 0ℚᵘ
  ```

* At the moment, there are 4 different ways such instance arguments can be provided,
  listed in order of convenience and clarity:
    1. By default there is always an instance of `NonZero (suc n)` for any `n` which 
	   will be picked up automatically:
	   ```
	   0/n≡0 : 0 / suc n ≡ 0
	   ```
	2. You can take the proof an instance argument as a parameter, e.g. 
	   ```
	   0/n≡0 : {{_ : NonZero n}} → 0 / n ≡ 0
	   ```
	3. You can define an instance argument in scope higher-up (or in a `where` clause):
	   ```
	   instance 
	     n≢0 : NonZero n
	     n≢0 = ...

	   0/n≡0 : 0 / n ≡ 0
	   ```
	4. You can provide the instance argument explicitly, e.g. `0/n≡0 : ∀ n (n≢0 : NonZero n) → ((0 / n) {{n≢0}}) ≡ 0`
	   ```
	   0/n≡0 : ∀ n (n≢0 : NonZero n) → ((0 / n) {{n≢0}}) ≡ 0
	   ```

* Previously one of the hacks used in proofs was to explicitly put everything in the form `suc n`.
  This often made the proofs extremely difficult to use if you're term wasn't in that form. These
  proofs have now all been updated to use instance arguments instead, e.g.
  ```
  n/n≡1 : ∀ n → suc n / suc n ≡ 1 
  ```
  becomes
  ```
  n/n≡1 : ∀ n {{_ : NonZero n}} → n / n ≡ 1
  ```
  This does however mean that if you passed in the value `x` to these proofs before, then you
  will now have to pass in `suc x`. The full list of such proofs is below:
  - In `Data.Nat.Properties`:
	```agda
	*-cancelʳ-≡ : ∀ m n {o} → m * suc o ≡ n * suc o → m ≡ n
	*-cancelˡ-≡ : ∀ {m n} o → suc o * m ≡ suc o * n → m ≡ n
	*-cancelʳ-≤ : ∀ m n o → m * suc o ≤ n * suc o → m ≤ n
	*-cancelˡ-≤ : ∀ {m n} o → suc o * m ≤ suc o * n → m ≤ n
	*-monoˡ-<   : ∀ n → (_* suc n) Preserves _<_ ⟶ _<_
	*-monoʳ-<   : ∀ n → (suc n *_) Preserves _<_ ⟶ _<_
	```

  - In `Data.Nat.DivMod`:
	```agda
    m≡m%n+[m/n]*n : ∀ m n → m ≡ m % suc n + (m / suc n) * suc n
    m%n≡m∸m/n*n   : ∀ m n → m % suc n ≡ m ∸ (m / suc n) * suc n
    n%n≡0         : ∀ n → suc n % suc n ≡ 0
    m%n%n≡m%n     : ∀ m n → m % suc n % suc n ≡ m % suc n
    [m+n]%n≡m%n   : ∀ m n → (m + suc n) % suc n ≡ m % suc n
    [m+kn]%n≡m%n  : ∀ m k n → (m + k * (suc n)) % suc n ≡ m % suc n
    m*n%n≡0       : ∀ m n → (m * suc n) % suc n ≡ 0
    m%n<n         : ∀ m n → m % suc n < suc n
    m%n≤m         : ∀ m n → m % suc n ≤ m
    m≤n⇒m%n≡m     : ∀ {m n} → m ≤ n → m % suc n ≡ m
    ```

  - In `Data.Nat.Divisibility`
    ```agda
    m%n≡0⇒n∣m : ∀ m n → m % suc n ≡ 0 → suc n ∣ m
    n∣m⇒m%n≡0 : ∀ m n → suc n ∣ m → m % suc n ≡ 0
    m%n≡0⇔n∣m : ∀ m n → m % suc n ≡ 0 ⇔ suc n ∣ m
	∣⇒≤       : ∀ {m n} → m ∣ suc n → m ≤ suc n
	>⇒∤        : ∀ {m n} → m > suc n → m ∤ suc n
	*-cancelˡ-∣ : ∀ {i j} k → suc k * i ∣ suc k * j → i ∣ j
	```

  - In `Data.Nat.GCD`
    ```
    GCD-* : ∀ {m n d c} → GCD (m * suc c) (n * suc c) (d * suc c) → GCD m n d
	gcd[m,n]≤n : ∀ m n → gcd m (suc n) ≤ suc n
    ```

  - In `Data.Nat.Coprimality`:
	```
	Bézout-coprime : ∀ {i j d} → Bézout.Identity (suc d) (i * suc d) (j * suc d) → Coprime i j
	```
	
  - In `Data.Integer.Properties`:
	```
	sign-◃    : ∀ s n → sign (s ◃ suc n) ≡ s
	sign-cong : ∀ {s₁ s₂ n₁ n₂} → s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
	-◃<+◃     : ∀ m n → Sign.- ◃ (suc m) < Sign.+ ◃ n
	m⊖1+n<m   : ∀ m n → m ⊖ suc n < + m
    ```

  - In `Data.Integer.Divisibility`:
	```
	*-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
	*-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
	```

  - In `Data.Integer.Divisibility.Signed`:
	```
    *-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
	*-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
	```

* A couple of other proofs in have also changed form:
  - In `Data.Nat.Properties`:
  ```
  m≤m*n          : ∀ m {n} → 0 < n → m ≤ m * n 
  m≤n*m          : ∀ m {n} → 0 < n → m ≤ n * m
  m<m*n          : ∀ {m n} → 0 < m → 1 < n → m < m * n
  suc[pred[n]]≡n : ∀ {n} → n ≢ 0 → suc (pred n) ≡ n
  ```
  - In `Data.Nat.DivMod`:
  ```
  m/n<m         : ∀ m n {≢0} → m ≥ 1 → n ≥ 2 → (m / n) {≢0} < m
  ```
  - In `Data.Integer.Properties`:
  ```
  *-cancelʳ-≡ : ∀ i j k → k ≢ + 0 → i * k ≡ j * k → i ≡ j
  *-cancelˡ-≡ : ∀ i j k → i ≢ + 0 → i * j ≡ i * k → j ≡ k
  *-cancelʳ-≤-pos : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
  ```

### Implementation of division and modulus for `ℤ`

* The previous implementations of `_divℕ_`, `_div_`, `_modℕ_`, `_mod_`
  in `Data.Integer.DivMod` internally converted to the unary `Fin` datatype
  resulting in poor performance. The implementation has been updated to
  use the corresponding operations from `Data.Nat.DivMod` which are 
  efficiently implemented using the Haskell backend.

### Strict functions

* The module `Strict` has been deprecated in favour of `Function.Strict`
  and the definitions of strict application, `_$!_` and `_$!′_`, have been
  moved from `Function.Base` to `Function.Strict`.

* The contents of `Function.Strict` is now re-exported by `Function`.

### Other

* The constructors `+0` and `+[1+_]` from `Data.Integer.Base` are no longer
  exported by `Data.Rational.Base`. You will have to open `Data.Integer(.Base)`
  directly to use them.

* The first two arguments of `m≡n⇒m-n≡0` (now `i≡j⇒i-j≡0`) in `Data.Integer.Base`
  have been made implicit.

* The relations `_≤_` `_≥_` `_<_` `_>_` in `Data.Fin.Base` have been
  generalised so they can now relate `Fin` terms with different indices.
  Should be mostly backwards compatible, but very occasionally when proving
  properties about the orderings themselves the second index must be provided
  explicitly.

  ### Creation of `Relation.Binary.Lattice` hierarchy
  * In order to improve modularity Relation.Binary.Lattice is split out into Relation.Binary.Lattice.(Definitions/Structures/Bundles).
  ###

Deprecated modules
------------------

### Deprecation of old function hierarchy

* The module `Function.Related` has been deprecated in favour of `Function.Related.Propositional`
  whose code uses the new function hierarchy. This also opens up the possibility of a more
  general `Function.Related.Setoid` at a later date. Several of the names have been changed
  in this process to bring them into line with the camelcase naming convention used
  in the rest of the library:
  ```agda
  reverse-implication ↦ reverseImplication 
  reverse-injection   ↦ reverseInjection
  left-inverse        ↦ leftInverse
  
  Symmetric-kind      ↦ SymmetricKind
  Forward-kind        ↦ ForwardKind
  Backward-kind       ↦ BackwardKind
  Equivalence-kind    ↦ EquivalenceKind
  ```


Deprecated names
----------------

* In `Data.Integer.Properties` references to variables in names have
  been made consistent so that `m`, `n` always refer to naturals and
  `i` and `j` always refer to integers:
  ```
  n≮n            ↦  i≮i
  ∣n∣≡0⇒n≡0      ↦  ∣i∣≡0⇒i≡0
  ∣-n∣≡∣n∣       ↦  ∣-i∣≡∣i∣
  0≤n⇒+∣n∣≡n     ↦  0≤i⇒+∣i∣≡i
  +∣n∣≡n⇒0≤n     ↦  +∣i∣≡i⇒0≤i
  +∣n∣≡n⊎+∣n∣≡-n ↦  +∣i∣≡i⊎+∣i∣≡-i
  ∣m+n∣≤∣m∣+∣n∣  ↦  ∣i+j∣≤∣i∣+∣j∣
  ∣m-n∣≤∣m∣+∣n∣  ↦  ∣i-j∣≤∣i∣+∣j∣
  signₙ◃∣n∣≡n    ↦  signᵢ◃∣i∣≡i
  ◃-≡            ↦  ◃-cong
  ∣m-n∣≡∣n-m∣    ↦  ∣i-j∣≡∣j-i∣
  m≡n⇒m-n≡0      ↦  i≡j⇒i-j≡0
  m-n≡0⇒m≡n      ↦  i-j≡0⇒i≡j
  m≤n⇒m-n≤0      ↦  i≤j⇒i-j≤0
  m-n≤0⇒m≤n      ↦  i-j≤0⇒i≤j
  m≤n⇒0≤n-m      ↦  i≤j⇒0≤j-i
  0≤n-m⇒m≤n      ↦  0≤i-j⇒j≤i
  n≤1+n          ↦  i≤suc[i]
  n≢1+n          ↦  i≢suc[i]
  m≤pred[n]⇒m<n  ↦  i≤pred[j]⇒i<j
  m<n⇒m≤pred[n]  ↦  i<j⇒i≤pred[j]
  -1*n≡-n        ↦  -1*i≡-i
  m*n≡0⇒m≡0∨n≡0  ↦  i*j≡0⇒i≡0∨j≡0
  ∣m*n∣≡∣m∣*∣n∣  ↦  ∣i*j∣≡∣i∣*∣j∣
  +-pos-monoʳ-≤  ↦  +-monoʳ-≤
  +-neg-monoʳ-≤  ↦  +-monoʳ-≤
  ```
  
* In `Data.Nat.Properties`:
  ```
  suc[pred[n]]≡n  ↦  suc-pred
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```
  ↥[p/q]≡p  ↦  ↥[n/d]≡n
  ↧[p/q]≡q  ↦  ↧[n/d]≡d
  ```

* In `Data.List.Properties`:
  ```agda
  zipWith-identityˡ  ↦  zipWith-zeroˡ
  zipWith-identityʳ  ↦  zipWith-zeroʳ
  ```

* In `Function.Construct.Composition`:
  ```
  _∘-⟶_   ↦   _⟶-∘_
  _∘-↣_   ↦   _↣-∘_
  _∘-↠_   ↦   _↠-∘_
  _∘-⤖_  ↦   _⤖-∘_
  _∘-⇔_   ↦   _⇔-∘_
  _∘-↩_   ↦   _↩-∘_
  _∘-↪_   ↦   _↪-∘_
  _∘-↔_   ↦   _↔-∘_
  ```

  * In `Function.Construct.Identity`:
  ```
  id-⟶   ↦   ⟶-id
  id-↣   ↦   ↣-id
  id-↠   ↦   ↠-id
  id-⤖  ↦   ⤖-id
  id-⇔   ↦   ⇔-id
  id-↩   ↦   ↩-id
  id-↪   ↦   ↪-id
  id-↔   ↦   ↔-id
  ```

* In `Function.Construct.Symmetry`:
  ```
  sym-⤖   ↦   ⤖-sym
  sym-⇔   ↦   ⇔-sym
  sym-↩   ↦   ↩-sym
  sym-↪   ↦   ↪-sym
  sym-↔   ↦   ↔-sym
  ```

New modules
-----------

* Identity morphisms and composition of morphisms between algebraic structures:
  ```
  Algebra.Morphism.Construct.Composition
  Algebra.Morphism.Construct.Identity
  ```

* Show module for unnormalised rationals:
  ```
  Data.Rational.Unnormalised.Show
  ```

* Properties of bijections:
  ```
  Function.Consequences
  Function.Properties.Bijection
  Function.Properties.RightInverse
  Function.Properties.Surjection
  ```

* Both versions of equality on predications are equivalences
  ```
  Relation.Unary.Relation.Binary.Equality
  ```

* Polymorphic verstions of some unary relations
 ```
 Relation.Unary.Polymorphic
 ```
 
* Various system types and primitives:
  ```
  System.Clock.Primitive
  System.Clock
  System.Console.ANSI
  System.Directory.Primitive
  System.Directory
  System.FilePath.Posix.Primitive
  System.FilePath.Posix
  System.Process.Primitive
  System.Process
  ```

* A golden testing library with test pools, an options parser, a runner:
  ```
  Test.Golden
  ```

* A small library for function arguments with default values:
  ```
  Data.Default
  ```

Other minor changes
-------------------

* The module `Algebra` now publicly re-exports the contents of
  `Algebra.Structures.Biased`.

* Added new definitions to `Algebra.Bundles`:
  ```agda
  record UnitalMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Quasigroup  c ℓ : Set (suc (c ⊔ ℓ))
  record Loop c ℓ : Set (suc (c ⊔ ℓ))
  record RawField c ℓ : Set (suc (c ⊔ ℓ)
  record Field c ℓ : Set (suc (c ⊔ ℓ))
  ```
  and the existing record `Lattice` now provides
  ```agda
  ∨-commutativeSemigroup : CommutativeSemigroup c ℓ
  ∧-commutativeSemigroup : CommutativeSemigroup c ℓ
  ```
  and their corresponding algebraic subbundles.

* Added new proofs to `Algebra.Consequences.Setoid`:
  ```agda
  comm+idˡ⇒id       : Commutative _•_ → LeftIdentity  e _•_ → Identity e _•_
  comm+idʳ⇒id       : Commutative _•_ → RightIdentity e _•_ → Identity e _•_
  comm+zeˡ⇒ze       : Commutative _•_ → LeftZero      e _•_ → Zero     e _•_
  comm+zeʳ⇒ze       : Commutative _•_ → RightZero     e _•_ → Zero     e _•_
  comm+distrˡ⇒distr : Commutative _•_ → _•_ DistributesOverˡ _◦_ → _•_ DistributesOver _◦_
  comm+distrʳ⇒distr : Commutative _•_ → _•_ DistributesOverʳ _◦_ → _•_ DistributesOver _◦_
  ```

* Added new functions to `Algebra.Construct.DirectProduct`:
  ```agda
  rawSemiring : RawSemiring a ℓ₁ → RawSemiring b ℓ₂ → RawSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  rawRing : RawRing a ℓ₁ → RawRing b ℓ₂ → RawRing (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero a ℓ₁ →
                                    SemiringWithoutAnnihilatingZero b ℓ₂ →
                                    SemiringWithoutAnnihilatingZero (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  semiring : Semiring a ℓ₁ → Semiring b ℓ₂ → Semiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  commutativeSemiring : CommutativeSemiring a ℓ₁ → CommutativeSemiring b ℓ₂ →
                        CommutativeSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  ring : Ring a ℓ₁ → Ring b ℓ₂ → Ring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  commutativeRing : CommutativeRing a ℓ₁ → CommutativeRing b ℓ₂ →
                    CommutativeRing (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
 ```
	
* Added new definitions to `Algebra.Structures`:
  ```agda
  record IsUnitalMagma (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  record IsQuasigroup  (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  record IsLoop (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  record IsField (+ * : Op₂ A)(-_ 1#/_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ)
  ```
  and the existing record `IsLattice` now provides
  ```
  ∨-isCommutativeSemigroup : IsCommutativeSemigroup ∨
  ∧-isCommutativeSemigroup : IsCommutativeSemigroup ∧
  ```
  and their corresponding algebraic substructures.

* Added new proofs in `Data.Integer.Properties`:
  ```agda
  sign-cong′ : s₁ ◃ n₁ ≡ s₂ ◃ n₂ → s₁ ≡ s₂ ⊎ (n₁ ≡ 0 × n₂ ≡ 0)
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  m*n≡0⇒m≡0 : .{{_ : NonZero n}} → m * n ≡ 0 → m ≡ 0
  ```

* Added new proofs in `Data.Nat.DivMod`:
  ```agda
  m%n≤n : .{{_ : NonZero n}} → m % n ≤ n
  ```

* Added new definitions and proofs in `Data.Rational.Properties`:
  ```agda
  +-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
  +-*-rawSemiring : RawSemiring 0ℓ 0ℓ
  toℚᵘ-isNearSemiringHomomorphism-+-* : IsNearSemiringHomomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
  toℚᵘ-isNearSemiringMonomorphism-+-* : IsNearSemiringMonomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
  toℚᵘ-isSemiringHomomorphism-+-* : IsSemiringHomomorphism +-*-rawSemiring ℚᵘ.+-*-rawSemiring toℚᵘ
  toℚᵘ-isSemiringMonomorphism-+-* : IsSemiringMonomorphism +-*-rawSemiring ℚᵘ.+-*-rawSemiring toℚᵘ
  ```

* Added new definitions in `Data.Rational.Unnormalised.Properties`:
  ```agda
  +-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
  +-*-rawSemiring : RawSemiring 0ℓ 0ℓ
  ```

* Added new proof to `Data.Product.Properties`:
  ```agda
  map-cong : f ≗ g → h ≗ i → map f h ≗ map g i
  ```

* Added new proofs in `Data.String.Properties`:
  ```
  ≤-isDecTotalOrder-≈ : IsDecTotalOrder _≈_ _≤_
  ≤-decTotalOrder-≈   :  DecTotalOrder _ _ _
  ```

* Added new definitions in `Data.Vec.Base`:
  ```agda
  diagonal : ∀ {n} → Vec (Vec A n) n → Vec A n
  DiagonalBind._>>=_ : ∀ {n} → Vec A n → (A → Vec B n) → Vec B n
  ```

* Added new instance in `Data.Vec.Categorical`:
  ```agda
  monad : RawMonad (λ (A : Set a) → Vec A n)
  ```

* Added new proofs in `Data.Vec.Properties`:
  ```agda
  map-const : ∀ {n} (xs : Vec A n) (x : B) → map {n = n} (const x) xs ≡ replicate x
  map-⊛ : ∀ {n} (f : A → B → C) (g : A → B) (xs : Vec A n) → (map f xs ⊛ map g xs) ≡ map (f ˢ g) xs
  ⊛-is->>= : ∀ {n} (fs : Vec (A → B) n) (xs : Vec A n) → (fs ⊛ xs) ≡ (fs DiagonalBind.>>= flip map xs)
  transpose-replicate : ∀ {m n} (xs : Vec A m) → transpose (replicate {n = n} xs) ≡ map replicate xs
  ```

* Added new proofs in `Function.Construct.Symmetry`:
  ```
  bijective     : Bijective ≈₁ ≈₂ f → Symmetric ≈₂ → Transitive ≈₂ → Congruent ≈₁ ≈₂ f → Bijective ≈₂ ≈₁ f⁻¹
  isBijection   : IsBijection ≈₁ ≈₂ f → Congruent ≈₂ ≈₁ f⁻¹ → IsBijection ≈₂ ≈₁ f⁻¹
  isBijection-≡ : IsBijection ≈₁ _≡_ f → IsBijection _≡_ ≈₁ f⁻¹
  bijection     : Bijection R S → Congruent IB.Eq₂._≈_ IB.Eq₁._≈_ f⁻¹ → Bijection S R
  bijection-≡   : Bijection R (setoid B) → Bijection (setoid B) R
  sym-⤖        : A ⤖ B → B ⤖ A
  ```

* Added new operations in `Function.Strict`:
  ```
  _!|>_  : (a : A) → (∀ a → B a) → B a
  _!|>′_ : A → (A → B) → B
  ```

* Added new definition to the `Surjection` module in `Function.Related.Surjection`:
  ```
  f⁻ = proj₁ ∘ surjective
  ```

* Added new operations in `IO`:
  ```
  Colist.forM  : Colist A → (A → IO B) → IO (Colist B)
  Colist.forM′ : Colist A → (A → IO B) → IO ⊤

  List.forM  : List A → (A → IO B) → IO (List B)
  List.forM′ : List A → (A → IO B) → IO ⊤
  ```

* Added new operations in `IO.Base`:
  ```
  lift! : IO A → IO (Lift b A)
  _<$_  : B → IO A → IO B
  _=<<_ : (A → IO B) → IO A → IO B
  _<<_  : IO B → IO A → IO B
  lift′ : Prim.IO ⊤ → IO {a} ⊤

  when   : Bool → IO {a} ⊤ → IO ⊤
  unless : Bool → IO {a} ⊤ → IO ⊤

  whenJust  : Maybe A → (A → IO {a} ⊤) → IO ⊤
  untilJust : IO (Maybe A) → IO A
  ```

* Equality of predicates
  ```
  _≐_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  _≐′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  ```
  
* Added new operations in `System.Exit`:
  ```
  isSuccess : ExitCode → Bool
  isFailure : ExitCode → Bool
  ```
* Added new definitions to `Algebra.Morphism.Structures`:
  ```agda
module FieldMorphisms (F₁ : RawField a ℓ₁) (F₂ : RawField b ℓ₂)
  ```