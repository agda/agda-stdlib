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

### Strict functions

* The module `Strict` has been deprecated in favour of `Function.Strict`
  and the definitions of strict application, `_$!_` and `_$!′_`, have been
  moved from `Function.Base` to `Function.Strict`.

* The contents of `Function.Strict` is now re-exported by `Function`.

### Other

* The constructors `+0` and `+[1+_]` from `Data.Integer.Base` are no longer
  exported by `Data.Rational.Base`. You will have to open `Data.Integer(.Base)`
  directly to use them.

Deprecated modules
------------------

Deprecated names
----------------

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
  Function.Properties.Bijection
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

Other minor additions
---------------------

* Added new definitions to `Algebra.Bundles`:
  ```agda
  record UnitalMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Quasigroup  c ℓ : Set (suc (c ⊔ ℓ))
  record Loop c ℓ : Set (suc (c ⊔ ℓ))
  ```
  and the existing record `Lattice` now provides
  ```agda
  ∨-commutativeSemigroup : CommutativeSemigroup c ℓ
  ∧-commutativeSemigroup : CommutativeSemigroup c ℓ
  ```
  and their corresponding algebraic subbundles.

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
  ```
  and the existing record `IsLattice` now provides
  ```
  ∨-isCommutativeSemigroup : IsCommutativeSemigroup ∨
  ∧-isCommutativeSemigroup : IsCommutativeSemigroup ∧
  ```
  and their corresponding algebraic substructures.

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

* Added new operations in `System.Exit`:
  ```
  isSuccess : ExitCode → Bool
  isFailure : ExitCode → Bool
  ```
