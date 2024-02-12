Version 2.1-dev
===============

The library has been tested using Agda 2.6.4 and 2.6.4.1.

Highlights
----------

Bug-fixes
---------

* Fix statement of `Data.Vec.Properties.toList-replicate`, where `replicate`
  was mistakenly applied to the level of the type `A` instead of the
  variable `x` of type `A`.

Non-backwards compatible changes
--------------------------------

* The modules and morphisms in `Algebra.Module.Morphism.Structures` are now
  parametrized by _raw_ bundles rather than lawful bundles, in line with other
  modules defining morphism structures.
* The definitions in `Algebra.Module.Morphism.Construct.Composition` are now
  parametrized by _raw_ bundles, and as such take a proof of transitivity.
* The definitions in `Algebra.Module.Morphism.Construct.Identity` are now
  parametrized by _raw_ bundles, and as such take a proof of reflexivity.

Other major improvements
------------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Data.Nat.Divisibility.Core`:
  ```agda
  *-pres-∣  ↦  Data.Nat.Divisibility.*-pres-∣
  ```

New modules
-----------

* `Algebra.Module.Bundles.Raw`: raw bundles for module-like algebraic structures

Additions to existing modules
-----------------------------

* In `Algebra.Module.Bundles`, raw bundles are re-exported and the bundles expose their raw counterparts.

* In `Algebra.Module.Construct.DirectProduct`:
  ```agda
  rawLeftSemimodule  : RawLeftSemimodule R m ℓm → RawLeftSemimodule m′ ℓm′ → RawLeftSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawLeftModule      : RawLeftModule R m ℓm → RawLeftModule m′ ℓm′ → RawLeftModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawRightSemimodule : RawRightSemimodule R m ℓm → RawRightSemimodule m′ ℓm′ → RawRightSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawRightModule     : RawRightModule R m ℓm → RawRightModule m′ ℓm′ → RawRightModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawBisemimodule    : RawBisemimodule R m ℓm → RawBisemimodule m′ ℓm′ → RawBisemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawBimodule        : RawBimodule R m ℓm → RawBimodule m′ ℓm′ → RawBimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawSemimodule      : RawSemimodule R m ℓm → RawSemimodule m′ ℓm′ → RawSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawModule          : RawModule R m ℓm → RawModule m′ ℓm′ → RawModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  ```

* In `Algebra.Module.Construct.TensorUnit`:
  ```agda
  rawLeftSemimodule  : RawLeftSemimodule _ c ℓ
  rawLeftModule      : RawLeftModule _ c ℓ
  rawRightSemimodule : RawRightSemimodule _ c ℓ
  rawRightModule     : RawRightModule _ c ℓ
  rawBisemimodule    : RawBisemimodule _ _ c ℓ
  rawBimodule        : RawBimodule _ _ c ℓ
  rawSemimodule      : RawSemimodule _ c ℓ
  rawModule          : RawModule _ c ℓ
  ```

* In `Algebra.Module.Construct.Zero`:
  ```agda
  rawLeftSemimodule  : RawLeftSemimodule R c ℓ
  rawLeftModule      : RawLeftModule R c ℓ
  rawRightSemimodule : RawRightSemimodule R c ℓ
  rawRightModule     : RawRightModule R c ℓ
  rawBisemimodule    : RawBisemimodule R c ℓ
  rawBimodule        : RawBimodule R c ℓ
  rawSemimodule      : RawSemimodule R c ℓ
  rawModule          : RawModule R c ℓ
  ```

* In `Data.Fin.Properties`:
  ```agda
  nonZeroIndex : Fin n → ℕ.NonZero n
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-catMaybes⁺ : All (Maybe.All P) xs → All P (catMaybes xs)
  Any-catMaybes⁺ : All (Maybe.Any P) xs → All P (catMaybes xs)
  ```

* In `Data.List.Relation.Unary.AllPairs.Properties`:
  ```agda
  catMaybes⁺ : AllPairs (Pointwise R) xs → AllPairs R (catMaybes xs)
  tabulate⁺-< : (i < j → R (f i) (f j)) → AllPairs R (tabulate f)
  ```

* In `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  pointwise⊆any : Pointwise R (just x) ⊆ Any (R x)
  ```

* In `Data.Nat.Divisibility`:
  ```agda
  quotient≢0       : m ∣ n → .{{NonZero n}} → NonZero quotient

  m∣n⇒n≡quotient*m : m ∣ n → n ≡ quotient * m
  m∣n⇒n≡m*quotient : m ∣ n → n ≡ m * quotient
  quotient-∣       : m ∣ n → quotient ∣ n
  quotient>1       : m ∣ n → m < n → 1 < quotient
  quotient-<       : m ∣ n → .{{NonTrivial m}} → .{{NonZero n}} → quotient < n
  n/m≡quotient     : m ∣ n → .{{_ : NonZero m}} → n / m ≡ quotient

  m/n≡0⇒m<n    : .{{_ : NonZero n}} → m / n ≡ 0 → m < n
  m/n≢0⇒n≤m    : .{{_ : NonZero n}} → m / n ≢ 0 → n ≤ m

  nonZeroDivisor : DivMod dividend divisor → NonZero divisor
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  m≤n+o⇒m∸n≤o : ∀ m n {o} → m ≤ n + o → m ∸ n ≤ o
  m<n+o⇒m∸n<o : ∀ m n {o} → .{{NonZero o}} → m < n + o → m ∸ n < o
  pred-cancel-≤ : pred m ≤ pred n → (m ≡ 1 × n ≡ 0) ⊎ m ≤ n
  pred-cancel-< : pred m < pred n → m < n
  pred-injective : .{{NonZero m}} → .{{NonZero n}} → pred m ≡ pred n → m ≡ n
  pred-cancel-≡ : pred m ≡ pred n → ((m ≡ 0 × n ≡ 1) ⊎ (m ≡ 1 × n ≡ 0)) ⊎ m ≡ n
  ```

* Added new functions in `Data.String.Base`:
  ```agda
  map : (Char → Char) → String → String
  ```

* Added new proofs in `Data.String.Properties`:
  ```
  ≤-isDecTotalOrder-≈ : IsDecTotalOrder _≈_ _≤_
  ≤-decTotalOrder-≈   :  DecTotalOrder _ _ _
  ```
* Added new definitions in `Data.Sum.Properties`:
  ```
  swap-↔ : (A ⊎ B) ↔ (B ⊎ A)
  ```

* Added new proofs in `Data.Sum.Properties`:
  ```
  map-assocˡ : (f : A → C) (g : B → D) (h : C → F) →
    map (map f g) h ∘ assocˡ ≗ assocˡ ∘ map f (map g h)
  map-assocʳ : (f : A → C) (g : B → D) (h : C → F) →
    map f (map g h) ∘ assocʳ ≗ assocʳ ∘ map (map f g) h
  ```

* Made `Map` public in `Data.Tree.AVL.IndexedMap`

* Added new definitions in `Data.Vec.Base`:
  ```agda
  truncate : m ≤ n → Vec A n → Vec A m
  pad      : m ≤ n → A → Vec A m → Vec A n

  FoldrOp A B = ∀ {n} → A → B n → B (suc n)
  FoldlOp A B = ∀ {n} → B n → A → B (suc n)

  foldr′ : (A → B → B) → B → Vec A n → B
  foldl′ : (B → A → B) → B → Vec A n → B
  countᵇ : (A → Bool) → Vec A n → ℕ

  iterate : (A → A) → A → Vec A n

  diagonal           : Vec (Vec A n) n → Vec A n
  DiagonalBind._>>=_ : Vec A n → (A → Vec B n) → Vec B n
  join               : Vec (Vec A n) n → Vec A n

  _ʳ++_              : Vec A m → Vec A n → Vec A (m + n)

  cast : .(eq : m ≡ n) → Vec A m → Vec A n
  ```

* Added new instance in `Data.Vec.Categorical`:
  ```agda
  monad : RawMonad (λ (A : Set a) → Vec A n)
  ```

* Added new proofs in `Data.Vec.Properties`:
  ```agda
  padRight-refl      : padRight ≤-refl a xs ≡ xs
  padRight-replicate : replicate a ≡ padRight le a (replicate a)
  padRight-trans     : padRight (≤-trans m≤n n≤p) a xs ≡ padRight n≤p a (padRight m≤n a xs)

  truncate-refl     : truncate ≤-refl xs ≡ xs
  truncate-trans    : truncate (≤-trans m≤n n≤p) xs ≡ truncate m≤n (truncate n≤p xs)
  truncate-padRight : truncate m≤n (padRight m≤n a xs) ≡ xs

  map-const    : map (const x) xs ≡ replicate x
  map-⊛        : map f xs ⊛ map g xs ≡ map (f ˢ g) xs
  map-++       : map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-is-foldr : map f ≗ foldr (Vec B) (λ x ys → f x ∷ ys) []
  map-∷ʳ       : map f (xs ∷ʳ x) ≡ (map f xs) ∷ʳ (f x)
  map-reverse  : map f (reverse xs) ≡ reverse (map f xs)
  map-ʳ++      : map f (xs ʳ++ ys) ≡ map f xs ʳ++ map f ys
  map-insert   : map f (insert xs i x) ≡ insert (map f xs) i (f x)
  toList-map   : toList (map f xs) ≡ List.map f (toList xs)

  lookup-concat : lookup (concat xss) (combine i j) ≡ lookup (lookup xss i) j

  ⊛-is->>=    : fs ⊛ xs ≡ fs >>= flip map xs
  lookup-⊛*   : lookup (fs ⊛* xs) (combine i j) ≡ (lookup fs i $ lookup xs j)
  ++-is-foldr : xs ++ ys ≡ foldr ((Vec A) ∘ (_+ n)) _∷_ ys xs
  []≔-++-↑ʳ   : (xs ++ ys) [ m ↑ʳ i ]≔ y ≡ xs ++ (ys [ i ]≔ y)
  unfold-ʳ++  : xs ʳ++ ys ≡ reverse xs ++ ys

  foldl-universal : ∀ (h : ∀ {c} (C : ℕ → Set c) (g : FoldlOp A C) (e : C zero) → ∀ {n} → Vec A n → C n) →
                    (∀ ... → h C g e [] ≡ e) →
                    (∀ ... → h C g e ∘ (x ∷_) ≗ h (C ∘ suc) g (g e x)) →
                    h B f e ≗ foldl B f e
  foldl-fusion  : h d ≡ e → (∀ ... → h (f b x) ≡ g (h b) x) → h ∘ foldl B f d ≗ foldl C g e
  foldl-∷ʳ      : foldl B f e (ys ∷ʳ y) ≡ f (foldl B f e ys) y
  foldl-[]      : foldl B f e [] ≡ e
  foldl-reverse : foldl B {n} f e ∘ reverse ≗ foldr B (flip f) e

  foldr-[]      : foldr B f e [] ≡ e
  foldr-++      : foldr B f e (xs ++ ys) ≡ foldr (B ∘ (_+ n)) f (foldr B f e ys) xs
  foldr-∷ʳ      : foldr B f e (ys ∷ʳ y) ≡ foldr (B ∘ suc) f (f y e) ys
  foldr-ʳ++     : foldr B f e (xs ʳ++ ys) ≡ foldl (B ∘ (_+ n)) (flip f) (foldr B f e ys) xs
  foldr-reverse : foldr B f e ∘ reverse ≗ foldl B (flip f) e

  ∷ʳ-injective  : xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
  ∷ʳ-injectiveˡ : xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
  ∷ʳ-injectiveʳ : xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y

  reverse-∷          : reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
  reverse-involutive : Involutive _≡_ reverse
  reverse-reverse    : reverse xs ≡ ys → reverse ys ≡ xs
  reverse-injective  : reverse xs ≡ reverse ys → xs ≡ ys

  transpose-replicate : transpose (replicate xs) ≡ map replicate xs
  toList-replicate    : toList (replicate {n = n} a) ≡ List.replicate n a

  toList-++ : toList (xs ++ ys) ≡ toList xs List.++ toList ys

  toList-cast   : toList (cast eq xs) ≡ toList xs
  cast-is-id    : cast eq xs ≡ xs
  subst-is-cast : subst (Vec A) eq xs ≡ cast eq xs
  cast-trans    : cast eq₂ (cast eq₁ xs) ≡ cast (trans eq₁ eq₂) xs
  map-cast      : map f (cast eq xs) ≡ cast eq (map f xs)
  lookup-cast   : lookup (cast eq xs) (Fin.cast eq i) ≡ lookup xs i
  lookup-cast₁  : lookup (cast eq xs) i ≡ lookup xs (Fin.cast (sym eq) i)
  lookup-cast₂  : lookup xs (Fin.cast eq i) ≡ lookup (cast (sym eq) xs) i

  zipwith-++ : zipWith f (xs ++ ys) (xs' ++ ys') ≡ zipWith f xs xs' ++ zipWith f ys ys'
  ```

* Added new proofs in `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  index-∈-fromList⁺ : Any.index (∈-fromList⁺ v∈xs) ≡ indexₗ v∈xs
  ```

* Added new proofs in `Data.Vec.Functional.Properties`:
  ```
  map-updateAt : f ∘ g ≗ h ∘ f → map f (updateAt i g xs) ≗ updateAt i h (map f xs)
  ```

* Added new proofs in `Data.Vec.Relation.Binary.Lex.Strict`:
  ```agda
  xs≮[] : ∀ {n} (xs : Vec A n) → ¬ xs < []
  <-respectsˡ : IsPartialEquivalence _≈_ → _≺_ Respectsˡ _≈_ →
                ∀ {m n} → _Respectsˡ_ (_<_ {m} {n}) _≋_
  <-respectsʳ : IsPartialEquivalence _≈_ → _≺_ Respectsʳ _≈_ →
                ∀ {m n} → _Respectsʳ_ (_<_ {m} {n}) _≋_
  <-wellFounded : Symmetric _≈_ →  Transitive _≈_ → _≺_ Respectsʳ _≈_ → WellFounded _≺_ →
                  ∀ {n} → WellFounded (_<_ {n})
```

* Added new functions in `Data.Vec.Relation.Unary.Any`:
  ```
  lookup : Any P xs → A
  ```

* Added new functions in `Data.Vec.Relation.Unary.All`:
  ```
  decide :  Π[ P ∪ Q ] → Π[ All P ∪ Any Q ]
  ```

* Added vector associativity proof to  `Data.Vec.Relation.Binary.Equality.Setoid`:
  ```
  ++-assoc : (xs ++ ys) ++ zs ≋ xs ++ (ys ++ zs)
  ```

* Added new functions in `Effect.Monad.State`:
  ```
  runState  : State s a → s → a × s
  evalState : State s a → s → a
  execState : State s a → s → s
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

  when   : Bool → IO ⊤ → IO ⊤
  unless : Bool → IO ⊤ → IO ⊤

  whenJust  : Maybe A → (A → IO ⊤) → IO ⊤
  untilJust : IO (Maybe A) → IO A
  untilRight : (A → IO (A ⊎ B)) → A → IO B
  ```

* Added new functions in `Reflection.AST.Term`:
  ```
  stripPis     : Term → List (String × Arg Type) × Term
  prependLams  : List (String × Visibility) → Term → Term
  prependHLams : List String → Term → Term
  prependVLams : List String → Term → Term
  ```

* Added new operations in `Relation.Binary.Construct.Closure.Equivalence`:
  ```
  fold   : IsEquivalence _∼_ → _⟶_ ⇒ _∼_ → EqClosure _⟶_ ⇒ _∼_
  gfold  : IsEquivalence _∼_ → _⟶_ =[ f ]⇒ _∼_ → EqClosure _⟶_ =[ f ]⇒ _∼_
  return : _⟶_ ⇒ EqClosure _⟶_
  join   : EqClosure (EqClosure _⟶_) ⇒ EqClosure _⟶_
  _⋆     : _⟶₁_ ⇒ EqClosure _⟶₂_ → EqClosure _⟶₁_ ⇒ EqClosure _⟶₂_
  ```

* Added new operations in `Relation.Binary.Construct.Closure.Symmetric`:
  ```
  fold   : Symmetric _∼_ → _⟶_ ⇒ _∼_ → SymClosure _⟶_ ⇒ _∼_
  gfold  : Symmetric _∼_ → _⟶_ =[ f ]⇒ _∼_ → SymClosure _⟶_ =[ f ]⇒ _∼_
  return : _⟶_ ⇒ SymClosure _⟶_
  join   : SymClosure (SymClosure _⟶_) ⇒ SymClosure _⟶_
  _⋆     : _⟶₁_ ⇒ SymClosure _⟶₂_ → SymClosure _⟶₁_ ⇒ SymClosure _⟶₂_
  ```

* Added new proofs to `Relation.Binary.Lattice.Properties.{Join,Meet}Semilattice`:
  ```agda
  isPosemigroup : IsPosemigroup _≈_ _≤_ _∨_
  posemigroup : Posemigroup c ℓ₁ ℓ₂
  ≈-dec⇒≤-dec : Decidable _≈_ → Decidable _≤_
  ≈-dec⇒isDecPartialOrder : Decidable _≈_ → IsDecPartialOrder _≈_ _≤_
  ```

* Added new proofs to `Relation.Binary.Lattice.Properties.Bounded{Join,Meet}Semilattice`:
  ```agda
  isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∨_ ⊥
  commutativePomonoid : CommutativePomonoid c ℓ₁ ℓ₂
  ```

* Added new proofs to `Relation.Binary.Properties.Poset`:
  ```agda
  ≤-dec⇒≈-dec : Decidable _≤_ → Decidable _≈_
  ≤-dec⇒isDecPartialOrder : Decidable _≤_ → IsDecPartialOrder _≈_ _≤_
  ```

* Added new proofs in `Relation.Binary.Properties.StrictPartialOrder`:
  ```agda
  >-strictPartialOrder : StrictPartialOrder s₁ s₂ s₃
  ```

* Added new proofs in `Relation.Binary.PropositionalEquality.Properties`:
  ```
  subst-application′ : subst Q eq (f x p) ≡ f y (subst P eq p)
  sym-cong : sym (cong f p) ≡ cong f (sym p)
  ```

* Added new proofs in `Relation.Binary.HeterogeneousEquality`:
  ```
  subst₂-removable : subst₂ _∼_ eq₁ eq₂ p ≅ p
  ```

* Added new definitions in `Relation.Unary`:
  ```
  _≐_  : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  _≐′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  _∖_  : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  ```

* Added new proofs in `Relation.Unary.Properties`:
  ```
  ⊆-reflexive : _≐_ ⇒ _⊆_
  ⊆-antisym : Antisymmetric _≐_ _⊆_
  ⊆-min : Min _⊆_ ∅
  ⊆-max : Max _⊆_ U
  ⊂⇒⊆ : _⊂_ ⇒ _⊆_
  ⊂-trans : Trans _⊂_ _⊂_ _⊂_
  ⊂-⊆-trans : Trans _⊂_ _⊆_ _⊂_
  ⊆-⊂-trans : Trans _⊆_ _⊂_ _⊂_
  ⊂-respʳ-≐ : _⊂_ Respectsʳ _≐_
  ⊂-respˡ-≐ : _⊂_ Respectsˡ _≐_
  ⊂-resp-≐ : _⊂_ Respects₂ _≐_
  ⊂-irrefl : Irreflexive _≐_ _⊂_
  ⊂-antisym : Antisymmetric _≐_ _⊂_
  ∅-⊆′ : (P : Pred A ℓ) → ∅ ⊆′ P
  ⊆′-U : (P : Pred A ℓ) → P ⊆′ U
  ⊆′-refl : Reflexive {A = Pred A ℓ} _⊆′_
  ⊆′-reflexive : _≐′_ ⇒ _⊆′_
  ⊆′-trans : Trans _⊆′_ _⊆′_ _⊆′_
  ⊆′-antisym : Antisymmetric _≐′_ _⊆′_
  ⊆′-min : Min _⊆′_ ∅
  ⊆′-max : Max _⊆′_ U
  ⊂′⇒⊆′ : _⊂′_ ⇒ _⊆′_
  ⊂′-trans : Trans _⊂′_ _⊂′_ _⊂′_
  ⊂′-⊆′-trans : Trans _⊂′_ _⊆′_ _⊂′_
  ⊆′-⊂′-trans : Trans _⊆′_ _⊂′_ _⊂′_
  ⊂′-respʳ-≐′ : _⊂′_ Respectsʳ _≐′_
  ⊂′-respˡ-≐′ : _⊂′_ Respectsˡ _≐′_
  ⊂′-resp-≐′ : _⊂′_ Respects₂ _≐′_
  ⊂′-irrefl : Irreflexive _≐′_ _⊂′_
  ⊂′-antisym : Antisymmetric _≐′_ _⊂′_
  ⊆⇒⊆′ : _⊆_ ⇒ _⊆′_
  ⊆′⇒⊆ : _⊆′_ ⇒ _⊆_
  ⊂⇒⊂′ : _⊂_ ⇒ _⊂′_
  ⊂′⇒⊂ : _⊂′_ ⇒ _⊂_
  ≐-refl : Reflexive _≐_
  ≐-sym : Sym _≐_ _≐_
  ≐-trans : Trans _≐_ _≐_ _≐_
  ≐′-refl : Reflexive _≐′_
  ≐′-sym : Sym _≐′_ _≐′_
  ≐′-trans : Trans _≐′_ _≐′_ _≐′_
  ≐⇒≐′ : _≐_ ⇒ _≐′_
  ≐′⇒≐ : _≐′_ ⇒ _≐_

  U-irrelevant : Irrelevant {A = A} U
  ∁-irrelevant : (P : Pred A ℓ) → Irrelevant (∁ P)
  ```

* Generalised proofs in `Relation.Unary.Properties`:
  ```
  ⊆-trans : Trans _⊆_ _⊆_ _⊆_
  ```

* Added new proofs in `Relation.Binary.Properties.Setoid`:
  ```
  ≈-isPreorder     : IsPreorder _≈_ _≈_
  ≈-isPartialOrder : IsPartialOrder _≈_ _≈_

  ≈-preorder : Preorder a ℓ ℓ
  ≈-poset    : Poset a ℓ ℓ
  ```

* Added new definitions in `Relation.Binary.Definitions`:
  ```
  Cotransitive _#_ = ∀ {x y} → x # y → ∀ z → (x # z) ⊎ (z # y)
  Tight    _≈_ _#_ = ∀ x y → (¬ x # y → x ≈ y) × (x ≈ y → ¬ x # y)

  Monotonic₁         _≤_ _⊑_ f     = f Preserves _≤_ ⟶ _⊑_
  Antitonic₁         _≤_ _⊑_ f     = f Preserves (flip _≤_) ⟶ _⊑_
  Monotonic₂         _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ _≤_ ⟶ _⊑_ ⟶ _≼_
  MonotonicAntitonic _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ _≤_ ⟶ (flip _⊑_) ⟶ _≼_
  AntitonicMonotonic _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ (flip _≤_) ⟶ _⊑_ ⟶ _≼_
  Antitonic₂         _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ (flip _≤_) ⟶ (flip _⊑_) ⟶ _≼_
  Adjoint            _≤_ _⊑_ f g   = ∀ {x y} → (f x ⊑ y → x ≤ g y) × (x ≤ g y → f x ⊑ y)
  ```

* Added new definitions in `Relation.Binary.Bundles`:
  ```
  record ApartnessRelation c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  ```

* Added new definitions in `Relation.Binary.Structures`:
  ```
  record IsApartnessRelation (_#_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```
  sym⇒¬-sym       : Symmetric _∼_ → Symmetric _≁_
  cotrans⇒¬-trans : Cotransitive _∼_ → Transitive _≁_
  irrefl⇒¬-refl   : Reflexive _≈_ → Irreflexive _≈_ _∼_ →  Reflexive _≁_
  mono₂⇒cong₂     : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ → ∀ {f} →
                    f Preserves₂ ≤₁ ⟶ ≤₁ ⟶ ≤₂ →
                    f Preserves₂ ≈₁ ⟶ ≈₁ ⟶ ≈₂
  ```

* Added new operations in `Relation.Binary.PropositionalEquality.Properties`:
  ```
  J       : (B : (y : A) → x ≡ y → Set b) (p : x ≡ y) → B x refl → B y p
  dcong   : (p : x ≡ y) → subst B p (f x) ≡ f y
  dcong₂  : (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
  dsubst₂ : (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
  ddcong₂ : (p : x₁ ≡ x₂) (q : subst B p y₁ ≡ y₂) → dsubst₂ C p q (f x₁ y₁) ≡ f x₂ y₂

  isPartialOrder : IsPartialOrder _≡_ _≡_
  poset          : Set a → Poset _ _ _
  ```

* Added new operations in `System.Exit`:
  ```
  isSuccess : ExitCode → Bool
  isFailure : ExitCode → Bool
  ```

* Added new functions in `Codata.Guarded.Stream`:
  ```
  transpose : List (Stream A) → Stream (List A)
  transpose⁺ : List⁺ (Stream A) → Stream (List⁺ A)
  concat : Stream (List⁺ A) → Stream A
  ```

* Added new proofs in `Codata.Guarded.Stream.Properties`:
  ```
  cong-concat : {ass bss : Stream (List⁺.List⁺ A)} → ass ≈ bss → concat ass ≈ concat bss
  map-concat : ∀ (f : A → B) ass → map f (concat ass) ≈ concat (map (List⁺.map f) ass)
  lookup-transpose : ∀ n (ass : List (Stream A)) → lookup n (transpose ass) ≡ List.map (lookup n) ass
  lookup-transpose⁺ : ∀ n (ass : List⁺ (Stream A)) → lookup n (transpose⁺ ass) ≡ List⁺.map (lookup n) ass
  ```

* Added new corollaries in `Data.List.Membership.Setoid.Properties`:
  ```
  ∈-++⁺∘++⁻ : ∀ {v} xs {ys} (p : v ∈ xs ++ ys) → [ ∈-++⁺ˡ , ∈-++⁺ʳ xs ]′ (∈-++⁻ xs p) ≡ p
  ∈-++⁻∘++⁺ : ∀ {v} xs {ys} (p : v ∈ xs ⊎ v ∈ ys) → ∈-++⁻ xs ([ ∈-++⁺ˡ , ∈-++⁺ʳ xs ]′ p) ≡ p
  ∈-++↔ : ∀ {v xs ys} → (v ∈ xs ⊎ v ∈ ys) ↔ v ∈ xs ++ ys
  ∈-++-comm : ∀ {v} xs ys → v ∈ xs ++ ys → v ∈ ys ++ xs
  ∈-++-comm∘++-comm : ∀ {v} xs {ys} (p : v ∈ xs ++ ys) → ∈-++-comm ys xs (∈-++-comm xs ys p) ≡ p
  ∈-++↔++ : ∀ {v} xs ys → v ∈ xs ++ ys ↔ v ∈ ys ++ xs
  ```

* Exposed container combinator conversion functions from `Data.Container.Combinator.Properties` separate from their correctness proofs in `Data.Container.Combinator`:
  ```
  to-id      : F.id A → ⟦ id ⟧ A
  from-id    : ⟦ id ⟧ A → F.id A
  to-const   : (A : Set s) → A → ⟦ const A ⟧ B
  from-const : (A : Set s) → ⟦ const A ⟧ B → A
  to-∘       : (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) → ⟦ C₁ ⟧ (⟦ C₂ ⟧ A) → ⟦ C₁ ∘ C₂ ⟧ A
  from-∘     : (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) → ⟦ C₁ ∘ C₂ ⟧ A → ⟦ C₁ ⟧ (⟦ C₂ ⟧ A)
  to-×       : (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) → ⟦ C₁ ⟧ A P.× ⟦ C₂ ⟧ A → ⟦ C₁ × C₂ ⟧ A
  from-×     : (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) → ⟦ C₁ × C₂ ⟧ A → ⟦ C₁ ⟧ A P.× ⟦ C₂ ⟧ A
  to-Π       : (I : Set i) (Cᵢ : I → Container s p) → (∀ i → ⟦ Cᵢ i ⟧ A) → ⟦ Π I Cᵢ ⟧ A
  from-Π     : (I : Set i) (Cᵢ : I → Container s p) → ⟦ Π I Cᵢ ⟧ A → ∀ i → ⟦ Cᵢ i ⟧ A
  to-⊎       : (C₁ : Container s₁ p) (C₂ : Container s₂ p) → ⟦ C₁ ⟧ A S.⊎ ⟦ C₂ ⟧ A → ⟦ C₁ ⊎ C₂ ⟧ A
  from-⊎     : (C₁ : Container s₁ p) (C₂ : Container s₂ p) → ⟦ C₁ ⊎ C₂ ⟧ A → ⟦ C₁ ⟧ A S.⊎ ⟦ C₂ ⟧ A
  to-Σ       : (I : Set i) (C : I → Container s p) → (∃ λ i → ⟦ C i ⟧ A) → ⟦ Σ I C ⟧ A
  from-Σ     : (I : Set i) (C : I → Container s p) → ⟦ Σ I C ⟧ A → ∃ λ i → ⟦ C i ⟧ A
  ```

* Added a non-dependent version of `Function.Base.flip` due to an issue noted in
  Pull Request #1812:
  ```agda
  flip′ : (A → B → C) → (B → A → C)
  ```

* Added new proofs to `Data.List.Properties`
  ```agda
  cartesianProductWith-zeroˡ       : cartesianProductWith f [] ys ≡ []
  cartesianProductWith-zeroʳ       : cartesianProductWith f xs [] ≡ []
  cartesianProductWith-distribʳ-++ : cartesianProductWith f (xs ++ ys) zs ≡
                                     cartesianProductWith f xs zs ++ cartesianProductWith f ys zs
  foldr-map : foldr f x (map g xs) ≡ foldr (g -⟨ f ∣) x xs
  foldl-map : foldl f x (map g xs) ≡ foldl (∣ f ⟩- g) x xs
  ```

NonZero/Positive/Negative changes
---------------------------------

This is a full list of proofs that have changed form to use irrelevant instance arguments:

* In `Data.Nat.Base`:
  ```
  ≢-nonZero⁻¹ : ∀ {n} → .(NonZero n) → n ≢ 0
  >-nonZero⁻¹ : ∀ {n} → .(NonZero n) → n > 0
  ```

* In `Data.Nat.Properties`:
  ```
  *-cancelʳ-≡ : ∀ m n {o} → m * suc o ≡ n * suc o → m ≡ n
  *-cancelˡ-≡ : ∀ {m n} o → suc o * m ≡ suc o * n → m ≡ n
  *-cancelʳ-≤ : ∀ m n o → m * suc o ≤ n * suc o → m ≤ n
  *-cancelˡ-≤ : ∀ {m n} o → suc o * m ≤ suc o * n → m ≤ n
  *-monoˡ-<   : ∀ n → (_* suc n) Preserves _<_ ⟶ _<_
  *-monoʳ-<   : ∀ n → (suc n *_) Preserves _<_ ⟶ _<_

  m≤m*n          : ∀ m {n} → 0 < n → m ≤ m * n
  m≤n*m          : ∀ m {n} → 0 < n → m ≤ n * m
  m<m*n          : ∀ {m n} → 0 < m → 1 < n → m < m * n
  suc[pred[n]]≡n : ∀ {n} → n ≢ 0 → suc (pred n) ≡ n
  ```

* In `Data.Nat.Coprimality`:
  ```
  Bézout-coprime : ∀ {i j d} → Bézout.Identity (suc d) (i * suc d) (j * suc d) → Coprime i j
  ```

* In `Data.Nat.Divisibility`
  ```agda
  m%n≡0⇒n∣m : ∀ m n → m % suc n ≡ 0 → suc n ∣ m
  n∣m⇒m%n≡0 : ∀ m n → suc n ∣ m → m % suc n ≡ 0
  m%n≡0⇔n∣m : ∀ m n → m % suc n ≡ 0 ⇔ suc n ∣ m
  ∣⇒≤       : ∀ {m n} → m ∣ suc n → m ≤ suc n
  >⇒∤        : ∀ {m n} → m > suc n → m ∤ suc n
  *-cancelˡ-∣ : ∀ {i j} k → suc k * i ∣ suc k * j → i ∣ j
  ```

* In `Data.Nat.DivMod`:
  ```
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

  m/n<m         : ∀ m n {≢0} → m ≥ 1 → n ≥ 2 → (m / n) {≢0} < m
  ```

* In `Data.Nat.GCD`
  ```
  GCD-* : ∀ {m n d c} → GCD (m * suc c) (n * suc c) (d * suc c) → GCD m n d
  gcd[m,n]≤n : ∀ m n → gcd m (suc n) ≤ suc n
  ```

* In `Data.Integer.Properties`:
  ```
  positive⁻¹        : ∀ {i} → Positive i → i > 0ℤ
  negative⁻¹        : ∀ {i} → Negative i → i < 0ℤ
  nonPositive⁻¹     : ∀ {i} → NonPositive i → i ≤ 0ℤ
  nonNegative⁻¹     : ∀ {i} → NonNegative i → i ≥ 0ℤ
  negative<positive : ∀ {i j} → Negative i → Positive j → i < j

  sign-◃    : ∀ s n → sign (s ◃ suc n) ≡ s
  sign-cong : ∀ {s₁ s₂ n₁ n₂} → s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
  -◃<+◃     : ∀ m n → Sign.- ◃ (suc m) < Sign.+ ◃ n
  m⊖1+n<m   : ∀ m n → m ⊖ suc n < + m

  *-cancelʳ-≡     : ∀ i j k → k ≢ + 0 → i * k ≡ j * k → i ≡ j
  *-cancelˡ-≡     : ∀ i j k → i ≢ + 0 → i * j ≡ i * k → j ≡ k
  *-cancelʳ-≤-pos : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n

  ≤-steps     : ∀ n → i ≤ j → i ≤ + n + j
  ≤-steps-neg : ∀ n → i ≤ j → i - + n ≤ j
  n≤m+n       : ∀ n → i ≤ + n + i
  m≤m+n       : ∀ n → i ≤ i + + n
  m-n≤m       : ∀ i n → i - + n ≤ i

  *-cancelʳ-≤-pos    : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
  *-cancelˡ-≤-pos    : ∀ m j k → + suc m * j ≤ + suc m * k → j ≤ k
  *-cancelˡ-≤-neg    : ∀ m {j k} → -[1+ m ] * j ≤ -[1+ m ] * k → j ≥ k
  *-cancelʳ-≤-neg    : ∀ {n o} m → n * -[1+ m ] ≤ o * -[1+ m ] → n ≥ o
  *-cancelˡ-<-nonNeg : ∀ n → + n * i < + n * j → i < j
  *-cancelʳ-<-nonNeg : ∀ n → i * + n < j * + n → i < j
  *-monoʳ-≤-nonNeg   : ∀ n → (_* + n) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonNeg   : ∀ n → (+ n *_) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonPos   : ∀ i → NonPositive i → (i *_) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonPos   : ∀ i → NonPositive i → (_* i) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos      : ∀ n → (+[1+ n ] *_) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos      : ∀ n → (_* +[1+ n ]) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg      : ∀ n → (-[1+ n ] *_) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg      : ∀ n → (_* -[1+ n ]) Preserves _<_ ⟶ _>_
  *-cancelˡ-<-nonPos : ∀ n → NonPositive n → n * i < n * j → i > j
  *-cancelʳ-<-nonPos : ∀ n → NonPositive n → i * n < j * n → i > j

  *-distribˡ-⊓-nonNeg : ∀ m j k → + m * (j ⊓ k) ≡ (+ m * j) ⊓ (+ m * k)
  *-distribʳ-⊓-nonNeg : ∀ m j k → (j ⊓ k) * + m ≡ (j * + m) ⊓ (k * + m)
  *-distribˡ-⊓-nonPos : ∀ i → NonPositive i → ∀ j k → i * (j ⊓ k) ≡ (i * j) ⊔ (i * k)
  *-distribʳ-⊓-nonPos : ∀ i → NonPositive i → ∀ j k → (j ⊓ k) * i ≡ (j * i) ⊔ (k * i)
  *-distribˡ-⊔-nonNeg : ∀ m j k → + m * (j ⊔ k) ≡ (+ m * j) ⊔ (+ m * k)
  *-distribʳ-⊔-nonNeg : ∀ m j k → (j ⊔ k) * + m ≡ (j * + m) ⊔ (k * + m)
  *-distribˡ-⊔-nonPos : ∀ i → NonPositive i → ∀ j k → i * (j ⊔ k) ≡ (i * j) ⊓ (i * k)
  *-distribʳ-⊔-nonPos : ∀ i → NonPositive i → ∀ j k → (j ⊔ k) * i ≡ (j * i) ⊓ (k * i)
  ```

* In `Data.Integer.Divisibility`:
  ```
  *-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
  *-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
  ```

* In `Data.Integer.Divisibility.Signed`:
  ```
  *-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
  *-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
  ```

* In `Data.Rational.Unnormalised.Properties`:
  ```agda
  positive⁻¹           : ∀ {q} → .(Positive q) → q > 0ℚᵘ
  nonNegative⁻¹        : ∀ {q} → .(NonNegative q) → q ≥ 0ℚᵘ
  negative⁻¹           : ∀ {q} → .(Negative q) → q < 0ℚᵘ
  nonPositive⁻¹        : ∀ {q} → .(NonPositive q) → q ≤ 0ℚᵘ
  positive⇒nonNegative : ∀ {p} → Positive p → NonNegative p
  negative⇒nonPositive : ∀ {p} → Negative p → NonPositive p
  negative<positive    : ∀ {p q} → .(Negative p) → .(Positive q) → p < q
  nonNeg∧nonPos⇒0      : ∀ {p} → .(NonNegative p) → .(NonPositive p) → p ≃ 0ℚᵘ

  ≤-steps : ∀ {p q r} → NonNegative r → p ≤ q → p ≤ r + q
  p≤p+q   : ∀ {p q} → NonNegative q → p ≤ p + q
  p≤q+p   : ∀ {p} → NonNegative p → ∀ {q} → q ≤ p + q

  *-cancelʳ-≤-pos    : ∀ {r} → Positive r → ∀ {p q} → p * r ≤ q * r → p ≤ q
  *-cancelˡ-≤-pos    : ∀ {r} → Positive r → ∀ {p q} → r * p ≤ r * q → p ≤ q
  *-cancelʳ-≤-neg    : ∀ r → Negative r → ∀ {p q} → p * r ≤ q * r → q ≤ p
  *-cancelˡ-≤-neg    : ∀ r → Negative r → ∀ {p q} → r * p ≤ r * q → q ≤ p
  *-cancelˡ-<-nonNeg : ∀ {r} → NonNegative r → ∀ {p q} → r * p < r * q → p < q
  *-cancelʳ-<-nonNeg : ∀ {r} → NonNegative r → ∀ {p q} → p * r < q * r → p < q
  *-cancelˡ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → r * p < r * q → q < p
  *-cancelʳ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → p * r < q * r → q < p
  *-monoˡ-≤-nonNeg   : ∀ {r} → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-nonNeg   : ∀ {r} → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonPos   : ∀ r → NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonPos   : ∀ r → NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos      : ∀ {r} → Positive r → (_* r) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos      : ∀ {r} → Positive r → (r *_) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg      : ∀ r → Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg      : ∀ r → Negative r → (r *_) Preserves _<_ ⟶ _>_

  pos⇒1/pos : ∀ p (p>0 : Positive p) → Positive ((1/ p) {{pos⇒≢0 p p>0}})
  neg⇒1/neg : ∀ p (p<0 : Negative p) → Negative ((1/ p) {{neg⇒≢0 p p<0}})

  *-distribʳ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊓ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊓ r) ≃ (p * q) ⊓ (p * r)
  *-distribˡ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊔ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊔ r) * p ≃ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊔ r) ≃ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊔ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊓ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊓ r) * p ≃ (q * p) ⊔ (r * p)
  ```

* In `Data.Rational.Properties`:
  ```
  positive⁻¹ : Positive p → p > 0ℚ
  nonNegative⁻¹ : NonNegative p → p ≥ 0ℚ
  negative⁻¹ : Negative p → p < 0ℚ
  nonPositive⁻¹ : NonPositive p → p ≤ 0ℚ
  negative<positive : Negative p → Positive q → p < q
  nonNeg≢neg : ∀ p q → NonNegative p → Negative q → p ≢ q
  pos⇒nonNeg : ∀ p → Positive p → NonNegative p
  neg⇒nonPos : ∀ p → Negative p → NonPositive p
  nonNeg∧nonZero⇒pos : ∀ p → NonNegative p → NonZero p → Positive p

  *-cancelʳ-≤-pos    : ∀ r → Positive r → ∀ {p q} → p * r ≤ q * r → p ≤ q
  *-cancelˡ-≤-pos    : ∀ r → Positive r → ∀ {p q} → r * p ≤ r * q → p ≤ q
  *-cancelʳ-≤-neg    : ∀ r → Negative r → ∀ {p q} → p * r ≤ q * r → p ≥ q
  *-cancelˡ-≤-neg    : ∀ r → Negative r → ∀ {p q} → r * p ≤ r * q → p ≥ q
  *-cancelˡ-<-nonNeg : ∀ r → NonNegative r → ∀ {p q} → r * p < r * q → p < q
  *-cancelʳ-<-nonNeg : ∀ r → NonNegative r → ∀ {p q} → p * r < q * r → p < q
  *-cancelˡ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → r * p < r * q → p > q
  *-cancelʳ-<-nonPos : ∀ r → NonPositive r → ∀ {p q} → p * r < q * r → p > q
  *-monoʳ-≤-nonNeg   : ∀ r → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonNeg   : ∀ r → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-nonPos   : ∀ r → NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoˡ-≤-nonPos   : ∀ r → NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos      : ∀ r → Positive r → (_* r) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos      : ∀ r → Positive r → (r *_) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg      : ∀ r → Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg      : ∀ r → Negative r → (r *_) Preserves _<_ ⟶ _>_

  *-distribˡ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊓ (p * r)
  *-distribʳ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊓ (r * p)
  *-distribˡ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos : ∀ p → NonPositive p → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊔ (r * p)

  pos⇒1/pos : ∀ p (p>0 : Positive p) → Positive ((1/ p) {{pos⇒≢0 p p>0}})
  neg⇒1/neg : ∀ p (p<0 : Negative p) → Negative ((1/ p) {{neg⇒≢0 p p<0}})
  1/pos⇒pos : ∀ p .{{_ : NonZero p}} → (1/p : Positive (1/ p)) → Positive p
  1/neg⇒neg : ∀ p .{{_ : NonZero p}} → (1/p : Negative (1/ p)) → Negative p
  ```

* In `Data.List.NonEmpty.Base`:
  ```agda
  drop+ : ℕ → List⁺ A → List⁺ A
  ```
  When drop+ping more than the size of the length of the list, the last element remains.

* Added new proofs in `Data.List.NonEmpty.Properties`:
  ```agda
  length-++⁺ : length (xs ++⁺ ys) ≡ length xs + length ys
  length-++⁺-tail : length (xs ++⁺ ys) ≡ suc (length xs + length (tail ys))
  ++-++⁺ : (xs ++ ys) ++⁺ zs ≡ xs ++⁺ ys ++⁺ zs
  ++⁺-cancelˡ′ : xs ++⁺ zs ≡ ys ++⁺ zs′ → List.length xs ≡ List.length ys → zs ≡ zs′
  ++⁺-cancelˡ : xs ++⁺ ys ≡ xs ++⁺ zs → ys ≡ zs
  drop+-++⁺ : drop+ (length xs) (xs ++⁺ ys) ≡ ys
  map-++⁺-commute : map f (xs ++⁺ ys) ≡ map f xs ++⁺ map f ys
  length-map : length (map f xs) ≡ length xs
  map-cong : f ≗ g → map f ≗ map g
  map-compose : map (g ∘ f) ≗ map g ∘ map f
  ```

* Added new functions and proofs in `Data.Nat.GeneralisedArithmetic`:
  ```agda
  iterate : (A → A) → A → ℕ → A
  iterate-is-fold : ∀ (z : A) s m → fold z s m ≡ iterate s z m
  ```

* Added new proofs to `Function.Properties.Inverse`:
  ```agda
  Inverse⇒Injection : Inverse S T → Injection S T
  ↔⇒↣ : A ↔ B → A ↣ B
  ```

* Added a new isomorphism to `Data.Fin.Properties`:
  ```agda
  2↔Bool : Fin 2 ↔ Bool
  ```

* Added new isomorphisms to `Data.Unit.Polymorphic.Properties`:
  ```agda
  ⊤↔⊤* : ⊤ {ℓ} ↔ ⊤*
  ```

* Added new isomorphisms to `Data.Vec.N-ary`:
  ```agda
  Vec↔N-ary : ∀ n → (Vec A n → B) ↔ N-ary n A B
  ```

* Added new isomorphisms to `Data.Vec.Recursive`:
  ```agda
  lift↔ : ∀ n → A ↔ B → A ^ n ↔ B ^ n
  Fin[m^n]↔Fin[m]^n : ∀ m n → Fin (m ^ n) ↔ Fin m Vec.^ n
  ```

* Added new functions to `Function.Properties.Inverse`:
  ```agda
  ↔-refl  : Reflexive _↔_
  ↔-sym   : Symmetric _↔_
  ↔-trans : Transitive _↔_
  ```

* Added new isomorphisms to `Function.Properties.Inverse`:
  ```agda
  ↔-fun : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
  ```

* Added new function to `Data.Fin.Properties`
  ```agda
  i≤inject₁[j]⇒i≤1+j : i ≤ inject₁ j → i ≤ suc j
  ```

* Added new function to `Data.Fin.Induction`
  ```agda
  <-weakInduction-startingFrom : P i →  (∀ j → P (inject₁ j) → P (suc j)) → ∀ {j} → j ≥ i → P j
  ```

* Added new module to `Data.Rational.Unnormalised.Properties`
  ```agda
  module ≃-Reasoning = SetoidReasoning ≃-setoid
  ```

* Added new functions to `Data.Rational.Unnormalised.Properties`
  ```agda
  0≠1 : 0ℚᵘ ≠ 1ℚᵘ
  ≃-≠-irreflexive : Irreflexive _≃_ _≠_
  ≠-symmetric : Symmetric _≠_
  ≠-cotransitive : Cotransitive _≠_
  ≠⇒invertible : p ≠ q → Invertible _≃_ 1ℚᵘ _*_ (p - q)
  ```

* Added new structures to `Data.Rational.Unnormalised.Properties`
  ```agda
  +-*-isHeytingCommutativeRing : IsHeytingCommutativeRing _≃_ _≠_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
  +-*-isHeytingField : IsHeytingField _≃_ _≠_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
  ```

* Added new bundles to `Data.Rational.Unnormalised.Properties`
  ```agda
  +-*-heytingCommutativeRing : HeytingCommutativeRing 0ℓ 0ℓ 0ℓ
  +-*-heytingField : HeytingField 0ℓ 0ℓ 0ℓ
  ```

* Added new function to `Data.Vec.Relation.Binary.Pointwise.Inductive`
  ```agda
  cong-[_]≔ : Pointwise _∼_ xs ys → Pointwise _∼_ (xs [ i ]≔ p) (ys [ i ]≔ p)
  ```

* Added new function to `Data.Vec.Relation.Binary.Equality.Setoid`
  ```agda
  map-[]≔ : map f (xs [ i ]≔ p) ≋ map f xs [ i ]≔ f p
  ```

* Added new function to `Data.List.Relation.Binary.Permutation.Propositional.Properties`
  ```agda
  ↭-reverse : (xs : List A) → reverse xs ↭ xs
  ```

* Added new functions to `Algebra.Properties.CommutativeMonoid`
  ```agda
  invertibleˡ⇒invertibleʳ : LeftInvertible _≈_ 0# _+_ x → RightInvertible _≈_ 0# _+_ x
  invertibleʳ⇒invertibleˡ : RightInvertible _≈_ 0# _+_ x → LeftInvertible _≈_ 0# _+_ x
  invertibleˡ⇒invertible  : LeftInvertible _≈_ 0# _+_ x → Invertible _≈_ 0# _+_ x
  invertibleʳ⇒invertible  : RightInvertible _≈_ 0# _+_ x → Invertible _≈_ 0# _+_ x
  ```

* Added new functions to `Algebra.Apartness.Bundles`
  ```agda
  invertibleˡ⇒# : LeftInvertible _≈_ 1# _*_ (x - y) → x # y
  invertibleʳ⇒# : RightInvertible _≈_ 1# _*_ (x - y) → x # y
  x#0y#0→xy#0   : x # 0# → y # 0# → x * y # 0#
  #-sym         : Symmetric _#_
  #-congʳ       : x ≈ y → x # z → y # z
  #-congˡ       : y ≈ z → x # y → x # z
  ```

* Added new proofs to `Data.List.Relation.Binary.Sublist.Setoid.Properties`
  and `Data.List.Relation.Unary.Sorted.TotalOrder.Properties`.
  ```agda
  ⊆-mergeˡ : ∀ xs ys → xs ⊆ merge _≤?_ xs ys
  ⊆-mergeʳ : ∀ xs ys → ys ⊆ merge _≤?_ xs ys
  ```

* Added new file `Relation.Binary.Reasoning.Base.Apartness`

  This is how to use it:
    ```agda
    _ : a # d
    _ = begin-apartness
      a ≈⟨ a≈b ⟩
      b #⟨ b#c ⟩
      c ≈⟨ c≈d ⟩
      d ∎
    ```
* In `Function.Bundles`, added `_⟶ₛ_` as a synonym for `Func` that can
  be used infix.

* Added module `Data.Vec.Functional.Relation.Binary.Permutation`:
  ```agda
  _↭_ : IRel (Vector A) _
  ```

* Added new file `Data.Vec.Functional.Relation.Binary.Permutation.Properties`:
  ```agda
  ↭-refl      : Reflexive (Vector A) _↭_
  ↭-reflexive : xs ≡ ys → xs ↭ ys
  ↭-sym       : Symmetric (Vector A) _↭_
  ↭-trans     : Transitive (Vector A) _↭_
  ```