Version TODO
============

The library has been tested using Agda version 2.6.0.

Changes since 1.0.1:

Highlights
----------

Bug-fixes
---------

#### `_<_` in `Data.Integer`

* The definition of `_<_` in `Data.Integer` often resulted in unsolved metas
  when Agda has to infer the first argument. This was because it was
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

* For backwards compatability the old relations still exist as primed versions
  `_<′_` as do all the old proofs, e.g. `+-monoˡ-<` has become `+-monoˡ-<′`,
  but these have all been deprecated and may be removed in some future version.

Non-backwards compatible changes
--------------------------------

* Split the `Maybe`-independent content of `Data.These` into `Data.These.Base`
  to avoid cyclic dependencies with `Data.Maybe.Base` which now has an `align`
  function. `Data.These` re-exports `Data.These.Base` so it should be mostly
  transparent for users.

New modules
-----------

* The following new modules have been added to the library:
  ```
  Algebra.Constructs.LiftedChoice

  Category.Monad.Reader

  Data.AVL.NonEmpty
  Data.AVL.NonEmpty.Propositional

  Data.List.Relation.Binary.Disjoint.Propositional
  Data.List.Relation.Binary.Disjoint.Setoid
  Data.List.Relation.Binary.Disjoint.Setoid.Properties

  Data.List.Relation.Binary.Permutation.Setoid
  Data.List.Relation.Binary.Permutation.Homogeneous

  Data.List.Relation.Unary.AllPairs
  Data.List.Relation.Unary.AllPairs.Properties
  Data.List.Relation.Unary.Unique.Propositional
  Data.List.Relation.Unary.Unique.Propositional.Properties
  Data.List.Relation.Unary.Unique.Setoid
  Data.List.Relation.Unary.Unique.Setoid.Properties

  Data.Nat.Induction
  Data.Fin.Induction

  Data.Sign.Base

  Data.These.Base

  Data.Unit.Properties

  Data.Trie
  Data.Trie.NonEmpty

  Relation.Binary.Construct.Closure.Equivalence.Properties
  Relation.Binary.Rewriting
  ```

Deprecated features
-------------------

* Renamed `Relation.Binary.Core`'s `Conn` to `Connex`.

* Renamed a few `-identity` lemmas in `Codata.Stream.Properties` as they were
  proving two streams bisimilar rather than propositionally equal.
  ```agda
  repeat-ap-identity ↦ ap-repeatˡ
  ap-repeat-identity ↦ ap-repeatʳ
  ```

* Renamed a few lemmas in `Codata.Stream.Properties` to match the more stdlib
  conventions:
  ```agda
  ap-repeat-commute  ↦ ap-repeat
  map-repeat-commute ↦ map-repeat
  ```

* The proof `decSetoid` in `Data.Bool` has been deprecated in favour
  of `≡-decSetoid` in `Data.Bool.Properties`.

* In `Data.Nat.Divisibility`:
  ```agda
  poset  ↦ ∣-poset
  *-cong ↦ *-monoʳ-∣
  /-cong ↦ *-cancelˡ-∣
  ```

* The following names have been deprecated in order to improve the consistency
  of proof names in `Data.Nat.Properties`:
  ```agda
  m≢0⇒suc[pred[m]]≡m ↦ suc[pred[n]]≡n

  i+1+j≢i            ↦ m+1+n≢m
  i+j≡0⇒i≡0          ↦ m+n≡0⇒m≡0
  i+j≡0⇒j≡0          ↦ m+n≡0⇒n≡0
  i+1+j≰i            ↦ m+1+n≰m
  i*j≡0⇒i≡0∨j≡0      ↦ m*n≡0⇒m≡0∨n≡0
  i*j≡1⇒i≡1          ↦ m*n≡1⇒m≡1
  i*j≡1⇒j≡1          ↦ m*n≡1⇒n≡1
  i^j≡0⇒i≡0          ↦ m^n≡0⇒m≡0
  i^j≡1⇒j≡0∨i≡1      ↦ m^n≡1⇒n≡0∨m≡1
  [i+j]∸[i+k]≡j∸k    ↦ [m+n]∸[m+o]≡n∸o

  n≡m⇒∣n-m∣≡0        ↦ m≡n⇒∣m-n∣≡0
  ∣n-m∣≡0⇒n≡m        ↦ ∣m-n∣≡0⇒m≡n
  ∣n-m∣≡n∸m⇒m≤n      ↦ ∣m-n∣≡m∸n⇒n≤m
  ∣n-n+m∣≡m          ↦ ∣m-m+n∣≡n
  ∣n+m-n+o∣≡∣m-o|    ↦ ∣m+n-m+o∣≡∣n-o|
  n∸m≤∣n-m∣          ↦ m∸n≤∣m-n∣
  ∣n-m∣≤n⊔m          ↦ ∣m-n∣≤m⊔n

  n≤m+n              ↦ m≤n+m
  n≤m+n∸m            ↦ m≤n+m∸n
  ∣n-m∣≡[n∸m]∨[m∸n]  ↦ ∣m-n∣≡[m∸n]∨[n∸m]
  ```
  Note that in the case of the last three proofs, the order of the
  arguments will need to be swapped.

* The following deprecations have occured in `Data.Unit` where the new
  names all live in the new `Data.Unit.Properties` file:
  ```agda
  setoid        ↦ ≡-setoid
  decSetoid     ↦ ≡-decSetoid
  total         ↦ ≤-total
  poset         ↦ ≤-poset
  decTotalOrder ↦ ≤-decTotalOrder
  ```
  The proof `preorder` has also been deprecated, but as it erroneously proved
  that `_≡_` (rather than `_≤_`) is a preorder with respect to `_≡_` it does
  not have a new name in `Data.Unit.Properties`.

* Deprecated `Unit` and `unit` in `Foreign.Haskell` in favour of
  `⊤` and `tt` from `Data.Unit`, as it turns out that the latter have been
  mapped to the Haskell equivalent for quite some time.

* The induction machinary for naturals was commonly held to be one of the hardest
  modules to find in the library. Therefore the module `Induction.Nat` has been
  split into two new modules: `Data.Nat.Induction` and `Data.Fin.Induction`.
  This should improve findability and better matches the design of the rest of
  the library. The new modules also export `Acc` and `acc` meaning there is no
  need to import `Data.Induction.WellFounded`.  The old module `Induction.Nat`
  still exists for backwards compatability but is deprecated.

* In `Reflection`:
  ```agda
  returnTC ↦ return
  ```

* Renamed functions in `Data.Char.Base` and the corresponding property
  in `Data.Char.Properties`:
  ```agda
  fromNat         ↦ fromℕ
  toNat           ↦ toℕ
  toNat-injective ↦ toℕ-injective
  ```

* In `Data.(Char/String).Properties`:
  ```agda
  setoid           ↦ ≡-setoid
  decSetoid        ↦ ≡-decSetoid
  strictTotalOrder ↦ <-strictTotalOrder-≈
  ```

Other minor additions
---------------------

* Added new record to `Algebra`:
  ```agda
  record SelectiveMagma c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new record to `Algebra.Structure`:
  ```agda
  record IsSelectiveMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
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

* Added new proof to `Data.Bool.Properties`:
  ```agda
  ≡-setoid : Setoid 0ℓ 0ℓ
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
  ≤-reflexive       : _≡_ ⇒ _≤_
  ≤-refl            : Reflexive _≤_
  ≤-antisym         : Antisymmetric _≡_ _≤_
  ≤-trans           : Transitive _≤_
  ≤-total           : Total _≤_
  _≤?_              : Decidable _≤_
  ≤-minimum         : Minimum _≤_ false
  ≤-maximum         : Maximum _≤_ true
  ≤-irrelevant      : B.Irrelevant _≤_
  ≤-isPreorder      : IsPreorder _≡_ _≤_
  ≤-isPartialOrder  : IsPartialOrder _≡_ _≤_
  ≤-isTotalOrder    : IsTotalOrder _≡_ _≤_
  ≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
  ≤-poset           : Poset 0ℓ 0ℓ 0ℓ
  ≤-preorder        : Preorder 0ℓ 0ℓ 0ℓ
  ≤-totalOrder      : TotalOrder 0ℓ 0ℓ 0ℓ
  ≤-decTotalOrder   : DecTotalOrder 0ℓ 0ℓ 0ℓ

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
  <-isStrictTotalOrder   : IsStrictTotalOrder _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder 0ℓ 0ℓ 0ℓ
  <-strictTotalOrder     : StrictTotalOrder 0ℓ 0ℓ 0ℓ
  ```

* Added new definitions to `Data.Char.Base`:
  ```agda
  _≈_ : Rel Char 0ℓ
  _<_ : Rel Char 0ℓ
  ```

* Added new properties to `Data.Char.Properties`:
  ```agda
  ≈⇒≡         : _≈_ ⇒ _≡_
  ≈-reflexive : _≡_ ⇒ _≈_
  ≈-refl      : Reflexive _≈_
  ≈-sym       : Symmetric _≈_
  ≈-trans     : Transitive _≈_
  ≈-subst     : ∀ {ℓ} → Substitutive _≈_ ℓ
  _≈?_        : Decidable _≈_

  ≈-isEquivalence    : IsEquivalence _≈_
  ≈-setoid           : Setoid _ _
  ≈-isDecEquivalence : IsDecEquivalence _≈_
  ≈-decSetoid        : DecSetoid _ _

  _<?_ : Decidable _<_
  ```

* Added new function to `Data.Digit`:
  ```agda
  toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
  ```

* Added new pattern synonyms to `Data.Integer`:
  ```agda
  pattern +0       = + 0
  pattern +[1+_] n = + (suc n)
  ```

* Added new proof to `Data.Integer.Properties`:
  ```agda
  ≡-setoid     : Setoid 0ℓ 0ℓ
  ≤-totalOrder : TotalOrder 0ℓ 0ℓ 0ℓ

  +[1+-injective : +[1+ m ] ≡ +[1+ n ] → m ≡ n
  drop‿+<+       : + m < + n → m ℕ.< n
  drop‿-<-       : -[1+ m ] < -[1+ n ] → n ℕ.< m

  m⊖n≤m          : m ⊖ n ≤ + m
  m⊖n<1+m        : m ⊖ n < +[1+ m ]
  m⊖1+n<m        : m ⊖ suc n < + m
  -[1+m]≤n⊖m+1   : -[1+ m ] ≤ n ⊖ suc m
  ⊖-monoʳ->-<    : (p ⊖_) Preserves ℕ._>_ ⟶ _<_
  ⊖-monoˡ-<      : (_⊖ p) Preserves ℕ._<_ ⟶ _<_

  *-distrib-+    : _*_ DistributesOver _+_
  ```

* Added new proof to `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`:
  ```agda
  concat⁺ : Sublist (Sublist R) ass bss → Sublist R (concat ass) (concat bss)
  ```

* Added new proofs to `Data.List.Relation.Binary.Sublist.Propositional.Properties`:
  ```agda
  All-resp-⊆ : (All P) Respects (flip _⊆_)
  Any-resp-⊆ : (Any P) Respects _⊆_
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-swap        : All (λ xs → All (xs ~_) ys) xss → All (λ y → All (_~ y) xss) ys

  applyDownFrom⁺₁ : (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₂ : (∀ i → P (f i)) → All P (applyDownFrom f n)
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  ap        : Maybe (A → B) → Maybe A → Maybe B
  _>>=_     : Maybe A → (A → Maybe B) → Maybe B
  ```

* Added new proofs to `Data.Nat.Divisibility`:
  ```agda
  ∣n∣m%n⇒∣m : d ∣ suc n → d ∣ (m % suc n) → d ∣ m
  %-presˡ-∣ : d ∣ m → d ∣ suc n → d ∣ (m % suc n)
  ```

* Added new operator and proofs to `Data.Nat.DivMod`:
  ```agda
  _/_ = _div_

  a%n≤a       : a % (suc n) ≤ a
  a≤n⇒a%n≡a   : a ≤ n → a % suc n ≡ a
  %-remove-+ˡ : a % suc n ≡ 0 → (a + b) % suc n ≡ b % suc n
  %-remove-+ʳ : b % suc n ≡ 0 → (a + b) % suc n ≡ a % suc n

  [a/n]*n≤a   : (a / suc n) * suc n ≤ a
  ```
  Additionally the `{≢0 : False (divisor ℕ.≟ 0)}` argument to all the
  functions has been made irrelevant. This means that the operations
  `_%_`, `_/_` etc. can now be used with `cong`.

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
  ```

* The functions `_≤?_` and `<-cmp` in `Data.Nat.Properties` have been
  reimplemented so that, when compiled, they run in logarithmic rather
  than linear time.

* The function `show` in `Data.Nat.Show` has been reimplemented and,
  when compiled, now runs in time `O(log₁₀(n))` rather than `O(n)`.

* Added new functions to `Data.Product`:
  ```agda
  zip′ : (A → B → C) → (D → E → F) → A × D → B × E → C × F
  ```

* Added new proofs to `Data.Rational.Properties`:
  ```agda
  ≡-setoid    : Setoid 0ℓ 0ℓ
  ≡-decSetoid : DecSetoid 0ℓ 0ℓ
  ```

* Added new proofs to `Data.Sign.Properties`:
  ```agda
  ≡-setoid    : Setoid 0ℓ 0ℓ
  ≡-decSetoid : DecSetoid 0ℓ 0ℓ
  ```

* Added new definitions to `Data.String.Base`:
  ```agda
  _≈_ : Rel String 0ℓ
  _<_ : Rel String 0ℓ
  ```

* Added new properties to `Data.String.Properties`:
  ```agda
  ≈⇒≡         : _≈_ ⇒ _≡_
  ≈-reflexive : _≡_ ⇒ _≈_
  ≈-refl      : Reflexive _≈_
  ≈-sym       : Symmetric _≈_
  ≈-trans     : Transitive _≈_
  ≈-subst     : ∀ {ℓ} → Substitutive _≈_ ℓ
  _≈?_        : Decidable _≈_

  ≈-isEquivalence    : IsEquivalence _≈_
  ≈-setoid           : Setoid _ _
  ≈-isDecEquivalence : IsDecEquivalence _≈_
  ≈-decSetoid        : DecSetoid _ _

  _<?_ : Decidable _<_
  ```

* Added new names, functions and shorthand to `Reflection`:
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

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  flip-Connex : Connex P Q → Connex Q P
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

* Added new definition in `Relation.Binary.Core`:
  ```agda
  Universal _∼_ = ∀ x y → x ∼ y
  ```

* The relation `_≅_` in `Relation.Binary.HeterogeneousEquality` has
  been generalised so that the types of the two equal elements need not
  be at the same universe level.

* Added new proofs to `Relation.Nullary.Construct.Add.Point`:
  ```agda
  ≡-dec        : Decidable {A = A} _≡_ → Decidable {A = Pointed A} _≡_
  []-injective : [ x ] ≡ [ y ] → x ≡ y
  ```

* Added new proof to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  ≢-sym : Symmetric _≢_
  ```

* Added new notation to `Relation.Unary`:
  ```agda
  syntax Satisfiable P = ∃⟨ P ⟩
  ```
