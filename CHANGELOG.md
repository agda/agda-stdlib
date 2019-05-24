Version TODO
============

The library has been tested using Agda version 2.6.0.

Changes since 1.0.1:

Highlights
----------

* The functions `_≤?_` and `<-cmp` in `Data.Nat.Properties` have been
  reimplemented so that, when compiled, they run in logarithmic rather
  than linear time.

* The function `show` in `Data.Nat.Show` has been reimplemented and,
  when compiled, now runs in time `O(log₁₀(n))` rather than `O(n)`.

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

* For backwards compatibility the old relations still exist as primed versions
  `_<′_` as do all the old proofs, e.g. `+-monoˡ-<` has become `+-monoˡ-<′`,
  but these have all been deprecated and may be removed in some future version.

* `Setω` is now exported in `Level`.

New modules
-----------

* The following new modules have been added to the library:
  ```
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
The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings have
been attached to all deprecated names.

#### Modules

* The induction machinery for naturals was commonly held to be one of the hardest
  modules to find in the library. Therefore the module `Induction.Nat` has been
  split into two new modules: `Data.Nat.Induction` and `Data.Fin.Induction`.
  This should improve findability and better matches the design of the rest of
  the library. The new modules also export `Acc` and `acc` meaning there is no
  need to import `Data.Induction.WellFounded`.  The old module `Induction.Nat`
  still exists for backwards compatibility but is deprecated.

* The module `Record` has been moved to `Data.Record`. The old module still
  exists but has been deprecated.

* The module `Universe` has been split into `Data.Universe` and
  `Data.Universe.Indexed`. In the latter `Indexed-universe` has been
  renamed to `IndexedUniverse` to better follow the library conventions. The
  old module still exists exporting the old names, but has been deprecated.

#### Names

* In `Relation.Binary.Core`:
  ```agdas
  Conn  ↦  Connex
  ```

* In `Codata.Stream.Properties`:
  ```agda
  repeat-ap-identity  ↦  ap-repeatˡ
  ap-repeat-identity  ↦  ap-repeatʳ
  ap-repeat-commute   ↦  ap-repeat
  map-repeat-commute  ↦  map-repeat
  ```

* In `Data.Bool` (new names in `Data.Bool.Properties`):
  ```agda
  decSetoid   ↦  ≡-decSetoid
  ```

* In `Data.Nat.Divisibility`:
  ```agda
  poset   ↦  ∣-poset
  *-cong  ↦  *-monoʳ-∣
  /-cong  ↦  *-cancelˡ-∣
  ```

* In `Data.Nat.Properties`:
  ```agda
  m≢0⇒suc[pred[m]]≡m  ↦  suc[pred[n]]≡n

  i+1+j≢i             ↦  m+1+n≢m
  i+j≡0⇒i≡0           ↦  m+n≡0⇒m≡0
  i+j≡0⇒j≡0           ↦  m+n≡0⇒n≡0
  i+1+j≰i             ↦  m+1+n≰m
  i*j≡0⇒i≡0∨j≡0       ↦  m*n≡0⇒m≡0∨n≡0
  i*j≡1⇒i≡1           ↦  m*n≡1⇒m≡1
  i*j≡1⇒j≡1           ↦  m*n≡1⇒n≡1
  i^j≡0⇒i≡0           ↦  m^n≡0⇒m≡0
  i^j≡1⇒j≡0∨i≡1       ↦  m^n≡1⇒n≡0∨m≡1
  [i+j]∸[i+k]≡j∸k     ↦  [m+n]∸[m+o]≡n∸o

  n≡m⇒∣n-m∣≡0         ↦  m≡n⇒∣m-n∣≡0
  ∣n-m∣≡0⇒n≡m         ↦  ∣m-n∣≡0⇒m≡n
  ∣n-m∣≡n∸m⇒m≤n       ↦  ∣m-n∣≡m∸n⇒n≤m
  ∣n-n+m∣≡m           ↦  ∣m-m+n∣≡n
  ∣n+m-n+o∣≡∣m-o|     ↦  ∣m+n-m+o∣≡∣n-o|
  n∸m≤∣n-m∣           ↦  m∸n≤∣m-n∣
  ∣n-m∣≤n⊔m           ↦  ∣m-n∣≤m⊔n

  n≤m+n               ↦  m≤n+m
  n≤m+n∸m             ↦  m≤n+m∸n
  ∣n-m∣≡[n∸m]∨[m∸n]   ↦  ∣m-n∣≡[m∸n]∨[n∸m]
  ```
  Note that in the case of the last three proofs, the order of the
  arguments will need to be swapped.

* In `Data.Unit` (new names in `Data.Unit.Properties`):
  ```agda
  setoid        ↦ ≡-setoid
  decSetoid     ↦ ≡-decSetoid
  total         ↦ ≤-total
  poset         ↦ ≤-poset
  decTotalOrder ↦ ≤-decTotalOrder
  ```

* In `Data.Unit` the proof `preorder` in has also been deprecated, but
  as it erroneously proved that `_≡_` rather than `_≤_` is a preorder
  with respect to `_≡_` it does not have a new name in `Data.Unit.Properties`.

* In `Foreign.Haskell` the terms `Unit` and `unit` have been deprecated in
  favour of `⊤` and `tt` from `Data.Unit`, as it turns out that the latter
  have been automatically mapped to the Haskell equivalent for quite some time.

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

* In `Data.Product.Relation.Binary.Pointwise.NonDependent`:
  ```agda
  ≡?×≡?⇒≡? ↦ Data.Product.Properties.≡-dec
  ```

Other minor additions
---------------------

* Added new proofs to `Codata.Stream.Properties`:
  ```agda
  splitAt-repeat-identity : splitAt n (repeat a) ≡ (Vec.replicate a , repeat a)
  replicate-repeat        : i ⊢ List.replicate n a ++ repeat a ≈ repeat a
  cycle-replicate         : i ⊢ cycle (List⁺.replicate n n≢0 a) ≈ repeat a
  map-cycle               : i ⊢ map f (cycle as) ≈ cycle (List⁺.map f as)
  map-⁺++                 : i ⊢ map f (as ⁺++ xs) ≈ List⁺.map f as ⁺++ Thunk.map (map f) xs
  map-++                  : i ⊢ map f (as ++ xs) ≈ List.map f as ++ map f xs
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
  ≡-setoid          : Setoid 0ℓ 0ℓ

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

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  ≡-setoid       : Setoid 0ℓ 0ℓ
  ≤-totalOrder   : TotalOrder 0ℓ 0ℓ 0ℓ

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

* Added new proofs to `Data.List.Properties`:
  ```agda
  foldr-forcesᵇ    : (P (f x y) → P x × P y) → P (foldr f e xs) → All P xs
  foldr-preservesᵇ : (P x → P y → P (f x y)) → P e → All P xs   → P (foldr f e xs)
  foldr-preservesʳ : (P y → P (f x y))       → P e              → P (foldr f e xs)
  foldr-preservesᵒ : (P x ⊎ P y → P (f x y)) → P e ⊎ Any P xs   → P (foldr f e xs)
  ```

* Defined a new utility in `Data.List.Relation.Binary.Permutation.Inductive.Properties`:
  ```agda
  shifts : xs ++ ys ++ zs ↭ ys ++ xs ++ zs
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

* Added new operations to `Data.List.Relation.Unary.All`:
  ```agda
  uncons    : All P (x ∷ xs) → P x × All P xs
  reduce    : (f : ∀ {x} → P x → B) → ∀ {xs} → All P xs → List B
  construct : (f : B → ∃ P) (xs : List B) → ∃ (All P)
  fromList  : (xs : List (∃ P)) → All P (List.map proj₁ xs)
  toList    : All P xs → List (∃ P)
  self      : All (const A) xs
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-swap        : All (λ xs → All (xs ~_) ys) xss → All (λ y → All (_~ y) xss) ys

  applyDownFrom⁺₁ : (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₂ : (∀ i → P (f i)) → All P (applyDownFrom f n)
  ```

* Added new proofs to `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  Any-Σ⁺ʳ : (∃ λ x → Any (_~ x) xs) → Any (∃ ∘ _~_) xs
  Any-Σ⁻ʳ : Any (∃ ∘ _~_) xs → ∃ λ x → Any (_~ x) xs
  gmap : P ⋐ Q ∘ f → Any P ⋐ Any Q ∘ map f
  ```

* Added new functions to `Data.Maybe.Base`:
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
  division and modulus functions has been marked irrelevant. This means
  that the operations `_%_`, `_/_` etc. can now be used with `cong`.

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

* Added new functions to `Data.Product`:
  ```agda
  zip′ : (A → B → C) → (D → E → F) → A × D → B × E → C × F
  ```

* Added new proofs to `Data.Product.Properties`:
  ```agda
  ,-injectiveʳ : (a , b) ≡ (c , d) → b ≡ d
  ,-injective : (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ≡-dec : Decidable {A} _≡_ → Decidable {B} _≡_ → Decidable {A × B} _≡_
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

* Added new types, functions and proofs to `Reflection`:
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

* Added new definitions in `Relation.Binary.Core`:
  ```agda
  Universal _∼_    = ∀ x y → x ∼ y
  Recomputable _~_ = ∀ {x y} → .(x ~ y) → x ~ y
  ```

* Added new proof to `Relation.Binary.Consequences`:
  ```agda
  dec⟶recomputable : Decidable R → Recomputable R
  flip-Connex      : Connex P Q → Connex Q P
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

* In `Relation.Binary.HeterogeneousEquality` the relation `_≅_` has
  been generalised so that the types of the two equal elements need not
  be at the same universe level.

* Added new proof to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  ≢-sym : Symmetric _≢_
  ```

* Added new proofs to `Relation.Nullary.Construct.Add.Point`:
  ```agda
  ≡-dec        : Decidable {A = A} _≡_ → Decidable {A = Pointed A} _≡_
  []-injective : [ x ] ≡ [ y ] → x ≡ y
  ```

* Added new type and syntax to `Relation.Unary`:
  ```agda
  Recomputable P = ∀ {x} → .(P x) → P x
  syntax Satisfiable P = ∃⟨ P ⟩
  ```

* Added new proof to `Relation.Unary.Consequences`:
  ```agda
  dec⟶recomputable : Decidable R → Recomputable R
  ```

* Added new alias definitions and modules for `Algebra.IdempotentCommutativeMonoid`
  and `Algebra.Structures.IsIdempotentCommutativeMonoid`:
  ```agda
  BoundedLattice = IdempotentCommutativeMonoid
  module BoundedLattice {c ℓ} (idempotentCommutativeMonoid : IdempotentCommutativeMonoid c ℓ)
  IsBoundedLattice = IsIdempotentCommutativeMonoid
  module IsBoundedLattice {∙ : Op₂ A}
                          {ε : A}
                          (isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid ∙ ε)

  ```
