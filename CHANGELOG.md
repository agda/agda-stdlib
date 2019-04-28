Version TODO
============

The library has been tested using Agda version 2.6.0.

Changes since 1.0.1:

Highlights
----------

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
  Category.Monad.Reader

  Data.AVL.NonEmpty
  Data.AVL.NonEmpty.Propositional

  Data.List.Relation.Binary.Disjoint.Propositional
  Data.List.Relation.Binary.Disjoint.Setoid
  Data.List.Relation.Binary.Disjoint.Setoid.Properties

  Data.List.Relation.Binary.Disjoint.Propositional
  Data.List.Relation.Binary.Disjoint.Setoid
  Data.List.Relation.Binary.Disjoint.Setoid.Properties

  Data.List.Relation.Unary.AllPairs
  Data.List.Relation.Unary.AllPairs.Properties
  Data.List.Relation.Unary.Unique.Propositional
  Data.List.Relation.Unary.Unique.Propositional.Properties
  Data.List.Relation.Unary.Unique.Setoid
  Data.List.Relation.Unary.Unique.Setoid.Properties

  Data.These.Base

  Data.Trie
  Data.Trie.NonEmpty
  ```

Deprecated features
-------------------

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

* Deprecated `Unit` and `unit` in `Foreign.Haskell` in favour of
  `⊤` and `tt` from `Data.Unit`, as it turns out that the latter have been
  mapped to the Haskell equivalent for quite some time.

* In `Reflection`:
  ```agda
  returnTC ↦ return
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

* Added new function to `Data.Digit`:
  ```agda
  toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
  ```

* Added new proof to `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`:
  ```agda
  concat⁺ : Sublist (Sublist R) ass bss → Sublist R (concat ass) (concat bss)
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

* Added new proof to `Data.Nat.DivMod`:
  ```agda
  [a/n]*n≤a : (a div (suc n)) * (suc n) ≤ a
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
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

* Added new proof to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  ≢-sym : Symmetric {A = A} _≢_
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

* The relation `_≅_` in `Relation.Binary.HeterogeneousEquality` has
  been generalised so that the types of the two equal elements need not
  be at the same universe level.

* Added new proofs to `Relation.Nullary.Construct.Add.Point`:
  ```agda
  ≡-dec        : Decidable {A = A} _≡_ → Decidable {A = Pointed A} _≡_
  []-injective : [ x ] ≡ [ y ] → x ≡ y
  ```
