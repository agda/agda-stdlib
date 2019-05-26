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
  Algebra.Properties.CommutativeSemigroup

  Category.Monad.Reader

  Data.AVL.NonEmpty
  Data.AVL.NonEmpty.Propositional

  Data.List.Relation.Binary.Disjoint.Propositional
  Data.List.Relation.Binary.Disjoint.Setoid
  Data.List.Relation.Binary.Disjoint.Setoid.Properties

  Data.List.Relation.Unary.AllPairs
  Data.List.Relation.Unary.AllPairs.Properties
  Data.List.Relation.Unary.Unique.Propositional
  Data.List.Relation.Unary.Unique.Propositional.Properties
  Data.List.Relation.Unary.Unique.Setoid
  Data.List.Relation.Unary.Unique.Setoid.Properties

  Data.Sign.Base

  Data.These.Base

  Data.Unit.Properties

  Data.Trie
  Data.Trie.NonEmpty

  Relation.Binary.Construct.Closure.Equivalence.Properties
  Relation.Binary.Rewriting

  Relation.Binary.Properties.Setoid
  ```

* ``Data/Bin.agda`` and ``Data.Bin/*.agda``  of lib-1.0 are removed,
  added new ``Data.Bin.Base, Data.Bin.Properties``.



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

* In `Reflection`:
  ```agda
  returnTC ↦ return
  ```

* In `Data.(Char/String).Properties`:
  ```agda
  setoid           ↦ ≡-setoid
  decSetoid        ↦ ≡-decSetoid
  strictTotalOrder ↦ <-strictTotalOrder-≈
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

* Added new proof to `Data.Bool.Properties`:
  ```agda
  ≡-setoid : Setoid 0ℓ 0ℓ
  ```

* Added new function to `Data.AVL.Indexed`:
  ```agda
  toList : Tree V l u h → List (K& V)
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
  ≡-setoid : Setoid 0ℓ 0ℓ
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
  ≤-<-connex : Connex _≤_ _<_
  ≥->-connex : Connex _≥_ _>_
  <-≤-connex : Connex _<_ _≤_
  >-≥-connex : Connex _>_ _≥_

  1+n≢0      : suc n ≢ 0
  0≢1+n      : 0 ≢ suc n
  n<1+n      : n < suc n   (by ≤-refl)
  m*[1+n]    : m * (suc n) ≡ m + m * n
  2m≢1+2n    : 2 * m ≢ 1 + 2 * n
  m>1⇒m*n≢1 : m > 1 ⇒ m * n ≢ 1

  <ᵇ⇒<      : T (m <ᵇ n) → m < n
  <⇒<ᵇ      : m < n → T (m <ᵇ n)
  n≢0⇒n>0   : n ≢ 0 → n > 0
  m≤m*n      : 0 < n → m ≤ m * n
  m<m*n      : 0 < m → 1 < n → m < m * n
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

* Added new definitions in `Relation.Binary.Core`:
  ```agda
  Universal _∼_  = ∀ x y → x ∼ y

  _←→_ A B = (A → B) × (B → A),
  ```

  definition of ``_Respects2_`` and proofs for its relation to ``_Respects₂_``

  ```

* The relation `_≅_` in `Relation.Binary.HeterogeneousEquality` has
  been generalised so that the types of the two equal elements need not
  be at the same universe level.

* Added new proof to `Relation.Binary.PropositionalEquality.Core`:
  ```agda
  ≢-sym : Symmetric _≢_
  ```

