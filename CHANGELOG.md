Version TODO
============

The library has been tested using Agda version 2.5.4.1.

Important changes since 0.17:

Non-backwards compatible changes
--------------------------------

#### Overhaul of `Data.Maybe`

Splitting up `Data.Maybe` into the standard hierarchy.

* Moved `Data.Maybe.Base`'s `Is-just`, `Is-nothing`, `to-witness`,
  and `to-witness-T` to `Data.Maybe` (they rely on `All` and `Any`
  which are now outside of `Data.Maybe.Base`).

* Moved `Data.Maybe.Base`'s `All` and `Data.Maybe`'s `allDec` to
  `Data.Maybe.All` and renamed some proofs:
  ```agda
  allDec ↦ dec
  ```

* Moved `Data.Maybe.Base`'s `Any` and `Data.Maybe`'s `anyDec` to
  `Data.Maybe.Any` and renamed some proofs:
  ```agda
  anyDec ↦ dec
  ```

* Created `Data.Maybe.Properties`, moved `Data.Maybe.Base`'s `just-injective`
  there and populated it with basic results.

* Moved `Data.Maybe`'s `Eq` to `Data.Maybe.Relation.Pointwise` and
  renamed some proofs:
  ```agda
  Eq                  ↦ Pointwise
  Eq-refl             ↦ refl
  Eq-sym              ↦ sym
  Eq-trans            ↦ trans
  Eq-dec              ↦ dec
  Eq-isEquivalence    ↦ isEquivalence
  Eq-isDecEquivalence ↦ isDecEquivalence
  ```

Other major changes
-------------------

* Added new module `Data.Vec.Any.Properties`

Deprecated features
-------------------

Other minor additions
---------------------

* Added new function to `Data.Fin.Base`:
  ```agda
  cast : m ≡ n → Fin m → Fin n
  ```

* Added new proof to `Data.Fin.Properties`:
  ```agda
  toℕ-cast    : toℕ (cast eq k) ≡ toℕ k
  ```

* Added new operations to `Data.List.All`:
  ```agda
  zipWith   : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q

  sequenceA : All (F ∘′ P) ⊆ F ∘′ All P
  sequenceM : All (M ∘′ P) ⊆ M ∘′ All P
  mapA      : (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  mapM      : (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forA      : All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  forM      : All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  ```

* Added new operators to `Data.List.Base`:
  ```agda
  _[_]%=_ : (xs : List A) → Fin (length xs) → (A → A) → List A
  _[_]∷=_ : (xs : List A) → Fin (length xs) → A → List A
  _─_     : (xs : List A) → Fin (length xs) → List A
  ```

* Added new proofs to `Data.List.All.Properties`:
  ```agda
  respects : P Respects _≈_ → (All P) Respects _≋_
  ```

* Added new proof to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-allFin : (k : Fin n) → k ∈ allFin n
  ```

* Added new function to `Data.List.Membership.(Setoid/Propositional)`:
  ```agda
  _∷=_    : x ∈ xs → A → List A
  _─_     : (xs : List A) → x ∈ xs → List A
  ```

* Added new proofs to `Data.List.Membership.(Setoid/Propositional).Properties`:
  ```agda
  length-mapWith∈ : length (mapWith∈ xs f) ≡ length xs
  length-∷=       : length (pr ∷= v) ≡ length xs
  ∈-∷=⁺-updated   : v ∈ (pr ∷= v)
  ∈-∷=⁺-untouched : (¬ x ≈ y) → y ∈ xs → y ∈ (pr ∷= v)
  ∈-∷=⁻           : (¬ y ≈ v) → y ∈ (pr ∷= v) → y ∈ xs
  map-∷=          : map f (pr ∷= v) ≡ ∈-map⁺ f≈ pr ∷= f v
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  length-%= : length (xs [ k ]%= f) ≡ length xs
  length-∷= : length (xs [ k ]∷= v) ≡ length xs
  map-∷=    : map f (xs [ k ]∷= v) ≡ map f xs [ cast eq k ]∷= f v
  length-─  : length (xs ─ k) ≡ pred (length xs)
  map-─     : map f (xs ─ k) ≡ map f xs ─ cast eq k
  ```

* Added new proofs to `Data.Maybe.All`:
  ```agda
  drop-just        : All P (just x) → P x
  just-equivalence : P x ⇔ All P (just x)
  map              : P ⊆ Q → All P ⊆ All Q
  fromAny          : Any P ⊆ All P
  zipWith          : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith        : P ⊆ Q ∩ R → All P ⊆ All Q ∩ All R
  zip              : All P ∩ All Q ⊆ All (P ∩ Q)
  unzip            : All (P ∩ Q) ⊆ All P ∩ All Q
  sequenceA        : RawApplicative F → All (F ∘′ P) ⊆ F ∘′ All P
  mapA             : RawApplicative F → (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  forA             : RawApplicative F → All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  sequenceM        : RawMonad M → All (M ∘′ P) ⊆ M ∘′ All P
  mapM             : RawMonad M → (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forM             : RawMonad M → All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  universal        : Universal P → Universal (All P)
  irrelevant       : Irrelevant P → Irrelevant (All P)
  satisfiable      : Satisfiable (All P)
  ```

* Created `Data.Maybe.All.Properties`:
  ```agda
  map⁺ : All (P ∘ f) mx → All P (map f mx)
  map⁻ : All P (map f mx) → All (P ∘ f) mx
  gmap : P ⊆ Q ∘ f → All P ⊆ All Q ∘ map f
  <∣>⁺ : All P mx → All P my → All P (mx <∣> my)
  <∣>⁻ : All P (mx <∣> my) → All P mx
  ```

* Added new proofs to `Data.Maybe.Any`:
  ```agda
  drop-just        : Any P (just x) → P x
  just-equivalence : P x ⇔ Any P (just x)
  map              : P ⊆ Q → Any P ⊆ Any Q
  satisfied        : Any P x → ∃ P
  zipWith          : P ∩ Q ⊆ R → Any P ∩ Any Q ⊆ Any R
  unzipWith        : P ⊆ Q ∩ R → Any P ⊆ Any Q ∩ Any R
  zip              : Any P ∩ Any Q ⊆ Any (P ∩ Q)
  unzip            : Any (P ∩ Q) ⊆ Any P ∩ Any Q
  irrelevant       : Irrelevant P → Irrelevant (Any P)
  satisfiable      : Satisfiable P → Satisfiable (Any P)
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  _<∣>_     : Maybe A → Maybe A → Maybe A
  ```

* Added new functions to `Data.Vec.Any.Properties`:
  ```agda
  lookup-index : (p : Any P xs) → P (lookup (index p) xs)
  fromList⁺    : List.Any P xs → Any P (fromList xs)
  fromList⁻    : Any P (fromList xs) → List.Any P xs
  toList⁺      : Any P xs → List.Any P (toList xs)
  toList⁻      : List.Any P (toList xs) → Any P xs
  ```

* Added new functions to `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  fromAny : Any P xs → ∃ λ x → x ∈ xs × P x
  toAny   : x ∈ xs → P x → Any P xs
  ```
