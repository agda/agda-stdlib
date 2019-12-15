Version 1.3-dev
===============

The library has been tested using Agda version 2.6.0.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

* The following lemmas may have breaking changes in their computational
  behaviour.
  - `Data.Fin.Permutation.Components`: `transpose-inverse`
  - `Data.Fin.Properties`: `decFinSubset`, `all?`

  Definitions that are sensitive to the behaviour of these lemmas, rather than
  just their existence, may need to be revised.

Other major additions
---------------------

* New modules
  ```
  Data.List.Show.Core
  Data.List.Show
  Data.Vec.Show
  ```

Other minor additions
---------------------

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ⁻¹-injective   : x ⁻¹ ≈ y ⁻¹ → x ≈ y
  ⁻¹-anti-homo-∙ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ```

* Added new proofs to `Data.Bool`:
  ```agda
  not-injective : not x ≡ not y → x ≡ y
  ```

* Added new properties to `Data.Fin.Subset`:
  ```agda
  _⊂_ : Subset n → Subset n → Set
  _⊄_ : Subset n → Subset n → Set
  ```

* Added induction over subsets to `Data.Fin.Subset.Induction`.

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  s⊆s : p ⊆ q → s ∷ p ⊆ s ∷ q

  x∈s⇒x∉∁s : x ∈ s → x ∉ ∁ s
  x∈∁s⇒x∉s : x ∈ ∁ s → x ∉ s
  x∉∁s⇒x∈s : x ∉ ∁ s → x ∈ s
  x∉s⇒x∈∁s : x ∉ s → x ∈ ∁ s
  ```

* Added new functions to `Data.List.Base`:
  ```agda
  _?∷_  : Maybe A → List A → List A
  _∷ʳ?_ : List A → Maybe A → List A
  ```

* Added new property to `Data.Nat.Properties`:
  ```
  ⌊n/2⌋+⌈n/2⌉≡n : ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
  ```

* Added new functions to `Data.String.Base`:
  ```agda
  padLeft    : Char → ℕ → String → String
  padRight   : Char → ℕ → String → String
  padBoth    : Char → Char → ℕ → String → String

  rectangle  : (ℕ → String → String) → Vec String n → Vec String n
  rectangleˡ : Char → Vec String n → Vec String n
  rectangleʳ : Char → Vec String n → Vec String n
  rectangleᶜ : Char → Char → Vec String n → Vec String n
  ```

* Added new functions to `Data.Vec.Base`:
  ```
  transpose : Vec (Vec A n) m → Vec (Vec A m) n
  ```

* Added new functions to `Data.Vec`:
  ```
  rectangle  : ∀[ Vec≤ A ⇒ Vec A ] → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
  rectangleˡ : A → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
  rectangleʳ : A → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
  rectangleᶜ : A → A → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
  ```

* Added new functions to `Data.Vec.Bounded.Base`:
  ```agda
  padLeft   : A → Vec≤ A n → Vec A n
  padRight  : A → Vec≤ A n → Vec A n
  padBoth : ∀ {n} → A → A → Vec≤ A n → Vec A n

  rectangle : List (∃ (Vec≤ A)) → ∃ (List ∘ Vec≤ A)
  ```

* Added a new proof to `Relation.Nullary.Decidable`:
  ```agda
  isYes≗does : (P? : Dec P) → isYes P? ≡ does P?
  ```

* Rewrote definitions branching on a `Dec` value to branch only on the boolean
  `does` field, wherever possible. Furthermore, branching on the `proof` field
  has been made as late as possible, using the `invert` lemma from
  `Relation.Nullary.Reflects`.

  For example, the old definition of `filter` in `Data.List.Base` used the
  `yes` and `no` patterns, which desugared to the following.

  ```agda
  filter : ∀ {P : Pred A p} → Decidable P → List A → List A
  filter P? [] = []
  filter P? (x ∷ xs) with P? x
  ... | false because ofⁿ _ = filter P? xs
  ... |  true because ofʸ _ = x ∷ filter P? xs
  ```

  Because the proofs (`ofⁿ _` and `ofʸ _`) are not giving us any information,
  we do not need to match on them. We end up with the following definition,
  where the `proof` field has been projected away.

  ```agda
  filter : ∀ {P : Pred A p} → Decidable P → List A → List A
  filter P? [] = []
  filter P? (x ∷ xs) with does (P? x)
  ... | false = filter P? xs
  ... | true  = x ∷ filter P? xs
  ```

  Correspondingly, when proving a property of `filter`, we can often make a
  similar change, but sometimes need the proof eventually. The following
  example is adapted from `Data.List.Membership.Setoid.Properties`.

  ```agda
  module _ {c ℓ p} (S : Setoid c ℓ) {P : Pred (Carrier S) p}
           (P? : Decidable P) (resp : P Respects (Setoid._≈_ S)) where

    open Membership S using (_∈_)

    ∈-filter⁺ : ∀ {v xs} → v ∈ xs → P v → v ∈ filter P? xs
    ∈-filter⁺ {xs = x ∷ _} (here v≈x) Pv with P? x
    -- There is no matching on the proof, so we can emit the result without
    -- computing the proof at all.
    ... |  true because   _   = here v≈x
    -- `invert` is used to get the proof just when it is needed.
    ... | false because [¬Px] = contradiction (resp v≈x Pv) (invert [¬Px])
    -- In the remaining cases, we make no use of the proof.
    ∈-filter⁺ {xs = x ∷ _} (there v∈xs) Pv with does (P? x)
    ... | true  = there (∈-filter⁺ v∈xs Pv)
    ... | false = ∈-filter⁺ v∈xs Pv
  ```
