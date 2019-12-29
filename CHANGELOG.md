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

Deprecated names
----------------

The following deprecations have occurred as part of a drive to improve consistency
across the library. The deprecated names still exist and therefore all existing code
should still work, however use of the new names is encouraged. Although not anticipated
any time soon, they may eventually be removed in some future release of the library.
Automated warnings are attached to all deprecated names to discourage their use.

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  Any¬→¬All  ↦  Any¬⇒¬All
  ```

Other major additions
---------------------

Other minor additions
---------------------

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ⁻¹-injective   : x ⁻¹ ≈ y ⁻¹ → x ≈ y
  ⁻¹-anti-homo-∙ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ```

* Made `RawFunctor`,  `RawApplicative` and `IFun` more level polymorphic
  (in `Category.Functor`, `Category.Applicative` and
  `Category.Applicative.Indexed`
  respectively).

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

* Added new proofs to `Data.Integer.Properties`, useful to migrate to 1.1's new `_<_`.

  ```agda
  m+1≤n⇒m<n : sucℤ m ≤ n → m < n
  m<n⇒m+1≤n : m < n → sucℤ m ≤ n
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
