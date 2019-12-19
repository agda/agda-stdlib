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

* The following record definitions in `Algebra.Structures` have been changed.

  - `IsCommutativeMonoid`
  - `IsCommutativeSemiring`
  - `IsRing`

  In all of these cases, the change has been to give each of these structures
  access to *all* of the fields of structures below (weaker) in the hierarchy.
  For example, consider `IsCommutativeMonoid`. The old definition effectively
  required the following fields.

  - Associativity
  - Left identity
  - Commutativity

  The new definition also requires:

  - Right identity.

  The justification for not including a right identity proof was that, given
  left identity and commutativity, right identity can be proven. However,
  omitting the right identity proof caused problems:

  1. It made the definition longer and more complex, as less code was reused.
  2. The forgetful map turning a commutative monoid into a monoid was not a
     retraction of all maps which augment a monoid with commutativity. To see
     that the forgetful map was not a retraction, notice that the augmentation
     must have discarded the right identity proof as there was no field for it
     in `IsCommutativeMonoid`.
  3. There was no easy way to give only the right identity proof, and have
     the left identity proof be generically derived.

  Point 2, and in particular the fact that it did not hold definitionally,
  caused problems when indexing over monoids and commutative monoids and
  requiring some compatibility between the two indexings.

  With the new definition, we address point 3 and recover the convenience of
  the old definition simultaneously. We do this by introducing *biased*
  structures, found in `Algebra.Structures.Biased`. In particular, one can
  generally convert old instances of `IsCommutativeMonoid` to new instances
  using the `IsCommutativeMonoidˡ` biased structure. This is introduced by
  the function `isCommutativeMonoidˡ`, so old instances can be converted as
  follows.

  ```agda
  --    Add this part:  ↓----↓----↓----↓----↓
  isCommutativeMonoid = isCommutativeMonoidˡ record
    { isSemigroup = ...  -- Everything
    ; identityˡ   = ...  -- else is
    ; comm        = ...  -- the same.
    }
  ```

  For `IsCommutativeSemiring`, we have `IsCommutativeSemiringˡ`, and for
  `IsRing`, we have `IsRingWithoutAnnihilatingZero`.

Other major additions
---------------------

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
