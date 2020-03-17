Version 1.3
===========

The library has been tested using Agda version 2.6.1.

Highlights
----------

* Monoid and ring tactics that are capable of solving equalities
  without having to restate the equation.

* Binary and rose trees.

* Warnings when importing deprecated modules.

Bug-fixes
---------

* In `Data.Fin.Subset.Properties` the incorrectly named proof 
  `p⊆q⇒∣p∣<∣q∣ : p ⊆ q → ∣ p ∣ ≤ ∣ q ∣` has been renamed to `p⊆q⇒∣p∣≤∣q∣`.

* In `Data.Nat.Properties` the incorrectly named proofs 
  `∀[m≤n⇒m≢o]⇒o<n : (∀ {m} → m ≤ n → m ≢ o) → n < o`
  and `∀[m<n⇒m≢o]⇒o≤n : (∀ {m} → m < n → m ≢ o) → n ≤ o` 
  have been renamed to `∀[m≤n⇒m≢o]⇒n<o` and `∀[m<n⇒m≢o]⇒n≤o` respectively.

* Fixed the definition of `_⊓_` for `Codata.Conat`; it was mistakenly using
  `_⊔_` in a recursive call.

* Fixed the type of `max≈v⁺` in `Data.List.Extrema`; it was mistakenly talking
  about `min` rather than `max`.

* The module `⊆-Reasoning` in `Data.List.Relation.Binary.BagAndSetEquality` 
  now exports the correct set of combinators.

* The record `DecStrictPartialOrder` now correctly re-exports the contents 
  of its `IsDecStrictPartialOrder` field.

Non-backwards compatible changes
--------------------------------

#### Changes to how equational reasoning is implemented

* NOTE: __Uses__ of equational reasoning remains unchanged. These changes should only
  affect users who are renaming/hiding the library's equational reasoning combinators.

* Previously all equational reasoning combinators (e.g. `_≈⟨_⟩_`, `_≡⟨_⟩_`, `_≤⟨_⟩_`)
  were defined in the following style:
  ```agda
  infixr 2 _≡⟨_⟩_

  _≡⟨_⟩_ : ∀ x {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z
  ```
  The type checker therefore infers the RHS of the equational step from the LHS + the
  type of the proof. For example for `x ≈⟨ x≈y ⟩ y ∎` it is inferred that `y ∎`
  must have type `y IsRelatedTo y` from `x : A` and `x≈y : x ≈ y`.

* There are two problems with this. Firstly, it means that the reasoning combinators are
  not compatible with macros (i.e. tactics) that attempt to automatically generate proofs
  for `x≈y`. This is because the reflection machinary does not have access to the type of RHS
  as it cannot be inferred. In practice this meant that the new reflective solvers
  `Tactic.RingSolver` and `Tactic.MonoidSolver` could not be used inside the equational
  reasoning. Secondly the inference procedure itself is slower as described in this
  [exchange](https://lists.chalmers.se/pipermail/agda/2016/009090.html)
  on the Agda mailing list.

* Therefore, as suggested on the mailing list, the order of arguments to the combinators
  have been reversed so that instead the type of the proof is inferred from the LHS + RHS.
  ```agda
  infixr -2 step-≡

  step-≡ : ∀ x {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ y≡z x≡y = trans x≡y y≡z

  syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z
  ```
  where the `syntax` declaration is then used to recover the original order of the arguments.
  This change enables the use of macros and anecdotally speeds up type checking by a
  factor of 5.

* No changes are needed when defining new combinators, as the old and new styles are
  compatible. Having said that you may want to switch to the new style for the benefits
  described above.

* **Changes required**: The only drawback to this change is that hiding and renaming the
  combinators no longer works  as before, as `_≡⟨_⟩_` etc. are now syntax instead of names. 
  For example instead of:
  ```agda
  open SetoidReasoning setoid public
    hiding (_≈⟨_⟩_) renaming (_≡⟨_⟩_ to _↭⟨_⟩_)
  ```
  one must now write :
  ```agda
  private
    module Base = SetoidReasoning setoid
  open Base public hiding (step-≈; step-≡)

  infixr 2 step-↭
  step-↭ = Base.step-≡
  syntax step-↭ x y≡z x≡y = x ↭⟨ x≡y ⟩ y≡z
  ```
  This is more verbose than before, but we hope that the advantages outlined above
  outweigh this minor inconvenience. (As an aside, it is hoped that at some point Agda might
  provide the ability to rename syntax that automatically generates the above boilerplate).


#### Changes to the algebra hierarchy

* The following record definitions in `Algebra.Structures` have been changed.
  - `IsCommutativeMonoid`
  - `IsCommutativeSemiring`
  - `IsRing`
  
  In each case, the structure now requires fields for all the required properties, 
  rather than just an (arbitrary) minimal set of properties.
  
* For example, whereas the old definition of `IsCommutativeMonoid` required 
  the following fields:
  
  - Associativity
  - Left identity
  - Commutativity

  the new definition also requires:

  - Right identity.

* Previously, the justification for not including a right identity proof was that,
  given left identity and commutativity, right identity can be proven. However,
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
  causes problems when indexing over monoids and commutative monoids and
  requires some compatibility between the two indexings.

* **Changes required**: We recover the old behaviour by introducing *biased*
  structures, found in `Algebra.Structures.Biased`. In particular, one can
  convert old instances of `IsCommutativeMonoid` to new instances using the 
  `isCommutativeMonoidˡ` function. For example:
  ```agda
  isCommutativeMonoid = record
    { isSemigroup = ...
    ; identityˡ   = ...
    ; comm        = ...
    }
  ```
  becomes:
  ```agda
  open import Algebra.Structures.Biased
  
  isCommutativeMonoid = isCommutativeMonoidˡ record
    { isSemigroup = ...
    ; identityˡ   = ...
    ; comm        = ...
    }
  ```

* For `IsCommutativeSemiring`, we have `isCommutativeSemiringˡ`, and for
  `IsRing`, we have `isRingWithoutAnnihilatingZero`.

#### Tweak to definition of `Permutation.refl`

* The definition of `refl` in `Data.List.Relation.Binary.Permutation.Homogeneous/Setoid`
  has been changed from
  ```agda
  refl  : ∀ {xs} → Permutation R xs xs
  ```
  to:
  ```agda
  refl  : ∀ {xs ys} → Pointwise R xs ys → Permutation R xs ys
  ```
  The old definition did not allow for size preserving transformations of permutations
  via pointwise equalities and hence made it difficult to prove termination of complicated
  proofs and functions over permutations.

* Correspondingly the proofs `isEquivalence` and `setoid` in `Permutation.Homogeneous`
  now require that the base relation `R` is reflexive.

#### Improved safety for `Word` and `Float`

* Decidable equality over floating point numbers has been made safe and
  so  `_≟_` has been moved from `Data.Float.Unsafe` to `Data.Float.Properties`.

* Decidable equality over words has been made safe and so `_≟_` has been
  moved from `Data.Word.Unsafe` to `Data.Word.Properties`.

* The modules `Data.Word.Unsafe` and `Data.Float.Unsafe` have been removed
  as there are no longer any unsafe operations.

#### Other

* The following lemmas may have breaking changes in their computational
  behaviour.
  - `transpose-inverse` in `Data.Fin.Permutation.Components`
  - `decFinSubset` & `all?` in `Data.Fin.Properties`

  Definitions that are sensitive to the behaviour of these lemmas, rather than
  just their existence, may need to be revised.

* The fixity level of `Data.List.Base`'s `_∷ʳ_` has been changed from 5 to 6.
  This means that `x ∷ xs ∷ʳ y` and `x ++ xs ∷ʳ y` are not ambiguous
  anymore: they both are parenthesised to the right (the more efficient
  variant).

* In `Codata.Cowriter` and `Codata.Musical.Colist` the functions `splitAt`, `take`
  and `take-⊑` have been changed to use bounded vectors as defined in
  `Data.Vec.Bounded` instead of the deprecated `Data.BoundedVec`. The old proofs
  still exist under the names `splitAt′`, `take′` and `take′-⊑` but have been
  deprecated.

* In `Codata.Colist`, uses of `Data.BoundedVec` have been replaced with the more
  up to date `Data.Vec.Bounded`.

Deprecated modules
------------------

* A warning is now raised whenever you import a deprecated module. This should 
  aid the transition to the new modules. These warnings can be disabled locally
  by adding the pragma `{-# OPTIONS --warn=noUserWarning #-}` to the top of a module.

The following modules have been renamed as part of a drive to improve
consistency across the library. The deprecated modules still exist and
therefore all existing code should still work, however use of the new names
is encouraged.

* In `Algebra`:
  ```
  Algebra.FunctionProperties.Consequences.Core           ↦ Algebra.Consequences.Base
  Algebra.FunctionProperties.Consequences.Propositional  ↦ Algebra.Consequences.Propositional
  Algebra.FunctionProperties.Consequences                ↦ Algebra.Conseqeunces.Setoid
  ```

* The sub-module `Lexicographic` in `Data.Induction.WellFounded` has been deprecated,
  instead the new proofs of well-foundedness in `Data.Product.Relation.Binary.Lex.Strict`
  should be used.
  
Deprecated names
----------------

The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.

* In `Data.Fin`:
  ```agda
  fromℕ≤  ↦ fromℕ<
  fromℕ≤″ ↦ fromℕ<″
  ```

* In `Data.Fin.Properties`
  ```agda
  fromℕ≤-toℕ       ↦ fromℕ<-toℕ
  toℕ-fromℕ≤       ↦ toℕ-fromℕ<
  fromℕ≤≡fromℕ≤″   ↦ fromℕ<≡fromℕ<″
  toℕ-fromℕ≤″      ↦ toℕ-fromℕ<″
  isDecEquivalence ↦ ≡-isDecEquivalence
  preorder         ↦ ≡-preorder
  setoid           ↦ ≡-setoid
  decSetoid        ↦ ≡-decSetoid
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  Any¬→¬All  ↦  Any¬⇒¬All
  ```

* In `Data.Nat.Properties`:
  ```agda
  ∀[m≤n⇒m≢o]⇒o<n  ↦  ∀[m≤n⇒m≢o]⇒n<o
  ∀[m<n⇒m≢o]⇒o≤n  ↦  ∀[m<n⇒m≢o]⇒n≤o
  ```

* In `Algebra.Morphism.Definitions` and `Relation.Binary.Morphism.Definitions`
  the type `Morphism A B` has been deprecated in favour of the standard
  function notation `A → B`.

New modules
-----------

* A hierarchy for algebraic modules:
  ```
  Algebra.Module
  Algebra.Module.Bundles
  Algebra.Module.Consequences
  Algebra.Module.Construct.Biproduct
  Algebra.Module.Construct.TensorUnit
  Algebra.Module.Construct.Zero
  Algebra.Module.Definitions
  Algebra.Module.Definitions.Bi
  Algebra.Module.Definitions.Left
  Algebra.Module.Definitions.Right
  Algebra.Module.Structures
  Algebra.Module.Structures.Biased
  ```
  Supported are all of {left, right, bi} {semi} modules.

* Morphisms over group and ring-like algebraic structures:
  ```agda
  Algebra.Morphism.GroupMonomorphism
  Algebra.Morphism.RingMonomorphism
  ```

* Bisimilarity relation for `Cowriter`.
  ```agda
  Codata.Cowriter.Bisimilarity
  ```

* Wrapper for the erased modality, allows the storage of erased proofs 
  in a record and the use of projections to manipulate them without having 
  to turn on the unsafe option `--irrelevant-projections`.
  ```agda
  Data.Erased
  ```

* Induction over finite subsets:
  ```agda
  Data.Fin.Subset.Induction
  ```

* Unary predicate for lists in which all related elements are grouped together.
  ```agda
  Data.List.Relation.Unary.Grouped
  Data.List.Relation.Unary.Grouped.Properties
  ```

* Unary predicate for products in which the components both satisfy individual 
  unary predicates.
  ```agda
  Data.Product.Relation.Unary.All
  ```
  
* New data type for dependent products in which the second component is irrelevant.
  ```agda
  Data.Refinement
  Data.Refinement.Relation.Unary.All
  ```

* New data type for binary and rose trees:
  ```agda
  Data.Tree.Binary
  Data.Tree.Binary.Properties
  Data.Tree.Binary.Relation.Unary.All
  Data.Tree.Binary.Relation.Unary.All.Properties
  Data.Tree.Rose
  Data.Tree.Rose.Properties
  ```

* New properties and functions over floats and words.
  ```agda
  Data.Float.Base
  Data.Float.Properties
  Data.Word.Base
  Data.Word.Properties
  ```

* Helper methods for using reflection with numeric data.
  ```agda
  Data.Nat.Reflection
  Data.Fin.Reflection
  ```

* Finer-grained breakdown of the reflection primitives, alongside
  new utility functions for writing macros.
  ```agda
  Reflection.Abstraction
  Reflection.Argument
  Reflection.Argument.Information
  Reflection.Argument.Relevance
  Reflection.Argument.Visibility
  Reflection.Definition
  Reflection.Literal
  Reflection.Meta
  Reflection.Name
  Reflection.Pattern
  Reflection.Term
  Reflection.TypeChecking.MonadSyntax
  ```
  
* New tactics for monoid and ring solvers. See `README.Tactic.MonoidSolver/RingSolver` for details
  ```agda
  Tactic.MonoidSolver
  Tactic.RingSolver
  Tactic.RingSolver.NonReflective
  ```

Other major changes
-------------------

#### Improved performance of decision processes

* All definitions branching on a `Dec` value have been rewritten, wherever possible,
  to branch only  on the boolean `does` field. Furthermore, branching on 
  the `proof` field has been made as late as possible, using the `invert` lemma from
  `Relation.Nullary.Reflects`.

* For example, the old definition of `filter` in `Data.List.Base` used the
  `yes` and `no` patterns, which desugared to the following:
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

#### Other

* The module `Reflection` is no longer `--unsafe`.

* Standardised the `Eq` modules in structures and bundles in `Relation.Binary` hierarchy.
  - `IsDecTotalOrder.Eq` now exports `isDecPartialOrder`.
  - `DecSetoid.Eq` now exports `partialSetoid` and `_≉_`.
  - `Poset.Eq` and `TotalOrder.Eq` now export `setoid`.
  - `DecTotalOrder.Eq` and `StrictTotalOrder.Eq` now export `decSetoid`.
  - `DecTotalOrder.decSetoid` is now deprecated in favour of the above `DecTotalOrder.Eq.decSetoid`.

Other minor additions
---------------------

* Added new record to `Algebra.Bundles`:
  ```agda
  +-rawGroup : RawGroup c ℓ
  ```
  and the `CommutativeMonoid` record now exports `commutativeSemigroup`.

* Added new definition to `Algebra.Definitions`:
  ```agda
  Interchangable _∘_ _∙_ = ∀ w x y z → ((w ∙ x) ∘ (y ∙ z)) ≈ ((w ∘ y) ∙ (x ∘ z))
  ```

* Added new records to `Algebra.Morphism.Structures`:
  ```agda
  IsGroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsGroupMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsGroupIsomorphism  (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  IsRingHomomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsRingMonomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsRingIsomorphism   (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  ```

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ⁻¹-injective   : x ⁻¹ ≈ y ⁻¹ → x ≈ y
  ⁻¹-anti-homo-∙ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ```

* In `Algebra.Structures` the record `IsCommutativeSemiring` now 
  exports `*-isCommutativeSemigroup`.

* Made `RawFunctor`,  `RawApplicative` and `IFun` more level polymorphic
  in `Category.Functor`, `Category.Applicative` and `Category.Applicative.Indexed` 
  respectively.

* Added new functions to `Codata.Colist`:
  ```agda
  drop   : ℕ → Colist A ∞ → Colist A ∞
  concat : Colist (List⁺ A) i → Colist A i
  ```

* Added new definitions to `Codata.Colist.Bisimilarity`:
  ```agda
  fromEq        : as ≡ bs → i ⊢ as ≈ bs
  isEquivalence : IsEquivalence R → IsEquivalence (Bisim R i)
  setoid        : Setoid a r → Size → Setoid a (a ⊔ r)
  module ≈-Reasoning

  ++⁺  : Pointwise R as bs → Bisim R i xs ys → Bisim R i (fromList as ++ xs) (fromList bs ++ ys)
  ⁺++⁺ : Pointwise R (toList as) (toList bs) → Thunk^R (Bisim R) i xs ys → Bisim R i (as ⁺++ xs) (bs ⁺++ ys)
  ```

* Added new proofs to `Codata.Colist.Properties`:
  ```agda
  fromCowriter∘toCowriter≗id : i ⊢ fromCowriter (toCowriter as) ≈ as
  length-∷                   : i ⊢ length (a ∷ as) ≈ 1 ℕ+ length (as .force)
  length-replicate           : i ⊢ length (replicate n a) ≈ n
  length-++                  : i ⊢ length (as ++ bs) ≈ length as + length bs
  length-map                 : i ⊢ length (map f as) ≈ length as
  length-scanl               : i ⊢ length (scanl c n as) ≈ 1 ℕ+ length as
  replicate-+                : i ⊢ replicate (m + n) a ≈ replicate m a ++ replicate n a
  map-replicate              : i ⊢ map f (replicate n a) ≈ replicate n (f a)
  lookup-replicate           : All (a ≡_) (lookup k (replicate n a))
  map-unfold                 : i ⊢ map f (unfold alg a) ≈ unfold (Maybe.map (Prod.map₂ f) ∘ alg) a
  unfold-nothing             : alg a ≡ nothing → unfold alg a ≡ []
  unfold-just                : alg a ≡ just (a′ , b) → i ⊢ unfold alg a ≈ b ∷ λ where .force → unfold alg a′
  scanl-unfold               : i ⊢ scanl cons nil (unfold alg a) ≈ nil ∷ (λ where .force → unfold alg′ (a , nil))
  map-alignWith              : i ⊢ map f (alignWith al as bs) ≈ alignWith (f ∘ al) as bs
  length-alignWith           : i ⊢ length (alignWith al as bs) ≈ length as ⊔ length bs
  map-zipWith                : i ⊢ map f (zipWith zp as bs) ≈ zipWith (λ a → f ∘ zp a) as bs
  length-zipWith             : i ⊢ length (zipWith zp as bs) ≈ length as ⊓ length bs
  drop-nil                   : i ⊢ drop {A = A} m [] ≈ []
  drop-drop-fusion           : i ⊢ drop n (drop m as) ≈ drop (m ℕ.+ n) as
  map-drop                   : i ⊢ map f (drop m as) ≈ drop m (map f as)
  length-drop                : i ⊢ length (drop m as) ≈ length as ∸ m
  length-cotake              : i ⊢ length (cotake n as) ≈ n
  map-cotake                 : i ⊢ map f (cotake n as) ≈ cotake n (Stream.map f as)
  drop-fromList-++-identity  : drop (length as) (fromList as ++ bs) ≡ bs
  drop-fromList-++-≤         : m ≤ length as → drop m (fromList as ++ bs) ≡ fromList (drop m as) ++ bs
  drop-fromList-++-≥         : m ≥ length as → drop m (fromList as ++ bs) ≡ drop (m ∸ length as) bs
  drop-⁺++-identity          : drop (length as) (as ⁺++ bs) ≡ bs .force
  map-chunksOf               : i ⊢ map (map f) (map f) (chunksOf n as) ≈ chunksOf n (map f as)
  fromList-++                : i ⊢ fromList (as ++ bs) ≈ fromList as ++ fromList bs
  fromList-scanl             : i ⊢ scanl c n (fromList as) ≈ fromList (scanl c n as)
  map-fromList               : i ⊢ map f (fromList as) ≈ fromList (map f as)
  length-fromList            : i co⊢ length (fromList as) ≈ fromℕ (length as)
  fromStream-++              : i ⊢ fromStream (as ++ bs) ≈ fromList as ++ fromStream bs
  fromStream-⁺++             : i ⊢ fromStream (as ⁺++ bs) ≈ fromList⁺ as ++ fromStream (bs .force)
  fromStream-concat          : i ⊢ concat (fromStream ass) ≈ fromStream (concat ass)
  fromStream-scanl           : i ⊢ scanl c n (fromStream as) ≈ fromStream (scanl c n as)
  map-fromStream             : i ⊢ map f (fromStream as) ≈ fromStream (map f as)
  ```

* Added new definitions to `Codata.Conat.Bisimilarity`:
  ```agda
  isEquivalence : IsEquivalence (i ⊢_≈_)
  setoid        : Size → Setoid 0ℓ 0ℓ
  module ≈-Reasoning
  ```

* Added new proof to `Codata.Conat.Properties`:
  ```agda
  0∸m≈0 : ∀ m → i ⊢ zero ∸ m ≈ zero
  ```

* Added new proofs to `Data.Bool`:
  ```agda
  not-injective : not x ≡ not y → x ≡ y
  ```

* Added new function to `Data.Difference.List`:
  ```agda
  _∷ʳ_ : DiffList A → A → DiffList A
  ```

* Added new properties to `Data.Fin.Properties`:
  ```agda
  lift-injective        : (∀ {x y} → f x ≡ f y → x ≡ y) → ∀ k {x y} → lift k f x ≡ lift k f y → x ≡ y
  inject+-raise-splitAt : [ inject+ n , raise {n} m ] (splitAt m i) ≡ i
  ```

* Added new properties to `Data.Fin.Subset`:
  ```agda
  _⊂_ : Subset n → Subset n → Set
  _⊄_ : Subset n → Subset n → Set
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  s⊆s           : p ⊆ q → s ∷ p ⊆ s ∷ q
  ∣p∣≡n⇒p≡⊤     : ∣ p ∣ ≡ n → p ≡ ⊤

  p∪∁p≡⊤        : p ∪ ∁ p ≡ ⊤
  ∣∁p∣≡n∸∣p∣    : ∣ ∁ p ∣ ≡ n ∸ ∣ p ∣
  x∈p⇒x∉∁p      : x ∈ p → x ∉ ∁ p
  x∈∁p⇒x∉p      : x ∈ ∁ p → x ∉ p
  x∉∁p⇒x∈p      : x ∉ ∁ p → x ∈ p
  x∉p⇒x∈∁p      : x ∉ p → x ∈ ∁ p

  x≢y⇒x∉⁅y⁆     : x ≢ y → x ∉ ⁅ y ⁆
  x∉⁅y⁆⇒x≢y     : x ∉ ⁅ y ⁆ → x ≢ y

  ∣p∩q∣≤∣p∣     : ∣ p ∩ q ∣ ≤ ∣ p ∣
  ∣p∩q∣≤∣q∣     : ∣ p ∩ q ∣ ≤ ∣ q ∣
  ∣p∩q∣≤∣p∣⊓∣q∣ : ∣ p ∩ q ∣ ≤ ∣ p ∣ ⊓ ∣ q ∣
  ∣p∣≤∣p∪q∣     : ∣ p ∣ ≤ ∣ p ∪ q ∣
  ∣q∣≤∣p∪q∣     : ∣ q ∣ ≤ ∣ p ∪ q ∣
  ∣p∣⊔∣q∣≤∣p∪q∣ : ∣ p ∣ ⊔ ∣ q ∣ ≤ ∣ p ∪ q ∣
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  suc[i]≤j⇒i<j : sucℤ i ≤ j → i < j
  i<j⇒suc[i]≤j : i < j → sucℤ i ≤ j
  ```

* Added new functions to `Data.List`:
  ```agda
  derun       : B.Decidable R → List A → List A
  deduplicate : Decidable _R_ → List A → List A
  ```

* Added new proofs to `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  Any-resp-≋      : P Respects _≈_ → (Any P) Respects _≋_
  All-resp-≋      : P Respects _≈_ → (All P) Respects _≋_
  AllPairs-resp-≋ : R Respects₂ _≈_ → (AllPairs R) Respects _≋_
  Unique-resp-≋   : Unique Respects _≋_
  ```

* Added new functions to `Data.List.Base`:
  ```agda
  _?∷_  : Maybe A → List A → List A
  _∷ʳ?_ : List A → Maybe A → List A
  ```

* Added new proofs to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-derun⁺       : z ∈ xs → z ∈ derun R? xs
  ∈-deduplicate⁺ : z ∈ xs → z ∈ deduplicate _≟_ xs
  ∈-derun⁻       : z ∈ derun R? xs → z ∈ xs
  ∈-deduplicate⁻ : z ∈ deduplicate R? xs → z ∈ xs
  ```

* Added new proofs to `Data.List.Membership.Setoid.Properties`:
  ```agda
  ∈-derun⁺       : _≈_ Respectsʳ R → z ∈ xs → z ∈ derun R? xs
  ∈-deduplicate⁺ : _≈_ Respectsʳ (flip R) → z ∈ xs → z ∈ deduplicate R? xs
  ∈-derun⁻       : z ∈ derun R? xs → z ∈ xs
  ∈-deduplicate⁻ : z ∈ deduplicate R? xs → z ∈ xs
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  derun⁺       : All P xs → All P (derun Q? xs)
  deduplicate⁺ : All P xs → All P (deduplicate Q? xs)
  filter⁻      : All Q (filter P? xs) → All Q (filter (¬? ∘ P?) xs) → All Q xs
  derun⁻       : All P (derun Q? xs) → All P xs
  deduplicate⁻ : All P (deduplicate Q? xs) → All P xs
  ```

* Added new proofs to `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  lookup-result : (p : Any P xs) → P (lookup p)
  filter⁺       : (p : Any P xs) → Any P (filter Q? xs) ⊎ ¬ Q (Any.lookup p)
  derun⁺        : P Respects Q → Any P xs → Any P (derun Q? xs)
  deduplicate⁺  : P Respects (flip Q) → Any P xs → Any P (deduplicate Q? xs)
  filter⁻       : Any P (filter Q? xs) → Any P xs
  derun⁻        : Any P (derun Q? xs) → Any P xs
  deduplicate⁻  : Any P (deduplicate Q? xs) → Any P xs
  ```

* The implementation of `↭-trans` has been altered in 
  `Data.List.Relation.Binary.Permutation.Inductive` to avoid
  adding unnecessary `refl`s, hence improving it's performance.
  
* Added new functions to `Data.List.Relation.Binary.Permutation.Setoid`:
  ```agda
  ↭-prep : xs ↭ ys → x ∷ xs ↭ x ∷ ys
  ↭-swap : xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys

  steps  : xs ↭ ys → ℕ
  ```

* Added new combinators to `PermutationReasoning` in `Data.List.Relation.Binary.Permutation.Setoid`:
  ```agda
  _≋⟨_⟩_  : x ≋ y → y IsRelatedTo z → x IsRelatedTo z
  _≋˘⟨_⟩_ : y ≋ x → y IsRelatedTo z → x IsRelatedTo z
  ```

* Added new functions to ` Data.List.Relation.Binary.Permutation.Setoid.Properties`:
  ```agda
  0<steps              : (xs↭ys : xs ↭ ys) → 0 < steps xs↭ys
  steps-respˡ          : (ys≋xs : ys ≋ xs) (ys↭zs : ys ↭ zs) → steps (↭-respˡ-≋ ys≋xs ys↭zs) ≡ steps ys↭zs
  steps-respʳ          : (xs≋ys : xs ≋ ys) (zs↭xs : zs ↭ xs) → steps (↭-respʳ-≋ xs≋ys zs↭xs) ≡ steps zs↭xs

  split                : xs ↭ as ++ [ v ] ++ bs → ∃₂ λ ps qs → xs ≋ ps ++ [ v ] ++ qs
  dropMiddle           : ws ++ vs ++ ys ↭ xs ++ vs ++ zs → ws ++ ys ↭ xs ++ zs
  dropMiddleElement    : ws ++ [ v ] ++ ys ↭ xs ++ [ v ] ++ zs → ws ++ ys ↭ xs ++ zs
  dropMiddleElement-≋  : ws ++ [ v ] ++ ys ≋ xs ++ [ v ] ++ zs → ws ++ ys ↭ xs ++ zs

  filter⁺              : xs ↭ ys → filter P? xs ↭ filter P? ys
  ```

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  Any-resp-Pointwise      : P Respects _∼_  → (Any P) Respects (Pointwise _∼_)
  All-resp-Pointwise      : P Respects _∼_  → (All P) Respects (Pointwise _∼_)
  AllPairs-resp-Pointwise : R Respects₂ _∼_ → (AllPairs R) Respects (Pointwise _∼_)
  ```

* Added new proofs to `Data.Maybe.Properties`:
  ```agda
  map-nothing : ma ≡ nothing → map f ma ≡ nothing
  map-just    : ma ≡ just a → map f ma ≡ just (f a)
  ```

* Added new proofs to `Data.Nat.DivMod`:
  ```agda
  %-distribˡ-* : (m * n) % d ≡ ((m % d) * (n % d)) % d
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  m<n+m         : n > 0 → m < n + m
  ∸-cancelʳ-≡   : o ≤ m → o ≤ n → m ∸ o ≡ n ∸ o → m ≡ n
  
  ⌊n/2⌋+⌈n/2⌉≡n : ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
  ⌊n/2⌋≤n       : ⌊ n /2⌋ ≤ n
  ⌊n/2⌋<n       : ⌊ suc n /2⌋ < suc n
  ⌈n/2⌉≤n       : ⌈ n /2⌉ ≤ n
  ⌈n/2⌉<n       : ⌈ suc (suc n) /2⌉ < suc (suc n)
  ⌊n/2⌋≤⌈n/2⌉   : ⌊ n /2⌋ ≤ ⌈ n /2⌉
  
  ⊔-pres-≤m     : n ≤ m → o ≤ m → n ⊔ o ≤ m
  ⊔-pres-<m     : n < m → o < m → n ⊔ o < m
  ⊓-pres-m≤     : m ≤ n → m ≤ o → m ≤ n ⊓ o
  ⊓-pres-m<     : m < n → m < o → m < n ⊓ o
  
  *-isCommutativeSemigroup : IsCommutativeSemigroup _*_
  *-commutativeSemigroup   : CommutativeSemigroup 0ℓ 0ℓ
  ```

* Added new data and functions to `Data.String.Base`:
  ```agda
  data Alignment : Set
  fromAlignment  : Alignment → ℕ → String → String

  parens         : String → String
  parensIfSpace  : String → String
  braces         : String → String
  intersperse    : String → List String → String
  unwords        : List String → String
  _<+>_          : String → String → String
  padLeft        : Char → ℕ → String → String
  padRight       : Char → ℕ → String → String
  padBoth        : Char → Char → ℕ → String → String

  rectangle      : Vec (ℕ → String → String) n → Vec String n → Vec String n
  rectangleˡ     : Char → Vec String n → Vec String n
  rectangleʳ     : Char → Vec String n → Vec String n
  rectangleᶜ     : Char → Char → Vec String n → Vec String n
  ```

* Added new proofs to `Data.String.Unsafe`:
  ```agda
  toList-++        : toList (s ++ t) ≡ toList s ++ toList t
  length-++        : length (s ++ t) ≡ length s + length t
  length-replicate : length (replicate n c) ≡ n
  ```

* Added new proof to `Data.Sum.Properties`:
  ```agda
  [,]-∘-distr     : f ∘ [ g , h ] ≗ [ f ∘ g , f ∘ h ]
  [,]-map-commute : [ f′ , g′ ] ∘ (map f g) ≗ [ f′ ∘ f , g′ ∘ g ]
  map-commute     : ((map f′ g′) ∘ (map f g)) ≗ map (f′ ∘ f) (g′ ∘ g)
  ```

* Improved the universe polymorphism of 
  `Data.Product.Relation.Binary.Lex.Strict/NonStrict`
  so that the equality and order relations need not live at the
  same universe level.

* Added new proofs to `Data.Product.Relation.Binary.Lex.Strict`:
  ```
  ×-wellFounded : WellFounded _<₁_ → WellFounded _<₂_ → WellFounded _<ₗₑₓ_
  ```

* Added new proofs to `Data.Rational.Properties`:
  ```agda
  ↥-* : ↥ (p * q) ℤ.* *-nf p q ≡ ↥ p ℤ.* ↥ q
  ↧-* : ↧ (p * q) ℤ.* *-nf p q ≡ ↧ p ℤ.* ↧ q

  toℚᵘ-homo-*                 : Homomorphic₂ toℚᵘ _*_ ℚᵘ._*_
  toℚᵘ-isMagmaHomomorphism-*  : IsMagmaHomomorphism *-rawMagma ℚᵘ.*-rawMagma toℚᵘ
  toℚᵘ-isMonoidHomomorphism-* : IsMonoidHomomorphism *-rawMonoid ℚᵘ.*-rawMonoid toℚᵘ
  toℚᵘ-isMonoidMonomorphism-* : IsMonoidMonomorphism *-rawMonoid ℚᵘ.*-rawMonoid toℚᵘ
  toℚᵘ-homo‿-                 : Homomorphic₁ toℚᵘ (-_) (ℚᵘ.-_)
  toℚᵘ-isGroupHomomorphism-+  : IsGroupHomomorphism +-0-rawGroup ℚᵘ.+-0-rawGroup toℚᵘ
  toℚᵘ-isGroupMonomorphism-+  : IsGroupMonomorphism +-0-rawGroup ℚᵘ.+-0-rawGroup toℚᵘ
  toℚᵘ-isRingHomomorphism-|-* : IsRingHomomorphism +-*-rawRing ℚᵘ.+-*-rawRing toℚᵘ
  toℚᵘ-isRingMonomorphism-|-* : IsRingMonomorphism +-*-rawRing ℚᵘ.+-*-rawRing toℚᵘ

  *-assoc     : Associative _*_
  *-comm      : Commutative _*_
  *-identityˡ : LeftIdentity 1ℚ _*_
  *-identityʳ : RightIdentity 1ℚ _*_
  *-identity  : Identity 1ℚ _*_
  +-inverseˡ  : LeftInverse 0ℚ -_ _+_
  +-inverseʳ  : RightInverse 0ℚ -_ _+_
  +-inverse   : Inverse 0ℚ -_ _+_
  -‿cong      :  Congruent₁ (-_)
  
  *-isMagma               : IsMagma _*_
  *-isSemigroup           : IsSemigroup _*
  *-1-isMonoid            : IsMonoid _*_ 1ℚ
  *-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℚ
  *-rawMagma              : RawMagma 0ℓ 0ℓ
  *-rawMonoid             : RawMonoid 0ℓ 0ℓ
  +-0-rawGroup            : RawGroup 0ℓ 0ℓ
  +-*-rawRing             : RawRing 0ℓ 0ℓ
  +-0-isGroup             : IsGroup _+_ 0ℚ (-_)
  +-0-isAbelianGroup      : IsAbelianGroup _+_ 0ℚ (-_)
  +-0-isRing              : IsRing _+_ _*_ -_ 0ℚ 1ℚ
  +-0-group               : Group 0ℓ 0ℓ
  +-0-abelianGroup        : AbelianGroup 0ℓ 0ℓ
  *-distribˡ-+            : _*_ DistributesOverˡ _+_
  *-distribʳ-+            : _*_ DistributesOverʳ _+_
  *-distrib-+             : _*_ DistributesOver _+_
  *-magma                 : Magma 0ℓ 0ℓ
  *-semigroup             : Semigroup 0ℓ 0ℓ
  *-1-monoid              : Monoid 0ℓ 0ℓ
  *-1-commutativeMonoid   : CommutativeMonoid 0ℓ 0ℓ
  +-*-isRing              : IsRing _+_ _*_ -_ 0ℚ 1ℚ
  +-*-ring                : Ring 0ℓ 0ℓ
  ```

* Added new proofs to `Data.Rational.Unnormalised.Properties`:
  ```agda
  +-inverseˡ            : LeftInverse _≃_ 0ℚᵘ -_ _+_
  +-inverseʳ            : RightInverse _≃_ 0ℚᵘ -_ _+_
  +-inverse             : Inverse _≃_ 0ℚᵘ -_ _+_
  -‿cong                : Congruent₁ _≃_ (-_)
  +-0-isGroup           : IsGroup _≃_ _+_ 0ℚᵘ (-_)
  +-0-group             : Group 0ℓ 0ℓ
  +-0-isAbelianGroup    : IsAbelianGroup _≃_ _+_ 0ℚᵘ (-_)
  +-0-abelianGroup      : AbelianGroup 0ℓ 0ℓ
  *-zeroˡ               : LeftZero _≃_ 0ℚᵘ _*_
  *-zeroʳ               : RightZero _≃_ 0ℚᵘ _*_
  *-zero                : Zero _≃_ 0ℚᵘ _*_
  *-distribˡ-+          : _DistributesOverˡ_ _≃_ _*_ _+_
  *-distribʳ-+          : _DistributesOverʳ_ _≃_ _*_ _+_
  *-distrib-+           : _DistributesOver_ _≃_ _*_ _+_
  +-*-isRing            : IsRing _≃_ _+_ _*_ -_ 0ℚᵘ 1ℚ 
  +-*-ring              : Ring 0ℓ 0ℓ
  +-0-rawGroup          : RawGroup 0ℓ 0ℓ
  +-*-rawRing           : RawRing 0ℓ 0ℓ
  +-*-isCommutativeRing : IsCommutativeRing _≃_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
  +-*-commutativeRing   : CommutativeRing 0ℓ 0ℓ
  ```

* Added new functions to `Data.Vec.Base`:
  ```agda
  uncons    : Vec A (suc n) → A × Vec A n
  length    : Vec A n → ℕ
  transpose : Vec (Vec A n) m → Vec (Vec A m) n
  ```

* Added new functions to `Data.Vec.Bounded.Base`:
  ```agda
  take : n → Vec≤ A m → Vec≤ A (n ⊓ m)
  drop : n → Vec≤ A m → Vec≤ A (m ∸ n)

  padLeft   : A → Vec≤ A n → Vec A n
  padRight  : A → Vec≤ A n → Vec A n
  padBoth : ∀ {n} → A → A → Vec≤ A n → Vec A n

  rectangle : List (∃ (Vec≤ A)) → ∃ (List ∘ Vec≤ A)
  ```

* Added new definitions to `Data.Word.Base`:
  ```agda
  _≈_ : Rel Word64 zero
  _<_ : Rel Word64 zero
  ```

* Added utility function to `Function.Base`:
  ```agda
  it : {A : Set a} → {{A}} → A
  ```

* Added new definitions to `Function.Bundles`:
  ```agda
  record BiInverse
  record BiEquivalence
  
  _↩↪_ : Set a → Set b → Set _
  mk↩↪ : Inverseˡ f g₁ → Inverseʳ f g₂ → A ↩↪ B
  ```

* Added new definitions to `Function.Structures`:
  ```agda
  record IsBiEquivalence (f : A → B) (g₁ : B → A) (g₂ : B → A)
  record IsBiInverse     (f : A → B) (g₁ : B → A) (g₂ : B → A)
  ```

* Added new proofs to `Induction.WellFounded`:
  ```agda
  Acc-resp-≈            : Symmetric _≈_ → _<_ Respectsʳ _≈_ → (Acc _<_) Respects _≈_
  some-wfRec-irrelevant : Some.wfRec P f x q ≡ Some.wfRec P f x q'
  wfRecBuilder-wfRec    : All.wfRecBuilder P f x y y<x ≡ All.wfRec P f y
  unfold-wfRec          : All.wfRec P f x ≡ f x λ y _ → All.wfRec P f y
  ```

* Added new definition in `Relation.Binary.Core`:
  ```agda
  DecidableEquality A = Decidable {A = A} _≡_
  ```

* Added new proofs to `Relation.Binary.Construct.Union`:
  ```agda
  respˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∪ R) Respectsˡ ≈
  respʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∪ R) Respectsʳ ≈
  resp₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∪ R) Respects₂ ≈
  ```

* Added new proof to `Relation.Binary.Setoid.Properties`:
  ```agda
  ≉-resp₂ : _≉_ Respects₂ _≈_
  ```

* Added a new proof to `Relation.Nullary.Decidable`:
  ```agda
  isYes≗does : (P? : Dec P) → isYes P? ≡ does P?
  ```
