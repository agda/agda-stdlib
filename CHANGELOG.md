Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

* First instance modules

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

* The module `Induction.WellFounded.InverseImage` has been deprecated. The proofs
  `accessible` and `wellFounded` have been moved to `Relation.Binary.Construct.On`.

* `Reflection.TypeChecking.MonadSyntax` ↦ `Reflection.TypeChecking.Monad.Syntax`

Deprecated names
----------------

Other major additions
---------------------

* Instance modules:
  ```agda
  Category.Monad.Partiality.Instances
  Codata.Stream.Instances
  Codata.Covec.Instances
  Data.List.Instances
  Data.List.NonEmpty.Instances
  Data.Maybe.Instances
  Data.Vec.Instances
  Function.Identity.Instances
  ```

* Symmetric transitive closures of binary relations:
  ```
  Relation.Binary.Construct.Closure.SymmetricTransitive
  ```

* Type-checking monads
  ```
  Reflection.TypeChecking.Monad
  Reflection.TypeChecking.Monad.Categorical
  Reflection.TypeChecking.Monad.Instances
  ```

Other major changes
-------------------

Other minor additions
---------------------

* The module `Data.Nat.Bin.Induction` now re-exports `Acc` and `acc`.

* Added proofs to `Relation.Binary.PropositionalEquality`:
  ```agda
  trans-cong  : trans (cong f p) (cong f q) ≡ cong f (trans p q)
  cong₂-reflˡ : cong₂ _∙_ refl p ≡ cong (x ∙_) p
  cong₂-reflʳ : cong₂ _∙_ p refl ≡ cong (_∙ u) p
  ```

* Made first argument of `[,]-∘-distr` in `Data.Sum.Properties` explicit

* Added new functions to `Data.List.Base`:
  ```agda
  cartesianProductWith : (A → B → C) → List A → List B → List C
  cartesianProduct     : List A → List B → List (A × B)
  ```

* Added new proofs to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-cartesianProductWith⁺ : a ∈ xs → b ∈ ys → f a b ∈ cartesianProductWith f xs ys
  ∈-cartesianProductWith⁻ : v ∈ cartesianProductWith f xs ys → ∃₂ λ a b → a ∈ xs × b ∈ ys × v ≡ f a b
  ∈-cartesianProduct⁺     : x ∈ xs → y ∈ ys → (x , y) ∈ cartesianProduct xs ys
  ∈-cartesianProduct⁻     : ∀ xs ys {xy@(x , y) : A × B} → xy ∈ cartesianProduct xs ys → x ∈ xs × y ∈ ys
  ```

* Added new proofs to `Data.List.Membership.Setoid.Properties`:
  ```agda
  ∈-cartesianProductWith⁺ : a ∈₁ xs → b ∈₂ ys → f a b ∈₃ cartesianProductWith f xs ys
  ∈-cartesianProductWith⁻ : v ∈₃ cartesianProductWith f xs ys → ∃₂ λ a b → a ∈₁ xs × b ∈₂ ys × v ≈₃ f a b
  ∈-cartesianProduct⁺     : x ∈₁ xs → y ∈₂ ys → (x , y) ∈₁₂ cartesianProduct xs ys
  ∈-cartesianProduct⁻     : (x , y) ∈₁₂ cartesianProduct xs ys → x ∈₁ xs
  ```

* Added new operations to `Data.List.Relation.Unary.All`:
  ```agda
  tabulateₛ : (S : Setoid a ℓ) → ∀ {xs} → (∀ {x} → x ∈ xs → P x) → All P xs
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (f x y)) → All P (cartesianProductWith f xs ys)
  cartesianProduct⁺     : (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x , y)) → All P (cartesianProduct xs ys)
  ```

* Added new proofs to `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {x y} → P x → Q y → R (f x y)) → Any P xs → Any Q ys → Any R (cartesianProductWith f xs ys)
  cartesianProductWith⁻ : (∀ {x y} → R (f x y) → P x × Q y) → Any R (cartesianProductWith f xs ys) → Any P xs × Any Q ys
  cartesianProduct⁺     : Any P xs → Any Q ys → Any (P ⟨×⟩ Q) (cartesianProduct xs ys)
  cartesianProduct⁻     : Any (P ⟨×⟩ Q) (cartesianProduct xs ys) → Any P xs × Any Q ys
  ```

* Added new proofs to `Data.List.Relation.Unary.Unique.Propositional.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {w x y z} → f w y ≡ f x z → w ≡ x × y ≡ z) → Unique xs → Unique ys → Unique (cartesianProductWith f xs ys)
  cartesianProduct⁺     : Unique xs → Unique ys → Unique (cartesianProduct xs ys)
  ```

* Added new proofs to `Data.List.Relation.Unary.Unique.Setoid.Properties`:
  ```agda
  cartesianProductWith⁺ : (∀ {w x y z} → f w y ≈₃ f x z → w ≈₁ x × y ≈₂ z) → Unique S xs → Unique T ys → Unique U (cartesianProductWith f xs ys)
  cartesianProduct⁺     : Unique S xs → Unique T ys → Unique (S ×ₛ T) (cartesianProduct xs ys)
  ```

* Added new proofs to ` Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  ↭-empty-inv     : xs ↭ [] → xs ≡ []
  ¬x∷xs↭[]        : ¬ (x ∷ xs ↭ [])
  ↭-singleton-inv : xs ↭ [ x ] → xs ≡ [ x ]
  ↭-map-inv       : map f xs ↭ ys → ∃ λ ys′ → ys ≡ map f ys′ × xs ↭ ys′
  ↭-length        : xs ↭ ys → length xs ≡ length ys
  ```

* Added new proofs to `Data.Sum.Properties`:
  ```agda
  map-id        : map id id ≗ id
  map₁₂-commute : map₁ f ∘ map₂ g ≗ map₂ g ∘ map₁ f
  [,]-cong      : f ≗ f′ → g ≗ g′ → [ f , g ] ≗ [ f′ , g′ ]
  [-,]-cong     : f ≗ f′ → [ f , g ] ≗ [ f′ , g ]
  [,-]-cong     : g ≗ g′ → [ f , g ] ≗ [ f , g′ ]
  map-cong      : f ≗ f′ → g ≗ g′ → map f g ≗ map f′ g′
  map₁-cong     : f ≗ f′ → map₁ f ≗ map₁ f′
  map₂-cong     : g ≗ g′ → map₂ g ≗ map₂ g′
  ```

* Added new proofs to `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  nothing-inv : Pointwise R nothing x → x ≡ nothing
  just-inv    : Pointwise R (just x) y → ∃ λ z → y ≡ just z × R x z
  ```
