Version 1.0
===========

The library has been tested using Agda version 2.6.0.

Important changes since 0.17:

Highlights
----------

* The library has been refactored to make clear where axiom K is used and
  where it is not. Hence it can now be used in conjunction with the
  `--without-k` option.

* Equational and inequality reasoning has been revamped. Several new
  primitives have been added and the inequality reasoning modules can now
  prove equalities and strict inequalities in addition to basic inequalities.

* AVL trees now work with arbitrary equalities rather than only propositional
  equality.

* New top level `Axiom` directory which contains statements of various
  additional axioms such as excluded middle and function extensionality which
  users may want to postulate.

* The proofs `_≟_` of decidable equality for `String`s and `Char`s have been
  made safe.

New modules
-----------

* The following list contains all the new modules that have been added in v1.0:
  ```
  Algebra.Construct.NaturalChoice.Min
  Algebra.Construct.NaturalChoice.Max
  Algebra.Properties.Semilattice
  Algebra.FunctionProperties.Consequences.Propositional

  Axiom.UniquenessOfIdentityProofs
  Axiom.UniquenessOfIdentityProofs.WithK
  Axiom.ExcludedMiddle
  Axiom.DoubleNegationElimination
  Axiom.Extensionality.Propositional
  Axiom.Extensionality.Heterogeneous

  Codata.Cowriter
  Codata.M.Properties
  Codata.M.Bisimilarity

  Data.Container.Combinator.Properties
  Data.Container.Membership
  Data.Container.Morphism
  Data.Container.Morphism.Properties
  Data.Container.Properties
  Data.Container.Related
  Data.Container.Relation.Unary.All
  Data.Container.Relation.Unary.Any
  Data.Container.Relation.Unary.Any.Properties
  Data.Container.Relation.Binary.Equality.Setoid
  Data.Container.Relation.Binary.Pointwise
  Data.Container.Relation.Binary.Pointwise.Properties

  Data.Char.Properties

  Data.Integer.Divisibility.Properties
  Data.Integer.Divisibility.Signed
  Data.Integer.DivMod

  Data.List.Relation.Unary.First
  Data.List.Relation.Unary.First.Properties

  Data.List.Relation.Binary.Suffix.Heterogeneous
  Data.List.Relation.Binary.Suffix.Heterogeneous.Properties
  Data.List.Relation.Binary.Prefix.Heterogeneous
  Data.List.Relation.Binary.Prefix.Heterogeneous.Properties
  Data.List.Relation.Binary.Sublist.Homogeneous.Properties
  Data.List.Relation.Binary.Sublist.Homogeneous.Solver
  Data.List.Relation.Binary.Sublist.Heterogeneous
  Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  Data.List.Relation.Binary.Sublist.Setoid
  Data.List.Relation.Binary.Sublist.Setoid.Properties
  Data.List.Relation.Binary.Sublist.DecSetoid
  Data.List.Relation.Binary.Sublist.DecSetoid.Properties
  Data.List.Relation.Binary.Sublist.DecSetoid.Solver
  Data.List.Relation.Binary.Sublist.Propositional
  Data.List.Relation.Binary.Sublist.Propositional.Properties
  Data.List.Relation.Binary.Sublist.DecPropositional
  Data.List.Relation.Binary.Sublist.DecPropositional.Properties
  Data.List.Relation.Binary.Sublist.DecPropositional.Solver
  Data.List.Relation.Ternary.Interleaving.Setoid
  Data.List.Relation.Ternary.Interleaving.Setoid.Properties
  Data.List.Relation.Ternary.Interleaving.Propositional
  Data.List.Relation.Ternary.Interleaving.Propositional.Properties

  Data.Maybe.Relation.Unary.All.Properties

  Data.String.Properties

  Data.These.Properties

  Data.Vec.Any.Properties
  Data.Vec.Membership.Setoid
  Data.Vec.Membership.DecSetoid
  Data.Vec.Membership.DecPropositional
  Data.Vec.Relation.Unary.Any.Properties

  Debug.Trace

  Function.Endomophism.Setoid
  Function.Endomophism.Propositional
  Function.HalfAdjointEquivalence

  Relation.Binary.Construct.Add.Extrema.Equality
  Relation.Binary.Construct.Add.Extrema.Strict
  Relation.Binary.Construct.Add.Extrema.NonStrict
  Relation.Binary.Construct.Add.Infimum.Equality
  Relation.Binary.Construct.Add.Infimum.Strict
  Relation.Binary.Construct.Add.Infimum.NonStrict
  Relation.Binary.Construct.Add.Supremum.Equality
  Relation.Binary.Construct.Add.Supremum.Strict
  Relation.Binary.Construct.Add.Supremum.NonStrict
  Relation.Binary.Construct.Add.Point.Equality
  Relation.Binary.Construct.Intersection
  Relation.Binary.Construct.Union
  Relation.Binary.Construct.NaturalOrder.Left
  Relation.Binary.Construct.NaturalOrder.Right
  Relation.Binary.Properties.BoundedLattice

  Relation.Nullary.Construct.Add.Extrema
  Relation.Nullary.Construct.Add.Infimum
  Relation.Nullary.Construct.Add.Supremum
  Relation.Nullary.Construct.Add.Point
  ```

Non-backwards compatible changes
--------------------------------

#### Extending the relation hierarchy for container datatypes

* This release has added many new relations over `List` (e.g. `First`,
  `Suffix`, `Prefix`, `Interleaving`) and it has become clear that the
  current hierarchy for relations in `List`,`Product`,`Sum`, `Table`
  and `Vec`is not deep enough.

* To address this, the contents of `Data.X.Relation` have been moved to
  `Data.X.Relation.Binary` and new folders `Data.X.Relation.(Unary/Ternary)`
  have been created. `Data.X.(All/Any)` have been moved to
  `Data.X.Relation.Unary.(All/Any)`.

* The old modules still exist for backwards compatability but are deprecated.

#### Support for `--without-K`

* The `--without-K` flag has been enabled in as many files as possible. An
  attempt has been made to only do this in files that do not depend on
  any file in which this flag is not enabled.

* Agda uses different rules for the target universe of data types when
  the `--without-K` flag is used, and because of this a number of type
  families now target a possibly larger universe:
  - Codata.Delay.Bisimilarity                 : `Bisim`
  - Codata.Musical.Covec                      : `_≈_`, `_∈_`, `_⊑_`
  - Codata.Stream.Bisimilarity                : `Bisim`
  - Data.List.Relation.Binary.Equality.Setoid : `_≋_`
  - Data.List.Relation.Binary.Lex.NonStrict   : `Lex-<`, `Lex-≤`
  - Data.List.Relation.Binary.Lex.Strict      : `Lex-<`, `Lex-≤`
  - Data.List.Relation.Binary.Pointwise       : `Pointwise`
  - Data.List.Relation.Unary.All              : `All`
  - Data.Maybe                                : `Is-just`, `Is-nothing`
  - Data.Maybe.Relation.Unary.Any             : `Any`
  - Data.Maybe.Relation.Unary.All             : `All`
  - Data.Maybe.Relation.Binary.Pointwise      : `Pointwise`

* Because of this change the texts of some type signatures were changed
  (some inferred parts of other type signatures may also have changed):
  - Data.List.Relation.Binary.Equality.DecSetoid : `≋-decSetoid`
  - Data.Maybe.Relation.Binary.Pointwise         : `setoid`, `decSetoid`

* Some code that relies on the K rule or uses heterogeneous equality has
  been moved from the existing file `X` to a new file `X.WithK` file
  (e.g. from `Data.AVL.Indexed` to `Data.AVL.Indexed.WithK`). These are as follows:
  - `Data.AVL.Indexed`                                                 : `node-injective-bal, node-injectiveʳ, node-injectiveˡ`
  - `Data.Container.Indexed`                                           : `Eq, Map.composition, Map.identity, PlainMorphism.NT, PlainMorphism.Natural, PlainMorphism.complete, PlainMorphism.natural, PlainMorphism.∘-correct, setoid, _∈_`
  - `Data.Product.Properties`                                          : `,-injectiveʳ`
  - `Data.Product.Relation.Binary.Pointwise.Dependent`                 : `Pointwise-≡⇒≡, ≡⇒Pointwise-≡, inverse, ↣`
  - `Data.Vec.Properties`                                              : `++-assoc, []=-irrelevance, foldl-cong, foldr-cong`
  - `Data.Vec.Relation.Binary.Equality.Propositional`                  : `≋⇒≅`
  - `Data.W`                                                           : `sup-injective₂`
  - `Relation.Binary.Construct.Closure.Transitive`                     : `∼⁺⟨⟩-injectiveʳ, ∼⁺⟨⟩-injectiveˡ`
  - `Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties` : `◅-injectiveʳ, ◅-injectiveˡ`
  - `Relation.Binary.PropositionalEquality`                            : `≡-irrelevance`
  (The name `↣` in `Data.Product.Relation.Binary.Pointwise.Dependent` now refers to a new
  definition with another type signature.)

* Other code has been changed to avoid use of the K rule. As part of
  such changes the texts of the following type signatures have been
  changed:
  - `Data.AVL.Indexed`                                           : `node-injective-key`
  - `Data.List.Relation.Binary.Sublist.Propositional.Properties` : `∷⁻`
  - `Data.Product.Relation.Binary.Pointwise.Dependent`           : `↣`
  - `Relation.Binary.PropositionalEquality`                      : `≡-≟-identity`
  (The old definition of `↣` was moved to `Data.Product.Relation.Binary.Pointwise.Dependent.WithK`.)

* The definition `_≅⟨_⟩_` has been removed from `Relation.Binary.PropositionalEquality`.

* The following previously deprecated names have also been removed:
  - `Data.Product.Relation.Binary.Pointwise.Dependent` : `Rel↔≡`
  - `Data.Vec.Properties`                              : `proof-irrelevance-[]=`
  - `Relation.Binary.PropositionalEquality`            : `proof-irrelevance`

#### Changes to the algebra hierarchy

* Over time the algebra inheritance hierarchy has become a tangled
  due to poorly structured additions. The following changes attempt
  to straighten the hierarchy out and new policies have been put in
  place so that the  need for additional such changes will be minimised
  in the future.

* Added `Magma` and `IsMagma` to the algebra hierarchy.

* The name `RawSemigroup` in `Algebra` has been deprecated in favour
  of `RawMagma`.

* The fields `isEquivalence` and `∙-cong` in `IsSemigroup` have been
  replaced with `isMagma`.

* The field `∙-cong` in `IsSemilattice`/`Semilattice` has been renamed
  `∧-cong`.

* The record `BooleanAlgebra` now exports `∨-isSemigroup`, `∧-isSemigroup`
  directly so `Algebra.Properties.BooleanAlgebra` no longer does so.

* The proof that every algebraic lattice induces a partial order has been
  moved from `Algebra.Properties.Lattice` to
  `Algebra.Properties.Semilattice`.  The corresponding `poset` instance is
  re-exported in `Algebra.Properties.Lattice`.

* All algebraic structures now export left and right congruence properties.
  For example this means `∙-cong refl x≈y` can be replaced with `∙-congˡ y≈z`

#### Upgrade of equational and inequality reasoning

* The core Reasoning modules have been renamed as follows:
  ```
  Relation.Binary.EqReasoning                 ↦ Relation.Binary.Reasoning.Setoid
  Relation.Binary.SetoidReasoning             ↦ Relation.Binary.Reasoning.MultiSetoid
  Relation.Binary.PreorderReasoning           ↦ Relation.Binary.Reasoning.Preorder
  Relation.Binary.PartialOrderReasoning       ↦ Relation.Binary.Reasoning.PartialOrder
  Relation.Binary.StrictPartialOrderReasoning ↦ Relation.Binary.Reasoning.StrictPartialOrder
  ```
  The old modules have been deprecated but still exist for backwards compatibility reasons.

* The way reasoning is implemented has been changed. In particular all of the above
  modules are specialised instances of the three modules
  `Relation.Binary.Reasoning.Base.(Single/Double/Triple)`. This means that if you have
  extended the reasoning modules yourself you may need to update the extensions.
  However all *uses* of the reasoning modules are fully backwards compatible.

* The new implementation allows the interleaving of both strict and non-strict links
  in proofs. For example where as before the following:
  ```agda
  begin
    a  ≤⟨ x≤y ⟩
    b  <⟨ y<z ⟩
    c  ≤⟨ x≤y ⟩
    d  ∎
  ```
  was not a valid proof that `a ≤ d` due to the `<` link in the middle, it is now accepted.

* The new implementation can now be used to prove both equalities and strict inequalities as
  well as basic inequalities. To do so use the new `begin-equality` and `begin-strict` combinators.
  For instance replacing `begin` with `begin-strict` in the example above:
  ```agda
  begin-strict
    a  ≤⟨ x≤y ⟩
    b  <⟨ y<z ⟩
    c  ≤⟨ x≤y ⟩
    d  ∎
  ```
  proves that `a < d` rather than `a ≤ d`.

* New symmetric equality combinators  `_≈˘⟨_⟩_` and `_≡˘⟨_⟩_` have been added. Consequently
  expressions of the form `x ≈⟨ sym y≈x ⟩ y` can be replaced with `x ≈˘⟨ y≈x ⟩ y`.

#### New `Axiom` modules

* A new top level `Axiom` directory has been created that contains modules
  for various additional axioms that users may want to postulate.

* `Excluded-Middle` and associated proofs have been moved out of `Relation.Nullary.Negation`
  and into `Axiom.ExcludedMiddle`.

* `Extensionality` and associated proofs have been moved out of
  `Relation.Binary.PropositionalEquality` and into `Axiom.Extensionality.Propositional`.

* `Extensionality` and associated proofs have been moved out of
  `Relation.Binary.HeterogeneousEquality` and into `Axiom.Extensionality.Heterogeneous`.

* The old names still exist for backwards compatability but have been deprecated.

* Changed the type of `≡-≟-identity` in `Relation.Binary.PropositionalEquality`
  to make use of the fact that equality being decidable implies uniqueness of identity proofs.

#### Relaxation of ring solvers requirements

* In the ring solvers the assumption that equality is `Decidable`
  has been replaced by a strictly weaker assumption that it is `WeaklyDecidable`.
  This allows the solvers to be used when equality is not fully decidable.
  ```
  Algebra.Solver.Ring
  Algebra.Solver.Ring.NaturalCoefficients
  ```

* Created a module `Algebra.Solver.Ring.NaturalCoefficients.Default` that
  instantiates the solver for any `CommutativeSemiring`.

#### New `Data.Sum/Product.Function` directories

* Various combinators for types of functions (injections, surjections, inverses etc.)
  over `Sum` and `Product` currently live in the `Data.(Product/Sum).Relation.Binary.Pointwise`
  modules. These are poorly placed as the properties a) do not directly reference `Pointwise`
  and b) are very hard to locate.

* They have therefore been moved into the new `Data.(Product/Sum).Function` directory
  as follows:
  ```
  Data.Product.Relation.Binary.Pointwise.Dependent    ↦ Data.Product.Function.Dependent.Setoid
                                                      ↘ Data.Product.Function.Dependent.Propositional
  Data.Product.Relation.Binary.Pointwise.NonDependent ↦ Data.Product.Function.NonDependent.Setoid
                                                      ↘ Data.Product.Function.NonDependent.Propositional
  Data.Sum.Relation.Binary.Pointwise.Dependent        ↦ Data.Sum.Function.Setoid
                                                      ↘ Data.Sum.Function.Propositional
  ```
  All the proofs about `Pointwise` remain untouched.

#### Overhaul of `Data.AVL`

* AVL trees now work over arbitrary equalities, rather than just
  propositional equality.

* Consequently the family of `Value`s stored in the tree now need
  to respect the `Key` equivalence

* The module parameter for `Data.AVL`, `Data.AVL.Indexed`, `Data.AVL.Key`,
  `Data.AVL.Sets` is now a `StrictTotalOrder` rather than a
  `IsStrictTotalOrder`, and the module parameter for `Data.AVL.Value` is
  now takes a `Setoid` rather than an `IsEquivalence`.

* It was noticed that `Data.AVL.Indexed`'s lookup & delete didn't use
  a range to guarantee that the recursive calls were performed in the
  right subtree. The types have been made more precise.

* The functions `(insert/union)With` now take a function of type
  `Maybe Val -> Val` rather than a value together with a merging function
  `Val -> Val -> Val` to handle the case where a value is already present
  at that key.

* Various functions have been made polymorphic which makes their biases
  & limitations clearer. e.g. we have:
  `unionWith : (V -> Maybe W -> W) -> Tree V -> Tree W -> Tree W`
  but ideally we would like to have:
  `unionWith : (These V W -> X) -> Tree V -> Tree W -> Tree X`

* Keys are now implemented via the new `Relation.(Binary/Nullary).Construct.AddExtrema`
  modules.

#### Overhaul of `Data.Container`

* `Data.Container` has been split up into the standard hierarchy.

* Moved `Data.Container`'s `All` and `Any` into their own
  `Data.Container.Relation.Unary.X` module. Made them record types
  to improve type inference.

* Moved morphisms to `Data.Container.Morphism` and their properties
  to `Data.Container.Morphism.Properties`.

* Made the index set explicit in `Data.Container.Combinator`'s `Π` and `Σ`.

* Moved `Eq` to `Data.Container.Relation.Binary.Pointwise`
  (and renamed it to `Pointwise`) and its properties to
  `Data.Container.Relation.Binary.Pointwise.Properties`.

* The type family `Data.Container.ν` is now defined using `Codata.M.M`
  rather than Codata.Musical.M.M`.

#### Overhaul of `Data.Maybe`

* `Data.Maybe` has been split up into the standard hierarchy for
  container datatypes.

* Moved `Data.Maybe.Base`'s `Is-just`, `Is-nothing`, `to-witness`,
  and `to-witness-T` to `Data.Maybe` (they rely on `All` and `Any`
  which are now outside of `Data.Maybe.Base`).

* Moved `Data.Maybe.Base`'s `All` and `Data.Maybe`'s `allDec` to
  `Data.Maybe.Relation.Unary.All` and renamed the proof `allDec` to `dec`.

* Moved `Data.Maybe.Base`'s `Any` and `Data.Maybe`'s `anyDec` to
  `Data.Maybe.Relation.Unary.Any` and renamed the proof `anyDec` to `dec`.

* Created `Data.Maybe.Properties` and moved `Data.Maybe.Base`'s `just-injective`
  into it and added new results.

* Moved `Data.Maybe`'s `Eq` to `Data.Maybe.Relation.Binary.Pointwise`, made the
  relation heterogeneously typed and renamed the following proofs:
  ```agda
  Eq                  ↦ Pointwise
  Eq-refl             ↦ refl
  Eq-sym              ↦ sym
  Eq-trans            ↦ trans
  Eq-dec              ↦ dec
  Eq-isEquivalence    ↦ isEquivalence
  Eq-isDecEquivalence ↦ isDecEquivalence
  ```

#### Overhaul of `Data.Sum.Relation.Binary`

* The implementations of `Data.Sum.Relation.Binary.(Pointwise/LeftOrder)` have been altered
  to bring them in line with implementations of similar orders for other datatypes.
  Namely they are no longer specialised instances of some `Core` module.

* The constructor `₁∼₂` for `LeftOrder` no longer takes an argument of type `⊤`.

* The constructor `₁∼₁` and `₂∼₂` in `Pointwise` have been renamed `inj₁` and `inj₂`
  respectively. The old names still exist but have been deprecated.

#### Overhaul of `MonadZero` and `MonadPlus`

* Introduce `RawIApplicativeZero` for an indexed applicative with a zero
  and `RawAlternative` for an indexed applicative with a zero and a sum.

* `RawIMonadZero` is now packing a `RawIApplicativeZero` rather than a `∅` directly

* Similarly `RawIMonadPlus` is defined in terms of `RawIAlternative` rather than
  directly packing a _∣_.

* Instances will be broken but usages should still work thanks to re-exports striving
  to maintain backwards compatibility.

#### Overhaul of `Data.Char` and `Data.String`

* Moved `setoid` and `strictTotalOrder` from `Data.(Char/String)` into the new
  module `Data.(Char/String).Properties`.

* Used the new builtins from `Agda.Builtin.(Char/String).Properties` to implement
  decidable equality (`_≟_`) in a safe manner. This has allowed `_≟_`,
  `decSetoid` and `_==_` to be moved from `Data.(Char/String).Unsafe` to
  `Data.(Char/String).Properties`.

####  Overhaul of `Data.Rational`

* Many new operators have been added to `Data.Rational` including
  addition, substraction, multiplication, inverse etc.

* The existing operator `_÷_` has been renamed `_/_` and is now more liberal
  as it now accepts non-coprime arguments (e.g. `+ 2 / 4`) which are then
  normalised.

* The old name `_÷_` has been repurposed to represent division between two
  rationals.

* The proofs `drop-*≤*`, `≃⇒≡` and `≡⇒≃` have been moved from `Data.Rational`
  to `Data.Rational.Properties`.


#### Changes in `Data.List`

* In `Data.List.Membership.Propositional.Properties`:
    - the `Set` argument has been made implicit in `∈-++⁺ˡ`, `∈-++⁺ʳ`, `∈-++⁻`, `∈-insert`, `∈-∃++`.
    - the `A → B` argument has been made explicit in `∈-map⁺`, `∈-map⁻`, `map-∈↔`.

* The module `Data.List.Relation.Binary.Sublist.Propositional.Solver` has been removed
  and replaced by `Data.List.Relation.Binary.Sublist.DecPropositional.Solver`.

* The functions `_∷=_` and `_─_` have been removed from `Data.List.Membership.Setoid`
  as they are subsumed by the more general versions now part of `Data.List.Any`.

#### Changes in `Data.Nat`

* Changed the implementation of `_≟_` and `_≤″?_` for natural numbers
  to use a (fast) boolean test. Compiled code that uses these should
  now run faster.

* Made the contents of the modules `Data.Nat.Unsafe` and `Data.Nat.DivMod.Unsafe`
  safe by using the new safe equality erasure primitive instead of the
  unsafe one defined in `Relation.Binary.PropositionalEquality.TrustMe`. As the
  safe erasure primitive requires the K axiom the two files are now named
  `Data.Nat.WithK` and `Data.Nat.DivMod.WithK`.

* Fixed a bug in `Data.Nat.Properties` where the type of `m⊓n≤m⊔n` was
  `∀ m n → m ⊔ n ≤ m ⊔ n`. The type has been corrected to `∀ m n → m ⊓ n ≤ m ⊔ n`.

#### Changes in `Data.Vec`

* The argument order for `lookup`, `insert` and `remove` in `Data.Vec` has been altered
  so that the `Vec` argument always come first, e.g. what was written as `lookup i v xs` is
  now `lookup xs i v`. The argument order for the corresponding proofs has also changed.
  This makes the operations more consistent with those in `Data.List`.

* The proofs `toList⁺` and `toList⁻` in `Data.Vec.Relation.Unary.All.Properties` have been swapped
  as they were the opposite way round to similar properties in the rest of the library.

#### Other changes

* The proof ``≢-sym`` added to Relation.Binary.PropositionalEquality.Core.

* The proofs ``n≢0⇒n>0`` and `m<m*n` (for 0<m, 1<n) added to Data.Nat.Properties.

* The proof ``[a/n]*n≤a``  added to Data.Nat.DivMod.

* A faster version for  Data.Nat.Show.show  is implemented.

* The proof `sel⇒idem` in `Algebra.FunctionProperties.Consequences` now
  only takes the equality relation as an argument instead of a full `Setoid`.

* The proof `_≟_` that equality is decidable for `Bool` has been moved
  from `Data.Bool.Base` to `Data.Bool.Properties`. Backwards compatibility
  has been (nearly completely) preserved by having `Data.Bool` publicly re-export `_≟_`.

* The type `Coprime` and proof `coprime-divisor` have been moved from
  `Data.Integer.Divisibility` to `Data.Integer.Coprimality`.

* The functions `fromMusical` and `toMusical` were moved from the `Codata` modules
  to the corresponding `Codata.Musical` modules.

Removed features
----------------

* The following modules that were deprecated in v0.14 and v0.15 have been removed.
  ```agda
  Data.Nat.Properties.Simple
  Data.Integer.Multiplication.Properties
  Data.Integer.Addition.Properties

  Relation.Binary.Sigma.Pointwise
  Relation.Binary.Sum
  Relation.Binary.List.NonStrictLex
  Relation.Binary.List.Pointwise
  Relation.Binary.List.StrictLex
  Relation.Binary.Product.NonStrictLex
  Relation.Binary.Product.Pointwise
  Relation.Binary.Product.StrictLex
  Relation.Binary.Vec.Pointwise
  ```

Deprecated features
-------------------

The following renaming has occurred as part of a drive to improve
consistency across the library. The old names still exist and therefore
all existing code should still work, however they have been deprecated
and use of the new names is encouraged. Although not anticipated any
time soon, they may eventually be removed in some future release of the library.

* In `Data.Bool.Properties`:
  ```agda
  T-irrelevance ↦ T-irrelevant
  ```

* In `Data.Fin.Properties`:
  ```agda
  ≤-irrelevance ↦ ≤-irrelevant
  <-irrelevance ↦ <-irrelevant
  ```

* In `Data.Integer.Properties`:
  ```agda
  ≰→>           ↦ ≰⇒>
  ≤-irrelevance ↦ ≤-irrelevant
  <-irrelevance ↦ <-irrelevant
  ```

* In `Data.List.Relation.Binary.Permutation.Inductive.Properties`:
  ```agda
  ↭⇒~bag ↦ ↭⇒∼bag
  ~bag⇒↭ ↦ ∼bag⇒↭
  ```
  (now typed with "\sim" rather than "~")

* In `Data.List.Relation.Binary.Pointwise`:
  ```agda
  decidable-≡   ↦ Data.List.Properties.≡-dec
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  filter⁺₁ ↦ all-filter
  filter⁺₂ ↦ filter⁺
  ```

* In `Data.Nat.Properties`:
  ```agda
  ≤-irrelevance ↦ ≤-irrelevant
  <-irrelevance ↦ <-irrelevant
  ```

* In `Data.Rational`:
  ```agda
  drop-*≤*
  ≃⇒≡
  ≡⇒≃
  ```
  (moved to `Data.Rational.Properties`)

* In `Data.Rational.Properties`:
  ```agda
  ≤-irrelevance ↦ ≤-irrelevant
  ```

* In `Data.Vec.Properties.WithK`:
  ```agda
  []=-irrelevance ↦ []=-irrelevant
  ```

* In `Relation.Binary.HeterogeneousEquality`:
  ```agda
  ≅-irrelevance                ↦ ≅-irrelevant
  ≅-heterogeneous-irrelevance  ↦ ≅-heterogeneous-irrelevant
  ≅-heterogeneous-irrelevanceˡ ↦ ≅-heterogeneous-irrelevantˡ
  ≅-heterogeneous-irrelevanceʳ ↦ ≅-heterogeneous-irrelevantʳ
  ```

* In `Induction.WellFounded`:
  ```agda
  module Inverse-image      ↦ InverseImage
  module Transitive-closure ↦ TransitiveClosure
  ```

* In `Relation.Binary.PropositionalEquality.WithK`:
  ```agda
  ≡-irrelevance ↦ ≡-irrelevant
  ```

Other minor additions
---------------------

* Added new records to `Algebra`:
  ```agda
  record RawMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Magma    c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new types to `Algebra.FunctionProperties`:
  ```agda
  LeftConical  e _∙_ = ∀ x y → (x ∙ y) ≈ e → x ≈ e
  RightConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → y ≈ e
  Conical e ∙        = LeftConical e ∙ × RightConical e ∙

  LeftCongruent  _∙_ = ∀ {x} → (_∙ x) Preserves _≈_ ⟶ _≈_
  RightCongruent _∙_ = ∀ {x} → (x ∙_) Preserves _≈_ ⟶ _≈_
  ```

* Added new proof to `Algebra.FunctionProperties.Consequences`:
  ```agda
  wlog : Commutative f → Total _R_ → (∀ a b → a R b → P (f a b)) → ∀ a b → P (f a b)
  ```

* Added new proofs to `Algebra.Properties.Lattice`:
  ```agda
  ∧-isSemilattice : IsSemilattice _≈_ _∧_
  ∧-semilattice   : Semilattice l₁ l₂
  ∨-isSemilattice : IsSemilattice _≈_ _∨_
  ∨-semilattice   : Semilattice l₁ l₂
  ```

* Added new operator to `Algebra.Solver.Ring`.
  ```agda
  _:×_
  ```

* Added new records to `Algebra.Structures`:
  ```agda
  record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  ```

* Added new proofs to `Category.Monad.State`:
  ```agda
  StateTIApplicative     : RawMonad     M → RawIApplicative     (IStateT S M)
  StateTIApplicativeZero : RawMonadZero M → RawIApplicativeZero (IStateT S M)
  StateTIAlternative     : RawMonadPlus M → RawIAlternative     (IStateT S M)
  ```

* Added new functions to `Codata.Colist`:
  ```agda
  fromCowriter : Cowriter W A i → Colist W i
  toCowriter   : Colist A i → Cowriter A ⊤ i
  [_]          : A → Colist A ∞
  chunksOf     : (n : ℕ) → Colist A ∞ → Cowriter (Vec A n) (BoundedVec A n) ∞
  ```

* Added new proofs to `Codata.Delay.Categorical`:
  ```agda
  Sequential.applicativeZero : RawApplicativeZero (λ A → Delay A i)
  Zippy.applicativeZero      : RawApplicativeZero (λ A → Delay A i)
  Zippy.alternative          : RawAlternative     (λ A → Delay A i)
  ```

* Added new functions to `Codata.Stream`:
  ```agda
  splitAt    : (n : ℕ) → Stream A ∞ → Vec A n × Stream A ∞
  drop       : ℕ → Stream A ∞ → Stream A ∞
  interleave : Stream A i → Thunk (Stream A) i → Stream A i
  chunksOf   : (n : ℕ) → Stream A ∞ → Stream (Vec A n) ∞
  ```

* Added new proofs to `Codata.Stream.Properties`:
  ```agda
  splitAt-map             : splitAt n (map f xs) ≡ map (map f) (map f) (splitAt n xs)
  lookup-iterate-identity : lookup n (iterate f a) ≡ fold a f n
  ```

* Added new proofs to `Data.Bool.Properties`:
  ```agda
  ∧-isMagma       : IsMagma _∧_
  ∨-isMagma       : IsMagma _∨_
  ∨-isBand        : IsBand _∨_
  ∨-isSemilattice : IsSemilattice _∨_
  ∧-isBand        : IsBand _∧_
  ∧-isSemilattice : IsSemilattice _∧_

  ∧-magma         : Magma 0ℓ 0ℓ
  ∨-magma         : Magma 0ℓ 0ℓ
  ∨-band          : Band 0ℓ 0ℓ
  ∧-band          : Band 0ℓ 0ℓ
  ∨-semilattice   : Semilattice 0ℓ 0ℓ
  ∧-semilattice   : Semilattice 0ℓ 0ℓ

  T?              : Decidable T
  T?-diag         : T b → True (T? b)
  ```

* Added new functions to `Data.Char`:
  ```agda
  toUpper : Char → Char
  toLower : Char → Char
  ```

* Added new functions to `Data.Fin.Base`:
  ```agda
  cast   : m ≡ n → Fin m → Fin n
  lower₁ : (i : Fin (suc n)) → (n ≢ toℕ i) → Fin n
  ```

* Added new proof to `Data.Fin.Properties`:
  ```agda
  toℕ-cast          : toℕ (cast eq k) ≡ toℕ k
  toℕ-inject₁-≢     : n ≢ toℕ (inject₁ i)

  inject₁-lower₁    : inject₁ (lower₁ i n≢i) ≡ i
  lower₁-inject₁′   : lower₁ (inject₁ i) n≢i ≡ i
  lower₁-inject₁    : lower₁ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
  lower₁-irrelevant : lower₁ i n≢i₁ ≡ lower₁ i n≢i₂
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  ∩-isMagma       : IsMagma _∩_
  ∪-isMagma       : IsMagma _∪_
  ∩-isBand        : IsBand _∩_
  ∪-isBand        : IsBand _∪_
  ∩-isSemilattice : IsSemilattice _∩_
  ∪-isSemilattice : IsSemilattice _∪_

  ∩-magma         : Magma _ _
  ∪-magma         : Magma _ _
  ∩-band          : Band _ _
  ∪-band          : Band _ _
  ∩-semilattice   : Semilattice _ _
  ∪-semilattice   : Semilattice _ _
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  suc-pred          : sucℤ (pred m) ≡ m
  pred-suc          : pred (sucℤ m) ≡ m
  neg-suc           : - + suc m ≡ pred (- + m)
  suc-+             : + suc m + n ≡ sucℤ (+ m + n)
  +-pred            : m + pred n ≡ pred (m + n)
  pred-+            : pred m + n ≡ pred (m + n)
  minus-suc         : m - + suc n ≡ pred (m - + n)
  [1+m]*n≡n+m*n     : sucℤ m * n ≡ n + m * n

  ⊓-comm            : Commutative _⊓_
  ⊓-assoc           : Associative _⊓_
  ⊓-idem            : Idempotent _⊓_
  ⊓-sel             : Selective _⊓_
  m≤n⇒m⊓n≡m         : m ≤ n → m ⊓ n ≡ m
  m⊓n≡m⇒m≤n         : m ⊓ n ≡ m → m ≤ n
  m≥n⇒m⊓n≡n         : m ≥ n → m ⊓ n ≡ n
  m⊓n≡n⇒m≥n         : m ⊓ n ≡ n → m ≥ n
  m⊓n≤n             : m ⊓ n ≤ n
  m⊓n≤m             : m ⊓ n ≤ m

  ⊔-comm            : Commutative _⊔_
  ⊔-assoc           : Associative _⊔_
  ⊔-idem            : Idempotent _⊔_
  ⊔-sel             : Selective _⊔_
  m≤n⇒m⊔n≡n         : m ≤ n → m ⊔ n ≡ n
  m⊔n≡n⇒m≤n         : m ⊔ n ≡ n → m ≤ n
  m≥n⇒m⊔n≡m         : m ≥ n → m ⊔ n ≡ m
  m⊔n≡m⇒m≥n         : m ⊔ n ≡ m → m ≥ n
  m≤m⊔n             : m ≤ m ⊔ n
  n≤m⊔n             : n ≤ m ⊔ n

  neg-distrib-⊔-⊓   : - (m ⊔ n) ≡ - m ⊓ - n
  neg-distrib-⊓-⊔   : - (m ⊓ n) ≡ - m ⊔ - n

  pred-mono         : pred Preserves _≤_ ⟶ _≤_
  suc-mono          : sucℤ Preserves _≤_ ⟶ _≤_
  ⊖-monoʳ-≥-≤       : (p ⊖_) Preserves ℕ._≥_ ⟶ _≤_
  ⊖-monoˡ-≤         : (_⊖ p) Preserves ℕ._≤_ ⟶ _≤_
  +-monoʳ-≤         : (_+_ n) Preserves _≤_ ⟶ _≤_
  +-monoˡ-≤         : (_+ n) Preserves _≤_ ⟶ _≤_
  +-monoˡ-<         : (_+ n) Preserves _<_ ⟶ _<_
  +-monoʳ-<         : (_+_ n) Preserves _<_ ⟶ _<_
  *-monoˡ-≤-pos     : (+ suc n *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-non-neg : (_* + n) Preserves _≤_ ⟶ _≤
  *-monoˡ-≤-non-neg : (+ n *_) Preserves _≤_ ⟶ _≤_
  +-mono-≤          : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-mono-<          : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-mono-≤-<        : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
  +-mono-<-≤        : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  neg-mono-≤-≥      : -_ Preserves _≤_ ⟶ _≥_
  neg-mono-<->      : -_ Preserves _<_ ⟶ _>_

  *-cancelˡ-≡       : i ≢ + 0 → i * j ≡ i * k → j ≡ k
  *-cancelˡ-≤-pos   : + suc m * n ≤ + suc m * o → n ≤ o

  neg-≤-pos         : - (+ m) ≤ + n
  0⊖m≤+             : 0 ⊖ m ≤ + n
  m≤n⇒m-n≤0         : m ≤ n → m - n ≤ + 0
  m-n≤0⇒m≤n         : m - n ≤ + 0 → m ≤ n
  m≤n⇒0≤n-m         : m ≤ n → + 0 ≤ n - m
  0≤n-m⇒m≤n         : + 0 ≤ n - m → m ≤ n
  m≤pred[n]⇒m<n     : m ≤ pred n → m < n
  m<n⇒m≤pred[n]     : m < n → m ≤ pred n
  m≤m+n             : m ≤ m + + n
  n≤m+n             : n ≤ + m + n
  m-n≤m             : m - + n ≤ m

  ≤-<-trans         : Trans _≤_ _<_ _<_
  <-≤-trans         : Trans _<_ _≤_ _<_
  >→≰               : x > y → x ≰ y
  >-irrefl          : Irreflexive _≡_ _>_

  pos-+-commute     : Homomorphic₂ +_ ℕ._+_ _+_
  neg-distribˡ-*    : - (x * y) ≡ (- x) * y
  neg-distribʳ-*    : - (x * y) ≡ x * (- y)
  *-distribˡ-+      : _*_ DistributesOverˡ _+_
  ≤-steps           : m ≤ n → m ≤ + p + n
  ≤-step-neg        : m ≤ n → pred m ≤ n
  ≤-steps-neg       : m ≤ n → m - + p ≤ n
  m≡n⇒m-n≡0         : m ≡ n → m - n ≡ + 0
  m-n≡0⇒m≡n         : m - n ≡ + 0 → m ≡ n
  0≤n⇒+∣n∣≡n        : + 0 ≤ n → + ∣ n ∣ ≡ n
  +∣n∣≡n⇒0≤n        : + ∣ n ∣ ≡ n → + 0 ≤ n
  ◃-≡               : sign m ≡ sign n → ∣ m ∣ ≡ ∣ n ∣ → m ≡ n

  +-isMagma         : IsMagma _+_
  *-isMagma         : IsMagma _*_
  +-magma           : Magma 0ℓ 0ℓ
  *-magma           : Magma 0ℓ 0ℓ
  +-semigroup       : Semigroup 0ℓ 0ℓ
  *-semigroup       : Semigroup 0ℓ 0ℓ
  +-0-monoid        : Monoid 0ℓ 0ℓ
  *-1-monoid        : Monoid 0ℓ 0ℓ
  +-*-ring          : Ring 0ℓ 0ℓ

  <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder _ _ _
  ```

* Added new proofs to `Data.List.Categorical`:
  ```agda
  applicativeZero : RawApplicativeZero List
  alternative     : RawAlternative List
  ```

* Added new operations to `Data.List.Relation.Unary.All`:
  ```agda
  zipWith   : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q

  sequenceA : All (F ∘′ P) ⊆ F ∘′ All P
  sequenceM : All (M ∘′ P) ⊆ M ∘′ All P
  mapA      : (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  mapM      : (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forA      : All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  forM      : All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)

  updateAt  : x ∈ xs → (P x → P x) → All P xs → All P xs
  _[_]%=_   : All P xs → x ∈ xs → (P x → P x) → All P xs
  _[_]≔_    : All P xs → x ∈ xs → P x → All P xs
  ```

* Added new proofs to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  respects    : P Respects _≈_ → (All P) Respects _≋_
  ─⁺          : All Q xs → All Q (xs Any.─ p)
  ─⁻          : Q (Any.lookup p) → All Q (xs Any.─ p) → All Q xs

  map-cong    : f ≗ g → map f ps ≡ map g ps
  map-id      : map id ps ≡ ps
  map-compose : map g (map f ps) ≡ map (g ∘ f) ps
  lookup-map  : lookup (map f ps) i ≡ f (lookup ps i)

  ∷ʳ⁺         : All P xs → P x → All P (xs ∷ʳ x)
  ∷ʳ⁻         : All P (xs ∷ʳ x) → All P xs × P x
  ```

* Added new proofs to `Data.List.Relation.Binary.Equality.DecPropositional`:
  ```agda
  _≡?_        : Decidable (_≡_ {A = List A})
  ```

* Added new functions to `Data.List.Relation.Unary.Any`:
  ```agda
  lookup : Any P xs → A
  _∷=_   : Any P xs → A → List A
  _─_    : ∀ xs → Any P xs → List A
  ```

* Added new functions to `Data.List.Base`:
  ```agda
  intercalate       : List A → List (List A) → List A
  partitionSumsWith : (A → B ⊎ C) → List A → List B × List C
  partitionSums     : List (A ⊎ B) → List A × List B

  _[_]%=_           : (xs : List A) → Fin (length xs) → (A → A) → List A
  _[_]∷=_           : (xs : List A) → Fin (length xs) → A → List A
  _─_               : (xs : List A) → Fin (length xs) → List A

  reverseAcc        : List A → List A → List A
  ```

* Added new proofs to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-allFin : (k : Fin n) → k ∈ allFin n
  []∈inits : [] ∈ inits as
  ```

* Added new function to `Data.List.Membership.(Setoid/Propositional)`:
  ```agda
  _∷=_ : x ∈ xs → A → List A
  _─_  : (xs : List A) → x ∈ xs → List A
  ```
  Added laws for `updateAt`. The laws that previously existed for `_[_]≔_` are now
  special instances of these.

* Added new proofs to `Data.List.Membership.Setoid.Properties`:
  ```agda
  length-mapWith∈ : length (mapWith∈ xs f) ≡ length xs

  ∈-∷=⁺-updated   : v ∈ (x∈xs ∷= v)
  ∈-∷=⁺-untouched : x ≉ y → y ∈ xs → y ∈ (x∈xs ∷= v)
  ∈-∷=⁻           : y ≉ v → y ∈ (x∈xs ∷= v) → y ∈ xs

  map-∷=          : map f (x∈xs ∷= v) ≡ ∈-map⁺ f≈ pr ∷= f v
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  ≡-dec                : Decidable _≡_ → Decidable {A = List A} _≡_

  ++-cancelˡ           : xs ++ ys ≡ xs ++ zs → ys ≡ zs
  ++-cancelʳ           : ys ++ xs ≡ zs ++ xs → ys ≡ zs
  ++-cancel            : Cancellative _++_
  ++-conicalˡ          : xs ++ ys ≡ [] → xs ≡ []
  ++-conicalʳ          : xs ++ ys ≡ [] → ys ≡ []
  ++-conical           : Conical [] _++_
  ++-isMagma           : IsMagma _++_

  length-%=            : length (xs [ k ]%= f) ≡ length xs
  length-∷=            : length (xs [ k ]∷= v) ≡ length xs
  length-─             : length (xs ─ k) ≡ pred (length xs)
  map-∷=               : map f (xs [ k ]∷= v) ≡ map f xs [ cast eq k ]∷= f v
  map-─                : map f (xs ─ k) ≡ map f xs ─ cast eq k

  length-applyUpTo     : length (applyUpTo     f n) ≡ n
  length-applyDownFrom : length (applyDownFrom f n) ≡ n
  length-upTo          : length (upTo            n) ≡ n
  length-downFrom      : length (downFrom        n) ≡ n
  length-tabulate      : length (tabulate      f  ) ≡ n

  lookup-applyUpTo     : lookup (applyUpTo     f n) i ≡ f (toℕ i)
  lookup-applyDownFrom : lookup (applyDownFrom f n) i ≡ f (n ∸ (suc (toℕ i)))
  lookup-upTo          : lookup (upTo            n) i ≡ toℕ i
  lookup-downFrom      : lookup (downFrom        n) i ≡ n ∸ (suc (toℕ i))
  lookup-tabulate      : lookup (tabulate      f)  i′ ≡ f i

  map-tabulate         : map f (tabulate g) ≡ tabulate (f ∘ g)
  ```

* Added new proofs to `Data.List.Relation.Binary.Permutation.Inductive.Properties`:
  ```agda
  ++-isMagma : IsMagma _↭_ _++_
  ++-magma   : Magma _ _
  ```

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  reverseAcc⁺ : Pointwise R a x → Pointwise R b y → Pointwise R (reverseAcc a b) (reverseAcc x y)
  reverse⁺    : Pointwise R as bs → Pointwise R (reverse as) (reverse bs)
  map⁺        : Pointwise (λ a b → R (f a) (g b)) as bs → Pointwise R (map f as) (map g bs)
  map⁻        : Pointwise R (map f as) (map g bs) → Pointwise (λ a b → R (f a) (g b)) as bs
  filter⁺     : Pointwise R as bs → Pointwise R (filter P? as) (filter Q? bs)
  replicate⁺  : R a b → Pointwise R (replicate n a) (replicate n b)
  irrelevant  : Irrelevant R → Irrelevant (Pointwise R)
  ```


* Added new function to `Data.Maybe.Base`:
  ```agda
  _<∣>_     : Maybe A → Maybe A → Maybe A
  ```

* Added new proofs to `Data.Maybe.Categorical`:
  ```agda
  applicativeZero : RawApplicativeZero Maybe
  alternative     : RawAlternative Maybe
  ```

* Added new proof to `Data.Maybe.Properties`:
  ```agda
  ≡-dec : Decidable _≡_ → Decidable {A = Maybe A} _≡_
  ```

* Added new proof to `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  reflexive : _≡_ ⇒ R → _≡_ ⇒ Pointwise R
  ```

* Added new proofs to `Data.Maybe.Relation.Unary.All`:
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

* Added new proofs to `Data.Maybe.Relation.Unary.Any`:
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

* Added a third alternative definition of "less than" to `Data.Nat.Base`:
  ```agda
  _≤‴_ : Rel ℕ 0ℓ
  _<‴_ : Rel ℕ 0ℓ
  _≥‴_ : Rel ℕ 0ℓ
  _>‴_ : Rel ℕ 0ℓ
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  +-isMagma          : IsMagma _+_
  *-isMagma          : IsMagma _*_
  ⊔-isMagma          : IsMagma _⊔_
  ⊓-isMagma          : IsMagma _⊓_
  ⊔-isBand           : IsBand _⊔_
  ⊓-isBand           : IsBand _⊓_
  ⊔-isSemilattice    : IsSemilattice _⊔_
  ⊓-isSemilattice    : IsSemilattice _⊓_

  +-magma            : Magma 0ℓ 0ℓ
  *-magma            : Magma 0ℓ 0ℓ
  ⊔-magma            : Magma 0ℓ 0ℓ
  ⊓-magma            : Magma 0ℓ 0ℓ
  ⊔-band             : Band 0ℓ 0ℓ
  ⊓-band             : Band 0ℓ 0ℓ
  ⊔-semilattice      : Semilattice 0ℓ 0ℓ
  ⊓-semilattice      : Semilattice 0ℓ 0ℓ

  +-cancelˡ-<        : LeftCancellative _<_ _+_
  +-cancelʳ-<        : RightCancellative _<_ _+_
  +-cancel-<         : Cancellative _<_ _+_

  m≤n⇒m⊓o≤n          : m ≤ n → m ⊓ o ≤ n
  m≤n⇒o⊓m≤n          : m ≤ n → o ⊓ m ≤ n
  m<n⇒m⊓o<n          : m < n → m ⊓ o < n
  m<n⇒o⊓m<n          : m < n → o ⊓ m < n
  m≤n⊓o⇒m≤n          : m ≤ n ⊓ o → m ≤ n
  m≤n⊓o⇒m≤o          : m ≤ n ⊓ o → m ≤ o
  m<n⊓o⇒m<n          : m < n ⊓ o → m < n
  m<n⊓o⇒m<o          : m < n ⊓ o → m < o
  m≤n⇒m≤n⊔o          : m ≤ n → m ≤ n ⊔ o
  m≤n⇒m≤o⊔n          : m ≤ n → m ≤ o ⊔ n
  m<n⇒m<n⊔o          : m < n → m < n ⊔ o
  m<n⇒m<o⊔n          : m < n → m < o ⊔ n
  m⊔n≤o⇒m≤o          : m ⊔ n ≤ o → m ≤ o
  m⊔n≤o⇒n≤o          : m ⊔ n ≤ o → n ≤ o
  m⊔n<o⇒m<o          : m ⊔ n < o → m < o
  m⊔n<o⇒n<o          : m ⊔ n < o → n < o

  m≢0⇒suc[pred[m]]≡m : m ≢ 0 → suc (pred m) ≡ m
  m≢1+n+m            : m ≢ suc (n + m)

  ≡ᵇ⇒≡               : T (m ≡ᵇ n) → m ≡ n
  ≡⇒≡ᵇ               : m ≡ n → T (m ≡ᵇ n)
  ≡-irrelevant       : Irrelevant {A = ℕ} _≡_
  ≟-diag             : (eq : m ≡ n) → (m ≟ n) ≡ yes eq

  ≤′-trans           : Transitive _≤′_

  m<ᵇn⇒1+m+[n-1+m]≡n : T (m <ᵇ n) → suc m + (n ∸ suc m) ≡ n
  m<ᵇ1+m+n           : T (m <ᵇ suc (m + n))

  <ᵇ⇒<″              : T (m <ᵇ n) → m <″ n
  <″⇒<ᵇ              : m <″ n → T (m <ᵇ n)
  ≤‴⇒≤″              : ∀{m n} → m ≤‴ n → m ≤″ n
  ≤″⇒≤‴              : ∀{m n} → m ≤″ n → m ≤‴ n

  ≤″-irrelevant      : Irrelevant _≤″_
  ≥″-irrelevant      : Irrelevant _≥″_
  <″-irrelevant      : Irrelevant _<″_
  >″-irrelevant      : Irrelevant _>″_

  m≤‴m+k             : m + k ≡ n → m ≤‴ n
    ```

* Added new proof to `Data.Product.Properties.WithK`:
  ```agda
  ,-injective : (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ≡-dec       : Decidable _≡_ → (∀ {a} → Decidable {A = B a} _≡_) → Decidable {A = Σ A B} _≡_
  ```

* Added new functions to `Data.Product.Relation.Binary.Pointwise.NonDependent`:
  ```agda
  <_,_>ₛ : A ⟶ B → A ⟶ C → A ⟶ (B ×ₛ C)
  proj₁ₛ : (A ×ₛ B) ⟶ A
  proj₂ₛ : (A ×ₛ B) ⟶ B
  swapₛ  : (A ×ₛ B) ⟶ (B ×ₛ A)
  ```

* Added new functions to `Data.Rational`:
  ```agda
  -_       : ℚ → ℚ
  1/_      : (p : ℚ) → .{n≢0 : ∣ ℚ.numerator p ∣ ≢0} → ℚ
  _*_      : ℚ → ℚ → ℚ
  _+_      : ℚ → ℚ → ℚ
  _-_      : ℚ → ℚ → ℚ
  _/_      : (p₁ p₂ : ℚ) → {n≢0 : ∣ ℚ.numerator p₂ ∣ ≢0} → ℚ
  show     : ℚ → String
  ```

* Added new proofs to `Data.Sign.Properties`:
  ```agda
  *-isMagma : IsMagma _*_
  *-magma   : Magma 0ℓ 0ℓ
  ```

* Added new functions to `Data.Sum.Base`:
  ```agda
  fromDec : Dec P → P ⊎ ¬ P
  toDec   : P ⊎ ¬ P → Dec P
  ```

* Added new proof to `Data.Sum.Properties`:
  ```agda
  ≡-dec : Decidable _≡_ → Decidable _≡_ → Decidable {A = A ⊎ B} _≡_
  ```

* Added new functions to `Data.Sum.Relation.Binary.Pointwise`:
  ```agda
  inj₁ₛ  : A ⟶ (A ⊎ₛ B)
  inj₂ₛ  : B ⟶ (A ⊎ₛ B)
  [_,_]ₛ : (A ⟶ C) → (B ⟶ C) → (A ⊎ₛ B) ⟶ C
  swapₛ  : (A ⊎ₛ B) ⟶ (B ⊎ₛ A)
  ```

* Added new function to `Data.These`:
  ```agda
  fromSum : A ⊎ B → These A B
  ```

* Added to `Data.Vec` a generalization of single point overwrite `_[_]≔_` to
  single-point modification `_[_]%=_` (with an alias `updateAt` with different
  argument order):
  ```agda
  _[_]%=_   : Vec A n → Fin n → (A → A) → Vec A n
  updateAt  : Fin n → (A → A) → Vec A n → Vec A n
  ```

* Added proofs for `updateAt` to `Data.Vec.Properties`. Previously existing proofs for
  `_[_]≔_` are now special instances of these.

* Added new proofs to `Data.Vec.Relation.Unary.Any.Properties`:
  ```agda
  lookup-index          : (p : Any P xs) → P (lookup (index p) xs)

  lift-resp             : P Respects _≈_ → (Any P) Respects (Pointwise _≈_)
  here-injective        : here p ≡ here q → p ≡ q
  there-injective       : there p ≡ there q → p ≡ q

  ¬Any[]                : ¬ Any P []
  ⊥↔Any⊥                : ⊥ ↔ Any (const ⊥) xs
  ⊥↔Any[]               : ⊥ ↔ Any P []

  map-id                : ∀ f → (∀ p → f p ≡ p) → ∀ p → Any.map f p ≡ p
  map-∘                 : Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)

  swap                  : Any (λ x → Any (x ∼_) ys) xs → Any (λ y → Any (_∼ y) xs) ys
  swap-there            : swap (Any.map there p) ≡ there (swap p)
  swap-invol            : swap (swap p) ≡ p
  swap↔                 : Any (λ x → Any (x ∼_) ys) xs ↔ Any (λ y → Any (_∼ y) xs) ys

  Any-⊎⁺                : Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁻                : Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  ⊎↔                    : (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs

  Any-×⁺                : Any P xs × Any Q ys → Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁻                : Any (λ x → Any (λ y → P x × Q y) ys) xs → Any P xs × Any Q ys

  singleton⁺            : P x → Any P [ x ]
  singleton⁻            : Any P [ x ] → P x
  singleton⁺∘singleton⁻ : singleton⁺ (singleton⁻ p) ≡ p
  singleton⁻∘singleton⁺ : singleton⁻ (singleton⁺ p) ≡ p
  singleton↔            : P x ↔ Any P [ x ]

  map⁺                  : Any (P ∘ f) xs → Any P (map f xs)
  map⁻                  : Any P (map f xs) → Any (P ∘ f) xs
  map⁺∘map⁻             : map⁺ (map⁻ p) ≡ p
  map⁻∘map⁺             : map⁻ (map⁺ p) ≡ p
  map↔                  : Any (P ∘ f) xs ↔ Any P (map f xs)

  ++⁺ˡ                  : Any P xs → Any P (xs ++ ys)
  ++⁺ʳ                  : Any P ys → Any P (xs ++ ys)
  ++⁻                   : Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁺∘++⁻               : ∀ p → [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁻∘++⁺               : ∀ p → ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++-comm               : ∀ xs ys → Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm∘++-comm       : ∀ p → ++-comm ys xs (++-comm xs ys p) ≡ p
  ++-insert             : ∀ xs → P x → Any P (xs ++ [ x ] ++ ys)
  ++↔                   : (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔++                 : ∀ xs ys → Any P (xs ++ ys) ↔ Any P (ys ++ xs)

  concat⁺               : Any (Any P) xss → Any P (concat xss)
  concat⁻               : Any P (concat xss) → Any (Any P) xss
  concat⁻∘++⁺ˡ          : ∀ xss p → concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
  concat⁻∘++⁺ʳ          : ∀ xs xss p → concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
  concat⁺∘concat⁻       : ∀ xss p → concat⁺ (concat⁻ xss p) ≡ p
  concat⁻∘concat⁺       : ∀ p → concat⁻ xss (concat⁺ p) ≡ p
  concat↔               : Any (Any P) xss ↔ Any P (concat xss)

  tabulate⁺             : ∀ i → P (f i) → Any P (tabulate f)
  tabulate⁻             : Any P (tabulate f) → ∃ λ i → P (f i)

  mapWith∈⁺             : ∀ f → (∃₂ λ x p → P (f p)) → Any P (mapWith∈ xs f)
  mapWith∈⁻             : ∀ xs f → Any P (mapWith∈ xs f) → ∃₂ λ x p → P (f p)
  mapWith∈↔             : (∃₂ λ x p → P (f p)) ↔ Any P (mapWith∈ xs f)

  toList⁺               : Any P xs → List.Any P (toList xs)
  toList⁻               : List.Any P (toList xs) → Any P xs
  fromList⁺             : List.Any P xs → Any P (fromList xs)
  fromList⁻             : Any P (fromList xs) → List.Any P xs

  ∷↔                    : ∀ P → (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
  >>=↔                  : Any (Any P ∘ f) xs ↔ Any P (xs >>= f)
  ```

* Added new functions to `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  fromAny : Any P xs → ∃ λ x → x ∈ xs × P x
  toAny   : x ∈ xs → P x → Any P xs
  ```

* Added new proof to `Data.Vec.Properties`:
  ```agda
  ≡-dec : Decidable _≡_ → ∀ {n} → Decidable {A = Vec A n} _≡_
  ```

* Added new proofs to `Function.Related.TypeIsomorphisms`:
  ```agda
  ×-isMagma : ∀ k ℓ → IsMagma (Related ⌊ k ⌋) _×_
  ⊎-isMagma : ∀ k ℓ → IsMagma (Related ⌊ k ⌋) _⊎_

  ×-magma   : Symmetric-kind → (ℓ : Level) → Magma _ _
  ⊎-magma   : Symmetric-kind → (ℓ : Level) → Semigroup _ _
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  wlog : Total _R_ → Symmetric Q → (∀ a b → a R b → Q a b) → ∀ a b → Q a b
  ```

* Added new definitions to `Relation.Binary.Core`:
  ```agda
  Antisym R S E = ∀ {i j} → R i j → S j i → E i j

  Max : REL A B ℓ → B → Set _
  Min : REL A B ℓ → A → Set _

  Conn P Q = ∀ x y → P x y ⊎ Q y x

  P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y
  ```
  Additionally the definition of the types `_Respectsʳ_`/`_Respectsˡ_` has been
  generalised as follows in order to support heterogenous relations:
  ```agda
  _Respectsʳ_ : REL A B ℓ₁ → Rel B ℓ₂ → Set _
  _Respectsˡ_ : REL A B ℓ₁ → Rel A ℓ₂ → Set _
  ```

* Added new proofs to `Relation.Binary.Lattice`:
  ```agda
  Lattice.setoid        : Setoid c ℓ
  BoundedLattice.setoid : Setoid c ℓ
  ```

* Added new operations and proofs to `Relation.Binary.Properties.HeytingAlgebra`:
  ```agda
  y≤x⇨y            : y ≤ x ⇨ y
  ⇨-unit           : x ⇨ x ≈ ⊤
  ⇨-drop           : (x ⇨ y) ∧ y ≈ y
  ⇨-app            : (x ⇨ y) ∧ x ≈ y ∧ x
  ⇨-relax          : _⇨_ Preserves₂ (flip _≤_) ⟶ _≤_ ⟶ _≤_
  ⇨-cong           : _⇨_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ⇨-applyˡ         : w ≤ x → (x ⇨ y) ∧ w ≤ y
  ⇨-applyʳ         : w ≤ x → w ∧ (x ⇨ y) ≤ y
  ⇨-curry          : x ∧ y ⇨ z ≈ x ⇨ y ⇨ z
  ⇨ʳ-covariant     : (x ⇨_) Preserves _≤_ ⟶ _≤_
  ⇨ˡ-contravariant : (_⇨ x) Preserves (flip _≤_) ⟶ _≤_

  ¬_               : Op₁ Carrier
  x≤¬¬x            : x ≤ ¬ ¬ x
  de-morgan₁       : ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
  de-morgan₂-≤     : ¬ (x ∧ y) ≤ ¬ ¬ (¬ x ∨ ¬ y)
  de-morgan₂-≥     : ¬ ¬ (¬ x ∨ ¬ y) ≤ ¬ (x ∧ y)
  de-morgan₂       : ¬ (x ∧ y) ≈ ¬ ¬ (¬ x ∨ ¬ y)
  weak-lem         : ¬ ¬ (¬ x ∨ x) ≈ ⊤
  ```

* Added new proofs to `Relation.Binary.Properties.JoinSemilattice`:
  ```agda
  x≤y⇒x∨y≈y : x ≤ y → x ∨ y ≈ y
  ```

* Added new proofs to `Relation.Binary.Properties.Lattice`:
  ```agda
  ∧≤∨            : x ∧ y ≤ x ∨ y
  quadrilateral₁ : x ∨ y ≈ x → x ∧ y ≈ y
  quadrilateral₂ : x ∧ y ≈ y → x ∨ y ≈ x
  collapse₁      : x ≈ y → x ∧ y ≈ x ∨ y
  collapse₂      : x ∨ y ≤ x ∧ y → x ≈ y
  ```

* Added new proofs to `Relation.Binary.Properties.MeetSemilattice`:
  ```agda
  y≤x⇒x∧y≈y : y ≤ x → x ∧ y ≈ y
  ```

* Added new definitions to `Relation.Binary.PropositionalEquality`:
  ```agda
  trans-injectiveˡ  : trans p₁ q ≡ trans p₂ q → p₁ ≡ p₂
  trans-injectiveʳ  : trans p q₁ ≡ trans p q₂ → q₁ ≡ q₂
  subst-injective   : subst P x≡y p ≡ subst P x≡y q → p ≡ q
  cong-id           : cong id p ≡ p
  cong-∘            : cong (f ∘ g) p ≡ cong f (cong g p)
  cong-≡id          : (f≡id : ∀ x → f x ≡ x) → cong f (f≡id x) ≡ f≡id (f x)
  naturality        : trans (cong f x≡y) (f≡g y) ≡ trans (f≡g x) (cong g x≡y)
  subst-application : (eq : x₁ ≡ x₂) → subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong f eq) y)
  subst-subst       : subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
  subst-subst-sym   : subst P x≡y (subst P (sym x≡y) p) ≡ p
  subst-sym-subst   : subst P (sym x≡y) (subst P x≡y p) ≡ p
  subst-∘           : subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
  trans-assoc       : trans (trans p q) r ≡ trans p (trans q r)
  trans-reflʳ       : trans p refl ≡ p
  trans-symʳ        : trans p (sym p) ≡ refl
  trans-symˡ        : trans (sym p) p ≡ refl
  ```

