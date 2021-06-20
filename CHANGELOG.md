Version 1.7
===========

The library has been tested using Agda 2.6.2.

Highlights
----------

* New module for making system calls during type checking, `Reflection.External`,
  which re-exports `Agda.Builtin.Reflection.External`.

* New predicate for lists that are enumerations their type in
  `Data.List.Relation.Unary.Enumerates`.

* New weak induction schemes in `Data.Fin.Induction` that allows one to avoid
  the complicated use of `Acc`/`inject`/`raise` when proving inductive properties
  over finite sets.

Bug-fixes
---------

* Added missing module `Function.Metric` which re-exports
  `Function.Metric.(Core/Definitions/Structures/Bundles)`. This module was referred
  to in the documentation of its children but until now was not present.

* Added missing fixity declaration to `_<_` in
  `Relation.Binary.Construct.NonStrictToStrict`.

Non-backwards compatible changes
--------------------------------

#### Floating-point arithmetic

* The functions in `Data.Float.Base` were updated following changes upstream,
  in `Agda.Builtin.Float`, see <https://github.com/agda/agda/pull/4885>.

* The bitwise binary relations on floating-point numbers (`_<_`, `_≈ᵇ_`, `_==_`)
  have been removed without replacement, as they were deeply unintuitive,
  e.g., `∀ x → x < -x`.

#### Reflection

* The representation of reflected syntax in `Reflection.Term`,
  `Reflection.Pattern`, `Reflection.Argument` and
  `Reflection.Argument.Information` has been updated to match the new
  representation used in Agda 2.6.2. Specifically, the following
  changes were made:

  * The type of the `var` constructor of the `Pattern` datatype has
    been changed from `(x : String) → Pattern` to `(x : Int) →
    Pattern`.

  * The type of the `dot` constructor of the `Pattern` datatype has
    been changed from `Pattern` to `(t : Term) → Pattern`.

  * The types of the `clause` and `absurd-clause` constructors of the
    `Clause` datatype now take an extra argument `(tel : Telescope)`,
    where `Telescope = List (String × Arg Type)`.

  * The following constructors have been added to the `Sort` datatype:
    `prop : (t : Term) → Sort`, `propLit : (n : Nat) → Sort`, and
    `inf : (n : Nat) → Sort`.

  * In `Reflection.Argument.Information` the function `relevance` was
    replaced by `modality`.

  * The type of the `arg-info` constructor is now
    `(v : Visibility) (m : Modality) → ArgInfo`.

  * In `Reflection.Argument` (as well as `Reflection`) there is a new
    pattern synonym `defaultModality`, and the pattern synonyms
    `vArg`, `hArg` and `iArg` have been changed.

  * Two new modules have been added, `Reflection.Argument.Modality`
    and `Reflection.Argument.Quantity`. The constructors of the types
    `Modality` and `Quantity` are reexported from `Reflection`.

#### Sized types

* Sized types are no longer considered safe in Agda 2.6.2. As a
  result, all modules that use `--sized-types` no longer have the
  `--safe` flag.  For a full list of affected modules, refer to the
  relevant [commit](https://github.com/agda/agda-stdlib/pull/1465/files#diff-e1c0e3196e4cea6ff808f5d2906031a7657130e10181516206647b83c7014584R91-R131.)

* In order to maintain the safety of `Data.Nat.Pseudorandom.LCG`, the function
  `stream` that relies on the newly unsafe `Codata` modules has
  been moved to the new module `Data.Nat.Pseudorandom.LCG.Unsafe`.

* In order to maintain the safety of the modules in the `Codata.Musical` directory,
  the functions `fromMusical` and `toMusical` defined in:
  ```
  Codata.Musical.Colist
  Codata.Musical.Conat
  Codata.Musical.Cofin
  Codata.Musical.M
  Codata.Musical.Stream
  ```
  have been moved to a new module `Codata.Musical.Conversion` and renamed to
  `X.fromMusical` and `X.toMusical` for each of `Codata.Musical.X`.

* In order to maintain the safety of `Data.Container(.Indexed)`, the greatest fixpoint
  of containers, `ν`, has been moved from `Data.Container(.Indexed)` to a new module
  `Data.Container(.Indexed).Fixpoints.Guarded` which also re-exports the least fixpoint.

#### Other

* Replaced existing O(n) implementation of `Data.Nat.Binary.fromℕ` with a new O(log n)
  implementation. The old implementation is maintained under `Data.Nat.Binary.fromℕ'`
  and proven to be equivalent to the new one.

* `Data.Maybe.Base` now re-exports the definition of `Maybe` given by
  `Agda.Builtin.Maybe`. The `Foreign.Haskell` modules and definitions
  corresponding to `Maybe` have been removed. See the release notes of
  Agda 2.6.2 for more information.

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* New module for making system calls during type checking:
  ```agda
  Reflection.External
  ```

* New modules for universes and annotations of reflected syntax:
  ```
  Reflection.Universe
  Reflection.Annotated
  Reflection.Annotated.Free
  ```

* Added new module for unary relations over sized types now that `Size`
  lives in it's own universe since Agda 2.6.2.
  ```agda
  Relation.Unary.Sized
  ```

* Metrics specialised to co-domains with rational numbers:
  ```
  Function.Metric.Rational
  Function.Metric.Rational.Definitions
  Function.Metric.Rational.Structures
  Function.Metric.Rational.Bundles
  ```

* Lists that contain every element of a type:
  ```
  Data.List.Relation.Unary.Enumerates.Setoid
  Data.List.Relation.Unary.Enumerates.Setoid.Properties
  ```

* (Unsafe) sized W type:
  ```
  Data.W.Sized
  ```

* (Unsafe) container fixpoints:
  ```
  Data.Container.Fixpoints.Sized
  ```

Other minor additions
---------------------

* Added new relations to `Data.Fin.Base`:
  ```agda
  _≥_ = ℕ._≥_ on toℕ
  _>_ = ℕ._>_ on toℕ
  ```

* Added new proofs to `Data.Fin.Induction`:
  ```agda
  >-wellFounded   : WellFounded {A = Fin n} _>_

  <-weakInduction : P zero      → (∀ i → P (inject₁ i) → P (suc i)) → ∀ i → P i
  >-weakInduction : P (fromℕ n) → (∀ i → P (suc i) → P (inject₁ i)) → ∀ i → P i
  ```

* Added new proofs to `Relation.Binary.Properties.Setoid`:
  ```agda
  respʳ-flip : _≈_ Respectsʳ (flip _≈_)
  respˡ-flip : _≈_ Respectsˡ (flip _≈_)
  ```

* Added new function to `Data.Fin.Base`:
  ```agda
  pinch : Fin n → Fin (suc n) → Fin n
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  pinch-surjective : Surjective _≡_ (pinch i)
  pinch-mono-≤     : (pinch i) Preserves _≤_ ⟶ _≤_
  ```

* Added new proofs to `Data.Nat.Binary.Properties`:
  ```agda
  fromℕ≡fromℕ'  : fromℕ ≗ fromℕ'
  toℕ-fromℕ'    : toℕ ∘ fromℕ' ≗ id
  fromℕ'-homo-+ : fromℕ' (m ℕ.+ n) ≡ fromℕ' m + fromℕ' n
  ```

* Rewrote proofs in `Data.Nat.Binary.Properties` for new implementation of `fromℕ`:
  ```agda
  toℕ-fromℕ    : toℕ ∘ fromℕ ≗ id
  fromℕ-homo-+ : fromℕ (m ℕ.+ n) ≡ fromℕ m + fromℕ n
  ```

* Added new proof to `Data.Nat.DivMod`:
  ```agda
  m/n≤m : (m / n) {≢0} ≤ m
  ```

* Added new type in `Size`:
  ```agda
  SizedSet ℓ = Size → Set ℓ
  ```
