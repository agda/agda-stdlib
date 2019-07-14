Version 1.2-dev
===============

The library has been tested using Agda version 2.6.0.1.

Changes since 1.1:

Highlights
----------



Bug-fixes
---------



Other non-backwards compatible changes
--------------------------------------

#### New function hierarchy

The main problems with the current way various types of functions are
handled are:
  1. The raw functions were wrapped in the  equality-preserving
         type `_⟶_` from `Function.Equality`. As the rest of the library
     very rarely used such wrapped functions, it was almost impossible
     to write code that interfaces neatly  between the `Function` hierarchy
     and, for example, the `Algebra` hierarchy.
  2. The symbol `_⟶_` that was used for equality preserving functions
     was almost indistinguishable from ordinary functions `_→_` in many fonts,
     leading to confusion when reading code.
  3. The hierarchy didn't follow the same pattern as the other record
     hierarchies in the standard library. Coupled with point 1., this meant
     that anecdotally people are scared away from it.
  4. There was no way of specifying a function has a specific property
     (e.g. is injective) without specifying all the properties required
     of the equality relation as well. This is in contrast to the
     `Relation.Binary` and `Algebra` hierarchies where it is perfectly
     possible to specify that for example an operation is commutative
     without providing all the proofs associated with the equality relation.

To address these problems a new function hierarchy similar to the ones in
`Relation.Binary` and `Algebra` has been created. The new modules are as
follows:
  - `Function.Definitions` containing definitions like `Injective`,
    `Surjective` parameterised by the function and the equality relations
     over the domain and codomain.
  - `Function.Structures` containing definitions like `IsInjection`,
     `IsSurjection`, once again parameterised by the function and the equality
     relations but also wrapping up all the equality and congruence lemmas.
  - `Function.Packages` containing definitions like `Injection`, `Surjection`
     which provides essentially the same top-level interface as currently exists,
     i.e. parameterised by setoids but hiding the function.
  - The old file `Function` has been moved to `Function.Core` and `Function`
    now exports the whole of this hierarchy, just like `Relation.Binary`.

These changes are nearly entirely backwards compatible. The only problem will occur
is when code imports both `Function` and e.g. `Function.Injection` in which case the
old and new definitions of `Injection` will clash. In the short term this can
immediately be fixed by importing `Function.Core` instead of `Function`. However
we would encourage to the new hierarchy in the medium to long term.

The old modules will probably be deprecated (NOT COMPLETED AS OF YET)
  ```agda
  Function.Equivalence
  Function.Equality
  Function.Bijection
  Function.Injection
  Function.Surjection
  Function.LeftInverse
  ```

#### Re-implementation of `Data.Bin`

* `Data/Bin.agda` and `Data.Bin/*.agda`  of lib-1.0 are removed,
  added new `Data.Bin.Base, Data.Bin.Properties`.
  This total change of the Bin part is done for the following reasons.
  1) Many necessary functions and proofs are added.
  2) After this has been done, the author noticed (decided) that the whole
   thing is implemented much simpler with using another representation for Bin:
   the one with certain three constructors. This representation is taken
   (with renaming the constructors) from the letter by Martin Escardo to the
   e-mail list. The referred code (of 2016) resides on
   http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html

New modules
-----------
The following new modules have been added to the library:

* The following new modules have been added to the library:
  ```
  Algebra.Morphism.RawMagma
  Algebra.Morphism.RawMonoid

  Algebra.Properties.Semigroup
  Algebra.Properties.CommutativeSemigroup

  Data.Bin
  Data.Bin.Base
  Data.Bin.Properties

  Function.Definitions
  Function.Packages
  Function.Structures

  Relation.Binary.Properties.Setoid
  ```

Relocated modules
-----------------
The following modules have been moved as part of a drive to improve
usability and consistency across the library. The old modules still exist and
therefore all existing code should still work, however they have been deprecated
and, although not anticipated any time soon, they may eventually
be removed in some future release of the library. After the next release of Agda
automated warnings will be attached to these modules to discourage their use.


Deprecated names
----------------
The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.

* In `Data.Integer.Properties`:
  ```agda
  [1+m]*n≡n+m*n ↦ suc-*
  ```

* In `Data.Nat.Properties`:
  ```agda
  +-*-suc ↦ *-suc
  ```

Other minor additions
---------------------

* Added new proof to `Data.Integer.Properties`:
  ```agda
  *-suc : m * sucℤ n ≡ m + m * n
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  even≢odd : ∀ m n → 2 * m ≢ suc (2 * n)
  0≢1+n    : ∀ {n} → 0 ≢ suc n
  n<1+n    : ∀ {n} → n < suc n
  ```

* Added functions to extract the universe level from a type and a term.
  ```agda
  levelOfType : ∀ {a} → Set a → Level
  levelOfTerm : ∀ {a} {A : Set a} → A → Level
  ```
