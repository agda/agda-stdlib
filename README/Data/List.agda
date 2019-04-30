------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for the List type
------------------------------------------------------------------------

{-# OPTIONS --warning noMissingDefinitions #-}

module README.Data.List where

open import Algebra.Structures
open import Data.Char
open import Data.Char.Properties as CharProp hiding (setoid)
open import Data.Nat
open import Data.Nat.Properties as NatProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; setoid)

------------------------------------------------------------------------
-- 1. Basics
------------------------------------------------------------------------
-- The `List` datatype is exported by the following file:

open import Data.List

module Basics where

  -- Lists are built using the "[]" and "_∷_" constructors.

  list₁ : List ℕ
  list₁ = 3 ∷ 1 ∷ 2 ∷ []

  -- Basic operations over lists are also exported by the same file.

  lem₁ : sum list₁ ≡ 6
  lem₁ = refl

  lem₂ : map (_+ 2) list₁ ≡ 5 ∷ 3 ∷ 4 ∷ []
  lem₂ = refl

  lem₃ : take 2 list₁ ≡ 3 ∷ 1 ∷ []
  lem₃ = refl

  lem₄ : reverse list₁ ≡ 2 ∷ 1 ∷ 3 ∷ []
  lem₄ = refl

  lem₅ : list₁ ++ list₁ ≡ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ []
  lem₅ = refl

  -- Various properties of these operations can be found in:

  open import Data.List.Properties

  lem₆ : ∀ n (xs : List ℕ) → take n xs ++ drop n xs ≡ xs
  lem₆ = take++drop

  lem₇ : ∀ (xs : List ℕ) → reverse (reverse xs) ≡ xs
  lem₇ = reverse-involutive

  lem₈ : ∀ (xs ys zs : List ℕ) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  lem₈ = ++-assoc

------------------------------------------------------------------------
-- 2. Binary relations over lists
------------------------------------------------------------------------

-- All binary relations over lists are found in the folder
-- `Data.List.Relation.Binary`.

------------------------------------------------------------------------
-- Pointwise

module PointwiseExplanation where

  -- One of the most basic ways to form a binary relation between two
  -- lists of type `List A`, given a binary relation over `A`, is to say
  -- that two lists are related if:
  --   i) the first elements in the lists are related
  --   ii) the second elements in the lists are related
  --   iii) the third elements in the lists are related etc.
  --
  -- A formalisation of this "pointwise" lifting of a relation to lists
  -- is found in:

  open import Data.List.Relation.Binary.Pointwise

  -- The same syntax to construct a list (`[]` & `_∷_`) is used to
  -- construct proofs for the `Pointwise` relation. For example if you
  -- want to prove that one list is strictly less than another list:

  lem₁ : Pointwise _<_ (0 ∷ 2 ∷ 1 ∷ []) (1 ∷ 4 ∷ 2 ∷ [])
  lem₁ = 0<1 ∷ 2<4 ∷ 1<2 ∷ []
    where
    0<1 = s≤s z≤n
    2<4 = s≤s (s≤s (s≤s z≤n))
    1<2 = s≤s 0<1

  -- Lists that are related by `Pointwise` must be of the same length.
  -- For example:

  open import Relation.Nullary using (¬_)

  lem₂ : ¬ Pointwise _<_ (0 ∷ 2 ∷ []) (1 ∷ [])
  lem₂ (0<1 ∷ ())

------------------------------------------------------------------------
-- Equality

module EqualityExplanation where

  -- There are many different options for what it means for two
  -- different lists of type `List A` to be "equal". We will initially
  -- consider notions of equality that require the list elements to be
  -- in the same order and later discuss other types of equality.

  -- The most basic option in the former case is simply to use
  -- propositional equality `_≡_` over lists:

  open import Relation.Binary.PropositionalEquality
    using (_≡_; sym; refl)

  lem₁ : 1 ∷ 2 ∷ 3 ∷ [] ≡ 1 ∷ 2 ∷ 3 ∷ []
  lem₁ = refl

  -- However propositional equality is only suitable when we want to
  -- use propositional equality to compare the individual elements.
  -- Although a contrived example, consider trying to prove the
  -- equality of two lists of the type `List (ℕ → ℕ)`:

  lem₂ : (λ x → 2 * x + 2) ∷ [] ≡ (λ x → 2 * (x + 1)) ∷ []

  -- In such a case it is impossible to prove the two lists equal with
  -- refl as the two functions are not propositionally equal. In the
  -- absence of postulating function extensionality (see README.Axioms),
  -- the most common definition of function equality is to say that two
  -- functions are equal if their outputs are always propositionally
  -- equal for any input. This notion of function equality `_≗_` is
  -- found in:

  open import Relation.Binary.PropositionalEquality using (_≗_)

  -- We now want to use the `Pointwise` relation to say that the two
  -- lists are equal if their elements are pointwise equal with resepct
  -- to `_≗_`. However instead of using the pointwise module directly
  -- to write:

  open import Data.List.Relation.Binary.Pointwise using (Pointwise)

  lem₃ : Pointwise _≗_ ((λ x → x + 1) ∷ []) ((λ x → x + 2 ∸ 1) ∷ [])

  -- the library provides some nicer wrappers and infix notation in the
  -- folder "Data.List.Relation.Binary.Equality".

  -- Within this folder there are four different modules.

  import Data.List.Relation.Binary.Equality.Setoid           as SetoidEq
  import Data.List.Relation.Binary.Equality.DecSetoid        as DecSetoidEq
  import Data.List.Relation.Binary.Equality.Propositional    as PropEq
  import Data.List.Relation.Binary.Equality.DecPropositional as DecPropEq

  -- Which one should be used depends on whether the underlying equality
  -- over "A" is:
  --   i)  propositional or setoid-based
  --   ii) decidable.

  -- Each of the modules except `PropEq` are designed to be opened with a
  -- module parameter. This is to avoid having to specify the underlying
  -- equality relation or the decidability proofs every time you use the
  -- list equality.

  -- In our example function equality is not decidable and not propositional
  -- and so we want to use the `SetoidEq` module. This requires a proof that
  -- the `_≗_` relation forms a setoid over functions of the type `ℕ → ℕ`.
  -- This is found in:

  open import Relation.Binary.PropositionalEquality using (_→-setoid_)

  -- The `SetoidEq` module should therefore be opened as follows:

  open SetoidEq (ℕ →-setoid ℕ)

  -- All four equality modules provide an infix operator `_≋_` for the
  -- new equality relation over lists. The type of `lem₃` can therefore
  -- be rewritten as:

  lem₄ : (λ x → x + 1) ∷ [] ≋ (λ x → x + 2 ∸ 1) ∷ []
  lem₄ = 2x+2≗2[x+1] ∷ []
    where
    2x+2≗2[x+1] : (λ x → x + 1) ≗ (λ x → x + 2 ∸ 1)
    2x+2≗2[x+1] x = sym (+-∸-assoc x (s≤s z≤n))

  -- The modules also provide proofs that the `_≋_` relation is a
  -- setoid in its own right and therefore is reflexive, symmetric,
  -- transitive:

  lem₅ : (λ x → 2 * x + 2) ∷ [] ≋ (λ x → 2 * x + 2) ∷ []
  lem₅ = ≋-refl

  -- If we could prove that `_≗_` forms a `DecSetoid` then we could use
  -- the module `DecSetoidEq` instead. This exports everything from
  -- `SetoidEq` as well as the additional proof `_≋?_` that the list
  -- equality is decidable.

  -- This pattern of four modules for each of the four different types
  -- of equality is repeated throughout the library (e.g. see the
  -- `Membership` subheading below). Note that in this case the modules
  -- `PropEq` and `DecPropEq` are not very useful as if two lists are
  -- pointwise propositionally equal they are necessarily
  -- propositionally equal (and vice-versa). There are proofs of this
  -- fact exported by `PropEq` and `DecPropEq`. Although, these two
  -- types of list equality are not very useful in practice, they are
  -- included for completeness's sake.

------------------------------------------------------------------------
-- Permutations

module PermutationExplanation where

  -- Alternatively you might consider two lists to be equal if they
  -- contain the same elements regardless of the order of the elements.
  -- This is known as either "set equality" or a "permutation".

  -- The easiest-to-use formalisation of this relation is found in the
  -- module:

  open import Data.List.Relation.Binary.Permutation.Inductive

  -- The permutation relation is written as `_↭_` and has four
  -- constructors. The first `refl` says that a list is always
  -- a permutation of itself, the second `prep` says that if the
  -- heads of the lists are the same they can be skipped, the third
  -- `swap` says that the first two elements of the lists can be
  -- swapped and the fourth `trans` says that permutation proofs
  -- can be chained transitively.

  -- For example a proof that two lists are a permutation of one
  -- another can be written as follows:

  lem₁ : 1 ∷ 2 ∷ 3 ∷ [] ↭ 3 ∷ 1 ∷ 2 ∷ []
  lem₁ = trans (prep 1 (swap 2 3 refl)) (swap 1 3 refl)

  -- In practice it is difficult to parse the constructors in the
  -- proof above and hence understand why it holds. The
  -- `PermutationReasoning` module can be used to write this proof
  -- in a much more readable form:

  open PermutationReasoning

  lem₂ : 1 ∷ 2 ∷ 3 ∷ [] ↭ 3 ∷ 1 ∷ 2 ∷ []
  lem₂ = begin
    1 ∷ 2 ∷ 3 ∷ []  ↭⟨ prep 1 (swap 2 3 refl) ⟩
    1 ∷ 3 ∷ 2 ∷ []  ↭⟨ swap 1 3 refl ⟩
    3 ∷ 1 ∷ 2 ∷ []  ∎

  -- As might be expected, properties of the permutation relation may be
  -- found in `Data.List.Relation.Binary.Permutation.Inductive.Properties`.

  open import Data.List.Relation.Binary.Permutation.Inductive.Properties

  lem₃ : ∀ {xs ys : List ℕ} → xs ↭ ys → map fromNat xs ↭ map fromNat ys
  lem₃ = map⁺ fromNat

  lem₄ : IsCommutativeMonoid {A = List ℕ} _↭_ _++_ []
  lem₄ = ++-isCommutativeMonoid

  -- Note: at the moment permutations have only been formalised for
  -- propositional equality. Permutations for the other three types of
  -- equality (decidable propositional, setoid and decidable setoid)
  -- will hopefully be added in later versions of the library.

------------------------------------------------------------------------
-- Other relations

-- There exist many other binary relations in the
-- `Data.List.Relation.Binary` folder, including:
--    1. lexicographic orderings
--    2. bag/multiset equality
--    3. the subset relations.
--    4. the sublist relations

------------------------------------------------------------------------
-- 3. Properties of lists
------------------------------------------------------------------------

-- Whereas binary relations deal with how two lists relate to one
-- another, the unary relations in `Data.List.Relation.Unary` are used
-- to reason about the properties of an individual list.

------------------------------------------------------------------------
-- Any

module AnyExplanation where

  -- The predicate `Any` encodes the idea of at least one element of a
  -- given list satisfying a given property (or more formally a
  -- predicate, see the `Pred` type in `Relation.Unary`).

  open import Data.List.Relation.Unary.Any as Any

  -- A proof of type Any consists of a sequence of the "there"
  -- constructors, which says that the element lies in the remainder of
  -- the list, followed by a single "here" constructor which indicates
  -- that the head of the list satisfies the predicate and takes a proof
  -- that it does so.

  -- For example a proof that a given list of natural numbers contains
  -- at least one number greater than or equal to 4 can be written as
  -- follows:

  lem₁ : Any (4 ≤_) (3 ∷ 5 ∷ 1 ∷ 6 ∷ [])
  lem₁ = there (here 4≤5)
    where
    4≤5 = s≤s (s≤s (s≤s (s≤s z≤n)))

  -- Note that nothing requires that the proof of `Any` points at the
  -- first such element in the list. There is therefore an alternative
  -- proof for the above lemma which points to 6 instead of 5.

  lem₂ : Any (4 ≤_) (3 ∷ 5 ∷ 1 ∷ 6 ∷ [])
  lem₂ = there (there (there (here 4≤6)))
    where
    4≤6 = s≤s (s≤s (s≤s (s≤s z≤n)))

  -- There also exist various operations over proofs of `Any` whose names
  -- shadow the corresponding list operation. The standard way of using
  -- these is to use `as` to name the module:

  import Data.List.Relation.Unary.Any as Any

  -- and then use the qualified name `Any.map`. For example, map can
  -- be used to change the predicate of `Any`:

  open import Data.Nat.Properties using (≤-trans; n≤1+n)

  lem₃ : Any (3 ≤_) (3 ∷ 5 ∷ 1 ∷ 6 ∷ [])
  lem₃ = Any.map 4≤x⇒3≤x lem₂
    where
    4≤x⇒3≤x : ∀ {x} → 4 ≤ x → 3 ≤ x
    4≤x⇒3≤x = ≤-trans (n≤1+n 3)

------------------------------------------------------------------------
-- All

module AllExplanation where

  -- The dual to `Any` is the predicate `All` which encodes the idea that
  -- every element in a given list satisfies a given property.

  open import Data.List.Relation.Unary.All

  -- Proofs for `All` are constructed using exactly the same syntax as
  -- is used to construct lists ("[]" & "_∷_"). For example to prove
  -- that every element in a list is less than or equal to one:

  lem₁ : All (_≤ 1) (1 ∷ 0 ∷ 1 ∷ [])
  lem₁ = 1≤1 ∷ 0≤1 ∷ 1≤1 ∷ []
    where
    0≤1 = z≤n
    1≤1 = s≤s z≤n

  -- As with `Any`, the module also provides the standard operators
  -- `map`, `zip` etc. to manipulate proofs for `All`.

  import Data.List.Relation.Unary.All as All
  open import Data.Nat.Properties using (≤-trans; n≤1+n)

  lem₂ : All (_≤ 2) (1 ∷ 0 ∷ 1 ∷ [])
  lem₂ = All.map ≤1⇒≤2 lem₁
    where
    ≤1⇒≤2 : ∀ {x} → x ≤ 1 → x ≤ 2
    ≤1⇒≤2 x≤1 = ≤-trans x≤1 (n≤1+n 1)

------------------------------------------------------------------------
-- Membership

module MembershipExplanation where

  -- Membership of a list is simply a special case of `Any` where
  -- `x ∈ xs` is defined as `Any (x ≈_) xs`.

  -- Just like pointwise equality of lists, the exact membership module
  -- that should be used depends on whether the equality on the
  -- underlying elements of the list is i) propositional or setoid-based
  -- and ii) decidable.

  import Data.List.Membership.Setoid as SetoidMembership
  import Data.List.Membership.DecSetoid as DecSetoidMembership
  import Data.List.Membership.Propositional as PropMembership
  import Data.List.Membership.DecPropositional as DecPropMembership

  -- For example if we want to reason about membership for `List ℕ`
  -- then you would use the `DecSetoidMembership` as we use
  -- propositional equality over `ℕ` and it is also decidable. Therefore
  -- the module `DecPropMembership` should be opened as follows:

  open DecPropMembership NatProp._≟_

  -- As membership is just an instance of `Any` we also need to import
  -- the constructors `here` and `there`. (See issue #553 on Github for
  -- why we're struggling to have `here` and `there` automatically
  -- re-exported by the membership modules).

  open import Data.List.Relation.Unary.Any using (here; there)

  -- These modules provide the infix notation `_∈_` which can be used
  -- as follows:

  lem₁ : 1 ∈ 2 ∷ 1 ∷ 3 ∷ []
  lem₁ = there (here refl)

  -- Properties of the membership relation can be found in the following
  -- two files:

  import Data.List.Membership.Setoid.Properties as SetoidProperties
  import Data.List.Membership.Propositional.Properties as PropProperties

  -- As of yet there are no corresponding files for properties of
  -- membership for decidable versions of setoid and propositional
  -- equality as we have no properties that only hold when equality is
  -- decidable.

  -- These `Properties` modules are NOT parameterised in the same way as
  -- the main membership modules as some of the properties relate
  -- membership proofs for lists of different types. For example in the
  -- following the first `∈` refers to lists of type `List ℕ` whereas
  -- the second `∈` refers to lists of type `List Char`.

  open DecPropMembership CharProp._≟_ renaming (_∈_ to _∈ᶜ_)
  open SetoidProperties using (∈-map⁺)

  lem₂ : {v : ℕ} {xs : List ℕ} → v ∈ xs → fromNat v ∈ᶜ map fromNat xs
  lem₂ = ∈-map⁺ (setoid ℕ) (setoid Char) (cong fromNat)
