------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing how the Function.Reasoning module
-- can be used to perform "functional reasoning" similar to what is being
-- described in: https://stackoverflow.com/q/22676703/3168666
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module README.Function.Reasoning where

-- Function.Reasoning exports a flipped application (_|>_) combinator
-- as well as a type annotation (_∶_) combinator.

open import Function.Reasoning

------------------------------------------------------------------------
-- A simple example

module _ {A B C : Set} {A→B : A → B} {B→C : B → C} where

-- Using the combinators we can, starting from a value, chain various
-- functions whilst tracking the types of the intermediate results.

  A→C : A → C
  A→C a =
       a    ∶ A
    |> A→B  ∶ B
    |> B→C  ∶ C

------------------------------------------------------------------------
-- A more concrete example

open import Data.Nat
open import Data.List.Base
open import Data.Char.Base
open import Data.String using (String; toList; fromList; _==_)
open import Function
open import Data.Bool hiding (_≤?_)
open import Data.Product as P using (_×_; <_,_>; uncurry; proj₁)
open import Agda.Builtin.Equality

-- This can give us for instance this decomposition of a function
-- collecting all of the substrings of the input which happen to be
-- palindromes:

subpalindromes : String → List String
subpalindromes str = let Chars = List Char in
     str                                   ∶ String
  -- first generate the substrings
  |> toList                                ∶ Chars
  |> inits                                 ∶ List Chars
  |> concatMap tails                       ∶ List Chars
  -- then only keeps the ones which are not singletons
  |> filter (λ cs → 2 ≤? length cs)        ∶ List Chars
  -- only keep the ones that are palindromes
  |> map < fromList , fromList ∘ reverse > ∶ List (String × String)
  |> boolFilter (uncurry _==_)             ∶ List (String × String)
  |> map proj₁                             ∶ List String

-- Test cases

_ : subpalindromes "doctoresreverse" ≡ "eve" ∷ "rever" ∷ "srevers" ∷ "esreverse" ∷ []
_ = refl

_ : subpalindromes "elle-meme" ≡ "ll" ∷ "elle" ∷ "mem" ∷ "eme" ∷ []
_ = refl



-- Example of using ≗-Reasoning
module _ where

  open import Data.Sum
  open import Data.Sum.Properties
  open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)

  variable
    A B C D E F : Set

  -- Use scenario:
  -- a ∘ b ∘ c ∘ d ∘ e ∘ f ∘ g    ≈⟨ a ∘ b ∘ c ∘> d≗d′ ∘ e ⟩∘⟨ f≗f′ ∘ g ⟩
  -- a ∘ b ∘ c ∘ d′ ∘ e ∘ f′ ∘ g    ≈⟨...
  --
  -- The above step performs 2 substitutions simultaneously by using the ⟩∘⟨
  -- divider (which can be used as many times as one wants to perform any
  -- number of substitutions).
  -- Thanks to the properties of function composition, it is very easy to
  -- specify a substitution in a long string of compositions. All one has to do
  -- is list the terms in the composition chain as they appear to the left
  -- of the equal sign but replace the function in question with a proof that
  -- it is ≗ to some other one and replace the `∘` before it (if any) by `∘>`.
  -- Note the lack of a need for any bracketing!

  example : ∀ {f g : C → D} {h i : B → C} {j k : A → B} → f ≗ g → h ≗ i → j ≗ k → f ∘ h ∘ j ≗ g ∘ i ∘ k
  example {f = f} {g} {h} {i} {j} {k} fg hi jk = begin
    f ∘ h ∘ j ≈⟨ f ∘> hi ∘ j ⟩
    f ∘ i ∘ j ≈⟨ fg ∘ i ∘ j ⟩
    g ∘ i ∘ j ≈⟨ g ∘ i ∘> jk ⟩
    g ∘ i ∘ k ∎
    where open ≗-Reasoning

  example2 : ∀ {f g : C → D} {h i : B → C} {j k : A → B} → f ≗ g → h ≗ i → j ≗ k → f ∘ h ∘ j ≗ g ∘ i ∘ k
  example2 {f = f} {g} {h} {i} {j} {k} fg hi jk = begin
    f ∘ h ∘ j ≈⟨ fg ⟩∘⟨ hi ⟩∘⟨ jk ⟩
    g ∘ i ∘ k ∎
    where open ≗-Reasoning

  example3 : ∀ {f g : C → D} {h i : A → C} {j k : B → C} → f ≗ g → h ≗ i → j ≗ k → (ab : A ⊎ B) →
             (f ∘ [ h , j ]) ab ≡ [ g ∘ i , g ∘ k ] ab
  example3 {f = f} {g} {h} {i} {j} {k} fg hi jk ab = on ab begin
    f ∘ [ h , j ]     ≈⟨ fg ⟩∘⟨ [ hi , jk ] ⟩
    g ∘ [ i , k ]     ≈⟨ g ∘[,] ⟩
    [ g ∘ i , g ∘ k ] ∎
    where open SumReasoning
