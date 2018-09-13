------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other.
------------------------------------------------------------------------

open import Relation.Binary using (Decidable; Setoid)

module Data.List.Relation.Sublist.Inductive.Setoid.Solver
       {c ℓ} (S : Setoid c ℓ) where

open import Data.Fin as Fin
open import Data.Maybe as M
open import Data.Nat as Nat
open import Data.Product
open import Data.Sum
open import Data.Vec as Vec using (Vec ; lookup)
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Function
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PEq

open import Data.Sum.Relation.Pointwise as Sum
open import Data.List.Relation.Equality.Setoid S as ≋
open import Data.List.Relation.Sublist.Inductive.Setoid S hiding (lookup)
open import Data.List.Relation.Sublist.Inductive.Setoid.Properties S as ⊆

open Setoid S renaming (Carrier to A)
import Relation.Binary.EqReasoning as EqReasoning

------------------------------------------------------------------------
-- Reified list expressions

-- Basic building blocks: variables and values
-- We use Sum because it gets handy later on in the definition of `keep-it`:
-- we can reuse the pointwise lifting of relations on Sums.
Item : ℕ → Set c
Item n = Fin n ⊎ A
pattern var k = inj₁ k
pattern val a = inj₂ a

-- Abstract Syntax Trees
infixr 5 _<>_
data TList (n : ℕ) : Set c where
  It   : Item n → TList n
  _<>_ : TList n → TList n → TList n
  []   : TList n

-- Equivalent linearised representation
RList : ℕ → Set c
RList n = List (Item n)

-- Semantics
⟦_⟧I : ∀ {n} → Item n → Vec (List A) n → List A
⟦ var k ⟧I ρ = lookup k ρ
⟦ val a ⟧I ρ = [ a ]

⟦_⟧T : ∀ {n} → TList n → Vec (List A) n → List A
⟦ It it  ⟧T ρ = ⟦ it ⟧I ρ
⟦ t <> u ⟧T ρ = ⟦ t ⟧T ρ ++ ⟦ u ⟧T ρ
⟦ []     ⟧T ρ = []

⟦_⟧R : ∀ {n} → RList n → Vec (List A) n → List A
⟦ []     ⟧R ρ = []
⟦ x ∷ xs ⟧R ρ = ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ

-- Orders
_⊆T_ : ∀ {n} → (d e : TList n) → Set _
d ⊆T e = ∀ ρ → ⟦ d ⟧T ρ ⊆ ⟦ e ⟧T ρ

_⊆R_ : ∀ {n} → (d e : RList n) → Set _
d ⊆R e = ∀ ρ → ⟦ d ⟧R ρ ⊆ ⟦ e ⟧R ρ

-- Flattening in a semantics-respecting manner

⟦++⟧R : ∀ {n} (xs ys : RList n) ρ → ⟦ xs ++ ys ⟧R ρ ≋ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
⟦++⟧R []       ys ρ = ≋-refl
⟦++⟧R (x ∷ xs) ys ρ = begin
  ⟦ x ⟧I ρ ++ ⟦ xs ++ ys ⟧R ρ
    ≈⟨ ≋.++⁺ ≋-refl (⟦++⟧R xs ys ρ) ⟩
  ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
    ≡⟨ PEq.sym $ ++-assoc (⟦ x ⟧I ρ) (⟦ xs ⟧R ρ) (⟦ ys ⟧R ρ) ⟩
  (⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ) ++ ⟦ ys ⟧R ρ
    ∎ where open EqReasoning ≋-setoid

flatten : ∀ {n} (t : TList n) → Σ[ r ∈ RList n ] ∀ ρ → ⟦ t ⟧T ρ ≋ ⟦ r ⟧R ρ
flatten []       = [] , λ _ → ≋-refl
flatten (It it)  = it ∷ [] , λ ρ → ≋-reflexive (PEq.sym $ ++-identityʳ (⟦ It it ⟧T ρ))
flatten (t <> u) =
  let (rt , eqt) = flatten t
      (ru , equ) = flatten u
  in rt ++ ru , λ ρ → begin
    ⟦ t <> u ⟧T ρ          ≡⟨⟩
    ⟦ t ⟧T ρ ++ ⟦ u ⟧T ρ   ≈⟨ ≋.++⁺ (eqt ρ) (equ ρ) ⟩
    ⟦ rt ⟧R ρ ++ ⟦ ru ⟧R ρ ≈⟨ ≋-sym $ ⟦++⟧R rt ru ρ ⟩
    ⟦ rt ++ ru ⟧R ρ        ∎ where open EqReasoning ≋-setoid

------------------------------------------------------------------------
-- Solver for the sublist problem

module _ {n : ℕ} (eq? : Decidable _≈_) where

-- auxiliary lemmas

  private

    keep-it : ∀ {it it′} → Sum.Pointwise PEq._≡_ _≈_ it it′ →
              (xs ys : RList n) → xs ⊆R ys → (it ∷ xs) ⊆R (it′ ∷ ys)
    keep-it (₁∼₂ ())       xs ys hyp ρ
    keep-it (₁∼₁ PEq.refl) xs ys hyp ρ = ⊆.++⁺ ⊆-refl (hyp ρ)
    keep-it (₂∼₂ x≈y)      xs ys hyp ρ = ⊆.++⁺ (keep x≈y base) (hyp ρ)

    skip-it : ∀ it (d e : RList n) → d ⊆R e → d ⊆R (it ∷ e)
    skip-it it d ys hyp ρ = skips (⟦ it ⟧I ρ) (hyp ρ)

-- Solver for linearised expressions

  solveR : (d e : RList n) → Maybe (d ⊆R e)
  -- trivial
  solveR []          e           = just (λ ρ → []⊆ ⟦ e ⟧R ρ)
  solveR (it ∷ d)    []          = nothing
  -- actual work
  solveR (var k ∷ d) (var l ∷ e) with k Fin.≟ l
  ... | yes k≡l = M.map (keep-it (₁∼₁ k≡l) d e) (solveR d e)
  ... | no ¬eq  = M.map (skip-it (var l) (var k ∷ d) e) (solveR (var k ∷ d) e)
  solveR (val a ∷ d) (val b ∷ e) with eq? a b
  ... | yes a≈b = M.map (keep-it (₂∼₂ a≈b) d e) (solveR d e)
  ... | no ¬eq  = M.map (skip-it (val b) (val a ∷ d) e) (solveR (val a ∷ d) e)
  solveR d (x ∷ e)               = M.map (skip-it x d e) (solveR d e)

-- Coming back to ASTs thanks to flatten

  solveT : (t u : TList n) → Maybe (t ⊆T u)
  solveT t u =
    let (rt , eqt) = flatten t
        (ru , equ) = flatten u
    in case solveR rt ru of λ where
      nothing    → nothing
      (just hyp) → just $′ λ ρ → begin
        ⟦ t ⟧T ρ  ≋⟨ eqt ρ ⟩
        ⟦ rt ⟧R ρ ⊆⟨ hyp ρ ⟩
        ⟦ ru ⟧R ρ ≋⟨ ≋-sym (equ ρ) ⟩
        ⟦ u ⟧T ρ  ∎ where open ⊆-Reasoning

-- Prover for ASTs

  prove : ∀ d e → From-just (solveT d e)
  prove d e = from-just (solveT d e)
