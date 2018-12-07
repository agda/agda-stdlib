------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.List.Relation.Sublist.Propositional.Solver where

open import Data.Fin as Fin
open import Data.Maybe as M
open import Data.Nat as Nat
open import Data.Product
open import Data.Vec as Vec using (Vec ; lookup)
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Data.List.Relation.Sublist.Propositional hiding (lookup)
open import Data.List.Relation.Sublist.Propositional.Properties
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open ≡-Reasoning

------------------------------------------------------------------------
-- Reified list expressions

-- Basic building blocks: variables and values
data Item {a} (n : ℕ) (A : Set a) : Set a where
  var : Fin n → Item n A
  val : A → Item n A

-- Abstract Syntax Trees
infixr 5 _<>_
data TList {a} (n : ℕ) (A : Set a) : Set a where
  It   : Item n A → TList n A
  _<>_ : TList n A → TList n A → TList n A
  []   : TList n A

-- Equivalent linearised representation
RList : ∀ {a} n → Set a → Set a
RList n A = List (Item n A)

module _ {n a} {A : Set a} where

-- Semantics
  ⟦_⟧I : Item n A → Vec (List A) n → List A
  ⟦ var k ⟧I ρ = lookup k ρ
  ⟦ val a ⟧I ρ = [ a ]

  ⟦_⟧T : TList n A → Vec (List A) n → List A
  ⟦ It it  ⟧T ρ = ⟦ it ⟧I ρ
  ⟦ t <> u ⟧T ρ = ⟦ t ⟧T ρ ++ ⟦ u ⟧T ρ
  ⟦ []     ⟧T ρ = []

  ⟦_⟧R : RList n A → Vec (List A) n → List A
  ⟦ []     ⟧R ρ = []
  ⟦ x ∷ xs ⟧R ρ = ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ

-- Orders
  _⊆T_ : (d e : TList n A) → Set a
  d ⊆T e = ∀ ρ → ⟦ d ⟧T ρ ⊆ ⟦ e ⟧T ρ

  _⊆R_ : (d e : RList n A) → Set a
  d ⊆R e = ∀ ρ → ⟦ d ⟧R ρ ⊆ ⟦ e ⟧R ρ

-- Flattening in a semantics-respecting manner

  ⟦++⟧R : ∀ xs ys ρ → ⟦ xs ++ ys ⟧R ρ ≡ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
  ⟦++⟧R []       ys ρ = refl
  ⟦++⟧R (x ∷ xs) ys ρ = begin
    ⟦ x ⟧I ρ ++ ⟦ xs ++ ys ⟧R ρ
      ≡⟨ cong (⟦ x ⟧I ρ ++_) (⟦++⟧R xs ys ρ) ⟩
    ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
      ≡⟨ sym $ ++-assoc (⟦ x ⟧I ρ) (⟦ xs ⟧R ρ) (⟦ ys ⟧R ρ) ⟩
    (⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ) ++ ⟦ ys ⟧R ρ
      ∎

  flatten : ∀ (t : TList n A) → Σ[ r ∈ RList n A ] ⟦ t ⟧T ≗ ⟦ r ⟧R
  flatten []       = [] , λ _ → refl
  flatten (It it)  = it ∷ [] , λ ρ → sym $ ++-identityʳ (⟦ It it ⟧T ρ)
  flatten (t <> u) =
    let (rt , eqt) = flatten t
        (ru , equ) = flatten u
    in rt ++ ru , λ ρ → begin
      ⟦ t <> u ⟧T ρ          ≡⟨⟩
      ⟦ t ⟧T ρ ++ ⟦ u ⟧T ρ   ≡⟨ cong₂ _++_ (eqt ρ) (equ ρ) ⟩
      ⟦ rt ⟧R ρ ++ ⟦ ru ⟧R ρ ≡⟨ sym $ ⟦++⟧R rt ru ρ ⟩
      ⟦ rt ++ ru ⟧R ρ        ∎

------------------------------------------------------------------------
-- Solver for the sublist problem

module _ {n : ℕ} {a} {A : Set a} (eq? : Decidable {A = A} _≡_) where

-- auxiliary lemmas

  private

    keep-it : ∀ it (xs ys : RList n A) → xs ⊆R ys → (it ∷ xs) ⊆R (it ∷ ys)
    keep-it it xs ys hyp ρ = ++⁺ ⊆-refl (hyp ρ)

    skip-it : ∀ it (d e : RList n A) → d ⊆R e → d ⊆R (it ∷ e)
    skip-it it d ys hyp ρ = skips (⟦ it ⟧I ρ) (hyp ρ)

-- Solver for linearised expressions

  solveR : (d e : RList n A) → Maybe (d ⊆R e)
  -- trivial
  solveR []          e           = just (λ ρ → []⊆ ⟦ e ⟧R ρ)
  solveR (it ∷ d)    []          = nothing
  -- actual work
  solveR (var k ∷ d) (var l ∷ e) with k Fin.≟ l
  ... | yes refl = M.map (keep-it (var k) d e) (solveR d e)
  ... | no ¬eq   = M.map (skip-it (var l) (var k ∷ d) e) (solveR (var k ∷ d) e)
  solveR (val a ∷ d) (val b ∷ e) with eq? a b
  ... | yes refl = M.map (keep-it (val a) d e) (solveR d e)
  ... | no ¬eq   = M.map (skip-it (val b) (val a ∷ d) e) (solveR (val a ∷ d) e)
  solveR d (x ∷ e)               = M.map (skip-it x d e) (solveR d e)

-- Coming back to ASTs thanks to flatten

  solveT : (t u : TList n A) → Maybe (t ⊆T u)
  solveT t u =
    let (rt , eqt) = flatten t
        (ru , equ) = flatten u
    in case solveR rt ru of λ where
      (just hyp) → just (λ ρ → subst₂ _⊆_ (sym (eqt ρ)) (sym (equ ρ)) (hyp ρ))
      nothing    → nothing

-- Prover for ASTs

  prove : ∀ d e → From-just (solveT d e)
  prove d e = from-just (solveT d e)

------------------------------------------------------------------------
-- Test

_ : ∀ xs ys → xs ++ xs ⊆ (xs ++ 2 ∷ ys) ++ xs
_ = λ xs ys →
    let `xs = It (var zero)
        `ys = It (var (suc zero))
    in prove Nat._≟_ (`xs <> `xs) ((`xs <> It (val 2) <> `ys) <> `xs)
                     (Vec.fromList (xs ∷ ys ∷ []))
