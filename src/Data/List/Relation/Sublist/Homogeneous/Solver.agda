------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Sublist.Homogeneous.Solver
       {a r} {A : Set a} (R : Rel A r)
-- Note that we only need this two constraints to define the solver itself.
-- The data structures do not depent on them.
-- However, having the whole module parametrised by them means that we can
-- instantiate them upon import.
       (R-refl : Reflexive R) (R? : Decidable R)
       where

open import Level using (_⊔_)
open import Data.Fin as Fin
open import Data.Maybe as M
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Product
open import Data.Vec as Vec using (Vec ; lookup)
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Data.List.Relation.Sublist.Heterogeneous
open import Data.List.Relation.Sublist.Homogeneous.Properties
open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open ≡-Reasoning

------------------------------------------------------------------------
-- Reified list expressions

-- Basic building blocks: variables and values
data Item (n : ℕ) : Set a where
  var : Fin n → Item n
  val : A → Item n

-- Abstract Syntax Trees
infixr 5 _<>_
data TList (n : ℕ) : Set a where
  It   : Item n → TList n
  _<>_ : TList n → TList n → TList n
  []   : TList n

-- Equivalent linearised representation
RList : ∀ n → Set a
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
data _⊆I_ {n} : (d e : Item n) → Set (a ⊔ r) where
  var : ∀ {k l} → k ≡ l → var k ⊆I var l
  val : ∀ {a b} → R a b → val a ⊆I val b

_⊆T_ : ∀ {n} → (d e : TList n) → Set (a ⊔ r)
d ⊆T e = ∀ ρ → Sublist R (⟦ d ⟧T ρ) (⟦ e ⟧T ρ)

_⊆R_ : ∀ {n} (d e : RList n) → Set (a ⊔ r)
d ⊆R e = ∀ ρ → Sublist R (⟦ d ⟧R ρ) (⟦ e ⟧R ρ)

-- Flattening in a semantics-respecting manner

⟦++⟧R : ∀ {n} xs ys (ρ : Vec (List A) n) → ⟦ xs ++ ys ⟧R ρ ≡ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
⟦++⟧R []       ys ρ = refl
⟦++⟧R (x ∷ xs) ys ρ = begin
  ⟦ x ⟧I ρ ++ ⟦ xs ++ ys ⟧R ρ
    ≡⟨ cong (⟦ x ⟧I ρ ++_) (⟦++⟧R xs ys ρ) ⟩
  ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
    ≡⟨ sym $ ++-assoc (⟦ x ⟧I ρ) (⟦ xs ⟧R ρ) (⟦ ys ⟧R ρ) ⟩
  (⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ) ++ ⟦ ys ⟧R ρ
    ∎

flatten : ∀ {n} (t : TList n) → Σ[ r ∈ RList n ] ⟦ r ⟧R ≗ ⟦ t ⟧T
flatten []       = [] , λ _ → refl
flatten (It it)  = it ∷ [] , λ ρ → ++-identityʳ (⟦ It it ⟧T ρ)
flatten (t <> u) =
  let (rt , eqt) = flatten t
      (ru , equ) = flatten u
  in rt ++ ru , λ ρ → begin
    ⟦ rt ++ ru ⟧R ρ        ≡⟨ ⟦++⟧R rt ru ρ ⟩
    ⟦ rt ⟧R ρ ++ ⟦ ru ⟧R ρ ≡⟨ cong₂ _++_ (eqt ρ) (equ ρ) ⟩
    ⟦ t ⟧T ρ ++ ⟦ u ⟧T ρ   ≡⟨⟩
    ⟦ t <> u ⟧T ρ          ∎

------------------------------------------------------------------------
-- Solver for the sublist problem

-- auxiliary lemmas

private

  keep-it : ∀ {n a b} → a ⊆I b → (xs ys : RList n) → xs ⊆R ys → (a ∷ xs) ⊆R (b ∷ ys)
  keep-it (var refl) xs ys hyp ρ = ++⁺ (Sublist-refl R-refl) (hyp ρ)
  keep-it (val rab)  xs ys hyp ρ = rab ∷ hyp ρ

  skip-it : ∀ {n} it (d e : RList n) → d ⊆R e → d ⊆R (it ∷ e)
  skip-it it d ys hyp ρ = ++ˡ (⟦ it ⟧I ρ) (hyp ρ)

-- Solver for linearised expressions
solveR : ∀ {n} (d e : RList n) → Maybe (d ⊆R e)
-- trivial
solveR []          e           = just (λ ρ → minimum _)
solveR (it ∷ d)    []          = nothing
-- actual work
solveR (var k ∷ d) (var l ∷ e) with k Fin.≟ l
... | yes eq = M.map (keep-it (var eq) d e) (solveR d e)
... | no ¬eq = M.map (skip-it (var l) (var k ∷ d) e) (solveR (var k ∷ d) e)
solveR (val a ∷ d) (val b ∷ e) with R? a b
... | yes rab = M.map (keep-it (val rab) d e) (solveR d e)
... | no ¬rab = M.map (skip-it (val b) (val a ∷ d) e) (solveR (val a ∷ d) e)
solveR d (x ∷ e)               = M.map (skip-it x d e) (solveR d e)

-- Coming back to ASTs thanks to flatten

solveT : ∀ {n} (t u : TList n) → Maybe (t ⊆T u)
solveT t u =
  let (rt , eqt) = flatten t
      (ru , equ) = flatten u
  in case solveR rt ru of λ where
    (just hyp) → just (λ ρ → subst₂ (Sublist R) (eqt ρ) (equ ρ) (hyp ρ))
    nothing    → nothing

-- Prover for ASTs

prove : ∀ {n} (d e : TList n) → From-just (solveT d e)
prove d e = from-just (solveT d e)
