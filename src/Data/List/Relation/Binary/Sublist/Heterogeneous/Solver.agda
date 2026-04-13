------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Decidable)

module Data.List.Relation.Binary.Sublist.Heterogeneous.Solver
  {a r} {A : Set a} (R : Rel A r)
  (R-refl : Reflexive R) (R? : Decidable R)
  where

-- Note that we only need the above two constraints to define the
-- solver itself. The data structures do not depend on them. However,
-- having the whole module parametrised by them means that we can
-- instantiate them upon import.

open import Level using (_⊔_)
open import Data.Fin as Fin
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; From-just; from-just)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Data.Vec.Base as Vec using (Vec ; lookup)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Binary.Sublist.Heterogeneous
  using (Sublist; minimum; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
open import Function.Base using (_$_; case_of_)

open import Relation.Binary.Consequences using (dec⇒weaklyDec)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≗_; sym; cong; cong₂; subst₂)
open import Relation.Binary.PropositionalEquality.Properties as ≡

open ≡.≡-Reasoning

infix 4  _⊆I_ _⊆R_ _⊆T_

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
⟦ var k ⟧I ρ = lookup ρ k
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
⟦++⟧R []       ys ρ = ≡.refl
⟦++⟧R (x ∷ xs) ys ρ = begin
  ⟦ x ⟧I ρ ++ ⟦ xs ++ ys ⟧R ρ
    ≡⟨ cong (⟦ x ⟧I ρ ++_) (⟦++⟧R xs ys ρ) ⟩
  ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
    ≡⟨ sym $ ++-assoc (⟦ x ⟧I ρ) (⟦ xs ⟧R ρ) (⟦ ys ⟧R ρ) ⟩
  (⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ) ++ ⟦ ys ⟧R ρ
    ∎

flatten : ∀ {n} (t : TList n) → Σ[ r ∈ RList n ] ⟦ r ⟧R ≗ ⟦ t ⟧T
flatten []       = [] , λ _ → ≡.refl
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
  keep-it (var a≡b) xs ys hyp ρ = ++⁺ (reflexive R-refl (cong _ a≡b)) (hyp ρ)
  keep-it (val rab) xs ys hyp ρ = rab ∷ hyp ρ

  skip-it : ∀ {n} it (d e : RList n) → d ⊆R e → d ⊆R (it ∷ e)
  skip-it it d ys hyp ρ = ++ˡ (⟦ it ⟧I ρ) (hyp ρ)

-- Solver for items
solveI : ∀ {n} (a b : Item n) → Maybe (a ⊆I b)
solveI (var k) (var l) = Maybe.map var $ dec⇒weaklyDec Fin._≟_ k  l
solveI (val a) (val b) = Maybe.map val $ dec⇒weaklyDec R? a b
solveI _ _ = nothing

-- Solver for linearised expressions
solveR : ∀ {n} (d e : RList n) → Maybe (d ⊆R e)
-- trivial
solveR [] e  = just (λ ρ → minimum _)
solveR d  [] = nothing
-- actual work
solveR (a ∷ d) (b ∷ e) with solveI a b
... | just it = Maybe.map (keep-it it d e) (solveR d e)
... | nothing = Maybe.map (skip-it b (a ∷ d) e) (solveR (a ∷ d) e)

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
