------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of sublist. This commonly known as an Order
-- Preserving Embedding (OPE).
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive.Solver where

open import Data.Nat
open import Data.Fin as Fin
open import Data.Product
open import Data.Vec as Vec using (Vec ; lookup)
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Data.List.Relation.Sublist.Inductive
open import Function
open import Relation.Nullary
import Relation.Binary.PreorderReasoning as PO-Reasoning
module ⊆-Reasoning {a} (A : Set a) = PO-Reasoning (⊆-preorder A)
open import Relation.Binary.PropositionalEquality hiding ([_])

------------------------------------------------------------------------
-- Reified list expressions

-- Basic building blocks: variables and values
data Item {a} (n : ℕ) (A : Set a) : Set a where
  var : Fin n → Item n A
  val : A → Item n A

-- Trees
infixr 5 _<>_
data TList {a} (n : ℕ) (A : Set a) : Set a where
  It   : Item n A → TList n A
  _<>_ : TList n A → TList n A → TList n A
  []   : TList n A

-- Linearised
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
  ⟦ x ∷ [] ⟧R ρ = ⟦ x ⟧I ρ
  ⟦ x ∷ xs ⟧R ρ = ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ

-- Orders
  _⊆T_ : (d e : TList n A) → Set a
  d ⊆T e = ∀ ρ → ⟦ d ⟧T ρ ⊆ ⟦ e ⟧T ρ

  _⊆R_ : (d e : RList n A) → Set a
  d ⊆R e = ∀ ρ → ⟦ d ⟧R ρ ⊆ ⟦ e ⟧R ρ

-- Flattening

  open ≡-Reasoning

  ⟦++⟧R : ∀ xs ys ρ → ⟦ xs ++ ys ⟧R ρ ≡ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
  ⟦++⟧R []               ys         ρ = refl
  ⟦++⟧R (x ∷ [])         []         ρ = sym (++-identityʳ (⟦ x ⟧I ρ))
  ⟦++⟧R (x ∷ [])         ys@(_ ∷ _) ρ = refl
  ⟦++⟧R (x ∷ xs@(_ ∷ _)) ys         ρ = begin
    ⟦ x ⟧I ρ ++ ⟦ xs ++ ys ⟧R ρ
      ≡⟨ cong (⟦ x ⟧I ρ ++_) (⟦++⟧R xs ys ρ) ⟩
    ⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ ++ ⟦ ys ⟧R ρ
      ≡⟨ sym $ ++-assoc (⟦ x ⟧I ρ) (⟦ xs ⟧R ρ) (⟦ ys ⟧R ρ) ⟩
    (⟦ x ⟧I ρ ++ ⟦ xs ⟧R ρ) ++ ⟦ ys ⟧R ρ
      ∎

  flatten : ∀ (t : TList n A) → Σ[ r ∈ RList n A ] (∀ ρ → ⟦ t ⟧T ρ ≡ ⟦ r ⟧R ρ)
  flatten []       = [] , λ _ → refl
  flatten (It it)  = it ∷ [] , λ _ → refl
  flatten (t <> u) =
    let (rt , eqt) = flatten t
        (ru , equ) = flatten u
    in rt ++ ru , λ ρ → begin
      ⟦ t <> u ⟧T ρ          ≡⟨⟩
      ⟦ t ⟧T ρ ++ ⟦ u ⟧T ρ   ≡⟨ cong₂ _++_ (eqt ρ) (equ ρ) ⟩
      ⟦ rt ⟧R ρ ++ ⟦ ru ⟧R ρ ≡⟨ sym $ ⟦++⟧R rt ru ρ ⟩
      ⟦ rt ++ ru ⟧R ρ        ∎


open import Data.Maybe as M
open import Relation.Binary

module _ {n : ℕ} {a} {A : Set a} (eq? : Decidable {A = A} _≡_) where

  open ⊆-Reasoning A

  private

    keep-it : ∀ it (xs ys : RList n A) → xs ⊆R ys → (it ∷ xs) ⊆R (it ∷ ys)
    keep-it it []         []         hyp ρ = ⊆-refl
    keep-it it []         ys@(_ ∷ _) hyp ρ = begin
      ⟦ it ⟧I ρ       ≈⟨ sym $ ++-identityʳ _ ⟩
      ⟦ it ⟧I ρ ++ [] ∼⟨ ++⁺ ⊆-refl (hyp ρ) ⟩
      ⟦ it ⟧I ρ ++ ⟦ ys ⟧R ρ ∎
    keep-it it xs@(_ ∷ _) []         hyp ρ = begin
      ⟦ it ⟧I ρ ++ ⟦ xs ⟧R ρ ∼⟨ ++⁺ ⊆-refl (hyp ρ) ⟩
      ⟦ it ⟧I ρ ++ []        ≈⟨ ++-identityʳ _ ⟩
      ⟦ it ⟧I ρ              ∎
    keep-it it (_ ∷ _)    (_ ∷ _)    hyp ρ = ++⁺ ⊆-refl (hyp ρ)

    skip-it : ∀ it (d e : RList n A) → d ⊆R e → d ⊆R (it ∷ e)
    skip-it it d []         hyp ρ = ⊆-trans (hyp ρ) ([]⊆ _)
    skip-it it d ys@(_ ∷ _) hyp ρ = skips _ (hyp ρ)

  solveR : (d e : RList n A) → Maybe (d ⊆R e)
  solveR []          e           = just (λ ρ → []⊆ ⟦ e ⟧R ρ)
  solveR (it ∷ d)    []          = nothing

  solveR (var k ∷ d) (var l ∷ e) with k Fin.≟ l
  ... | yes refl = M.map (keep-it (var k) d e) (solveR d e)
  ... | no ¬eq   = M.map (skip-it (var l) (var k ∷ d) e) (solveR (var k ∷ d) e)
  solveR (val a ∷ d) (val b ∷ e) with eq? a b
  ... | yes refl = M.map (keep-it (val a) d e) (solveR d e)
  ... | no ¬eq   = M.map (skip-it (val b) (val a ∷ d) e) (solveR (val a ∷ d) e)
  solveR d (x ∷ e)               = M.map (skip-it x d e) (solveR d e)

  solveT : (t u : TList n A) → Maybe (t ⊆T u)
  solveT t u =
    let (rt , eqt) = flatten t
        (ru , equ) = flatten u
    in case solveR rt ru of λ where
      (just hyp) → just (λ ρ → subst₂ _⊆_ (sym (eqt ρ)) (sym (equ ρ)) (hyp ρ))
      nothing    → nothing

  prove : ∀ d e → From-just (solveT d e)
  prove d e = from-just (solveT d e)

open import Data.Nat as Nat

_ : ∀ xs ys → xs ++ xs ⊆ (xs ++ 2 ∷ ys) ++ xs
_ = λ xs ys →
    let `xs = It (var zero)
        `ys = It (var (suc zero))
    in prove Nat._≟_ (`xs <> `xs) ((`xs <> It (val 2) <> `ys) <> `xs)
                     (Vec.fromList (xs ∷ ys ∷ []))
