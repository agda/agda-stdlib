------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Decidable unary predicates on Fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Relation.Unary.Decidable where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Fin.Relation.Unary.Base
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product.Base as Product
  using (∃; ∃-syntax; _×_; _,_; proj₁; uncurry; <_,_>)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Function.Base using (id; _∘_; _$_; const; flip; _$-; λ-)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; refl)
open import Relation.Nullary.Decidable as Dec
  using (Dec; yes; no; _×-dec_; _⊎-dec_; map′)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Unary as U
  using (Pred; Decidable; _⊆_; Satisfiable; Universal)

private
  variable
    p q : Level
    n : ℕ
    P : Pred (Fin n) p
    Q : Pred (Fin n) q


------------------------------------------------------------------------
-- Quantification

any? : Decidable P → Dec (∃ P)
any? {zero}  P? = no λ { (() , _) }
any? {suc _} P? = Dec.map ⊎⇔∃ (P? zero ⊎-dec any? (P? ∘ suc))

all? : Decidable P → Dec (∀ i → P i)
all? {zero}  P? = yes λ()
all? {suc _} P? = Dec.map ∀-cons-⇔ (P? zero ×-dec all? (P? ∘ suc))

Universal< : Pred (Fin n) p → Pred (Fin n) p
Universal< P i = (j : Fin′ i) → P (inject j)

syntax Universal< (λ j → P) i = ∀[ j < i ] P

ExistsMinimalCounterexample : (P : Pred (Fin n) p) → Set p
ExistsMinimalCounterexample P = ∃[ i ] ¬ P i × ∀[ j < i ] P j

syntax ExistsMinimalCounterexample P = μ⟨¬ P ⟩

searchMin : Decidable P → (∀ i → P i) ⊎ ∃[ i ] ¬ P i × ∀[ j < i ] P j
searchMin {zero}  {P = _} P? = inj₁ λ()
searchMin {suc n} {P = P} P? with P? zero
... | no ¬p₀ = inj₂ (_ , ¬p₀ , λ())
... | yes p₀ = Sum.map (∀-cons p₀) μ⁺ (searchMin (P? ∘ suc))
  where
  μ⁺ : μ⟨¬ P ∘ suc ⟩ → μ⟨¬ P ⟩
  μ⁺ (i , ¬pᵢ , ∀<[P∘suc]) = suc i , ¬pᵢ , ∀-cons p₀ ∀<[P∘suc]

private
  -- A nice computational property of `all?`:
  -- The boolean component of the result is exactly the
  -- obvious fold of boolean tests (`foldr _∧_ true`).
  note : ∀ {P : Pred (Fin 3) p} (P? : Decidable P) →
         ∃ λ z → Dec.does (all? P?) ≡ z
  note P? = Dec.does (P? 0F) ∧ Dec.does (P? 1F) ∧ Dec.does (P? 2F) ∧ true
          , refl

------------------------------------------------------------------------
-- Corollaries to `searchMin`

-- If a decidable predicate P over a finite set is sometimes false,
-- then we can find the smallest value for which this is the case.

¬∀⟶∃¬-smallest : ∀ n (P : Pred (Fin n) p) → Decidable P →
                 ¬ (∀ i → P i) → ExistsMinimalCounterexample P
¬∀⟶∃¬-smallest _ _ P? ¬∀[i]P = [ flip contradiction ¬∀[i]P , id ] $ searchMin P?

-- When P is a decidable predicate over a finite set the following
-- lemma can be proved.

¬∀⟶∃¬ : ∀ n (P : Pred (Fin n) p) → Decidable P →
          ¬ (∀ i → P i) → (∃ λ i → ¬ P i)
¬∀⟶∃¬ n P P? ¬P = Product.map id proj₁ (¬∀⟶∃¬-smallest n P P? ¬P)

------------------------------------------------------------------------
-- Kleisli lifting of Dec over subset relation

decFinSubset : Decidable Q → Q ⊆ Dec ∘ P → Dec (Q ⊆ P)
decFinSubset {zero}  {_}     {_}     Q? P? = yes λ {}
decFinSubset {suc n} {Q = Q} {P = P} Q? P? = dec[Q⊆P]
  module DecFinSubset where

  cons : (Q 0F → P 0F) → (Q ∘ suc ⊆ P ∘ suc) → Q ⊆ P
  cons q₀⊆p₀ f = ∀-cons {P = λ x → Q x → P x} q₀⊆p₀ (λ- f) $-

  ih : Dec (Q ∘ suc ⊆ P ∘ suc)
  ih = decFinSubset (Q? ∘ suc) P?

  Q⊆P⇒Q∘suc⊆P∘suc : Q ⊆ P → Q ∘ suc ⊆ P ∘ suc
  Q⊆P⇒Q∘suc⊆P∘suc f {x} = f {suc x}

  dec[Q⊆P] : Dec (Q ⊆ P)
  dec[Q⊆P] with Q? zero
  ... | no ¬q₀ = map′ (cons (flip contradiction ¬q₀)) Q⊆P⇒Q∘suc⊆P∘suc ih
  ... | yes q₀ = map′ (uncurry (cons ∘ const)) < _$ q₀ , Q⊆P⇒Q∘suc⊆P∘suc > (P? q₀ ×-dec ih)

