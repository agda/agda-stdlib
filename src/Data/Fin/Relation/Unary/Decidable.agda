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
open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; s≤s; z≤n; z<s; s<s; s<s⁻¹; _∸_; _^_)
import Data.Nat.Properties as ℕ
open import Data.Product.Base as Product
  using (∃; ∃-syntax; ∃₂; _×_; _,_; map; proj₁; proj₂; uncurry; <_,_>)
open import Data.Product.Properties using (,-injective)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Sum.Properties using ([,]-map; [,]-∘)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Function.Base using (_∘_; id; _$_; flip; const; _$-; λ-)
open import Function.Bundles using (Injection; _↣_; _⇔_; _↔_; mk⇔; mk↔ₛ′)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_)
open import Relation.Nullary.Decidable as Dec
  using (Dec; _because_; yes; no; _×-dec_; _⊎-dec_; map′)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Unary as U
  using (U; Pred; Decidable; _⊆_; Satisfiable; Universal)
open import Relation.Unary.Properties using (U?)

private
  variable
    f p q : Level
    m n o : ℕ
    i j : Fin n
    P : Pred (Fin n) p
    Q : Pred (Fin n) q


------------------------------------------------------------------------
-- Quantification
------------------------------------------------------------------------

module _ {P : Pred (Fin (suc n)) p} where

  ∀-cons : P zero → Π[ P ∘ suc ] → Π[ P ]
  ∀-cons z s zero    = z
  ∀-cons z s (suc i) = s i

  ∀-cons-⇔ : (P zero × Π[ P ∘ suc ]) ⇔ Π[ P ]
  ∀-cons-⇔ = mk⇔ (uncurry ∀-cons) < _$ zero , _∘ suc >

  ∃-here : P zero → ∃⟨ P ⟩
  ∃-here = zero ,_

  ∃-there : ∃⟨ P ∘ suc ⟩ → ∃⟨ P ⟩
  ∃-there = map suc id

  ∃-toSum : ∃⟨ P ⟩ → P zero ⊎ ∃⟨ P ∘ suc ⟩
  ∃-toSum ( zero , P₀ ) = inj₁ P₀
  ∃-toSum (suc f , P₁₊) = inj₂ (f , P₁₊)

  ⊎⇔∃ : (P zero ⊎ ∃⟨ P ∘ suc ⟩) ⇔ ∃⟨ P ⟩
  ⊎⇔∃ = mk⇔ [ ∃-here , ∃-there ] ∃-toSum

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
  ... | false because [¬Q0] = let ¬q₀ = invert [¬Q0] in
    map′ (cons (flip contradiction ¬q₀)) Q⊆P⇒Q∘suc⊆P∘suc ih
  ... | true  because  [Q0] = let q₀ = invert [Q0] in
    map′ (uncurry (cons ∘ const)) < _$ q₀ , Q⊆P⇒Q∘suc⊆P∘suc > (P? q₀ ×-dec ih)

any? : Decidable P → Dec (∃ P)
any? {zero}  P? = no λ { (() , _) }
any? {suc _} P? = Dec.map ⊎⇔∃ (P? zero ⊎-dec any? (P? ∘ suc))

all? : Decidable P → Dec (∀ f → P f)
all? {zero}  P? = yes λ()
all? {suc _} P? = Dec.map ∀-cons-⇔ (P? zero ×-dec all? (P? ∘ suc))

Universal< : Pred (Fin n) p → Pred (Fin n) p
Universal< P i = (j : Fin′ i) → P (inject j)

syntax Universal< (λ j → P) i = ∀[ j < i ] P

ExistsMinimalCounterexample : (P : Pred (Fin n) p) → Set p
ExistsMinimalCounterexample P = ∃[ i ] ¬ P i × ∀[ j < i ] P j

syntax ExistsMinimalCounterexample P = μ⟨¬ P ⟩

min? : ∀ {P : Pred (Fin n) p} → Decidable P → Π[ P ] ⊎ μ⟨¬ P ⟩
min? {n = zero}  {P = _} P? = inj₁ λ()
min? {n = suc n} {P = P} P? with P? zero
... | no ¬p₀ = inj₂ (_ , ¬p₀ , λ())
... | yes p₀ = Sum.map (∀-cons p₀) μ⁺ (min? (P? ∘ suc))
  where
  μ⁺ : μ⟨¬ P ∘ suc ⟩ → μ⟨¬ P ⟩
  μ⁺ (i , ¬pᵢ , Π<[P∘suc]) = suc i , ¬pᵢ , ∀-cons p₀ Π<[P∘suc]

private
  -- A nice computational property of `all?`:
  -- The boolean component of the result is exactly the
  -- obvious fold of boolean tests (`foldr _∧_ true`).
  note : ∀ {P : Pred (Fin 3) p} (P? : Decidable P) →
         ∃ λ z → Dec.does (all? P?) ≡ z
  note P? = Dec.does (P? 0F) ∧ Dec.does (P? 1F) ∧ Dec.does (P? 2F) ∧ true
          , refl

-- If a decidable predicate P over a finite set is sometimes false,
-- then we can find the smallest value for which this is the case.

¬∀⟶∃¬-smallest : ∀ n (P : Pred (Fin n) p) → Decidable P →
                 ¬ (∀ i → P i) → ExistsMinimalCounterexample P
¬∀⟶∃¬-smallest _ _ P? ¬∀[i]P = [ flip contradiction ¬∀[i]P , id ] $ min? P?

-- When P is a decidable predicate over a finite set the following
-- lemma can be proved.

¬∀⟶∃¬ : ∀ n (P : Pred (Fin n) p) → Decidable P →
          ¬ (∀ i → P i) → (∃ λ i → ¬ P i)
¬∀⟶∃¬ n P P? ¬P = map id proj₁ (¬∀⟶∃¬-smallest n P P? ¬P)


------------------------------------------------------------------------
-- Effectful
------------------------------------------------------------------------

module _ {F : Set f → Set f} (RA : RawApplicative F) where

  open RawApplicative RA

  sequence : ∀ {P : Pred (Fin n) f} →
             (∀ i → F (P i)) → F (∀ i → P i)
  sequence {n = zero}  ∀iPi = pure λ()
  sequence {n = suc _} ∀iPi = ∀-cons <$> ∀iPi zero <*> sequence (∀iPi ∘ suc)

module _ {F : Set f → Set f} (RF : RawFunctor F) where

  open RawFunctor RF

  sequence⁻¹ : ∀ {A : Set f} {P : Pred A f} →
               F (∀ i → P i) → (∀ i → F (P i))
  sequence⁻¹ F∀iPi i = (λ f → f i) <$> F∀iPi

