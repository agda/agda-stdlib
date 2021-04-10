------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of same-length vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Binary.Lex.Core {a} {A : Set a} where

open import Data.Empty
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Function.Base using (flip)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong)
open import Relation.Nullary as Nullary hiding (Irrelevant)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation
open import Level using (Level; _⊔_)

private
  variable
    ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Definition

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {A : Set a} (P : Set) (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂)
       : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂) where
  base : (p : P) → Lex P _≈_ _≺_ [] []
  this : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n}
         (x≺y : x ≺ y) (m≡n : m ≡ n) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n}
         (x≈y : x ≈ y) (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Operations

map-P : ∀ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} {P₁ P₂ : Set} → (P₁ → P₂) →
        ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
        Lex P₁ _≈_ _≺_ xs ys → Lex P₂ _≈_ _≺_ xs ys
map-P f (base p)         = base (f p)
map-P f (this x≺y m≡n)   = this x≺y m≡n
map-P f (next x≈y xs<ys) = next x≈y (map-P f xs<ys)

------------------------------------------------------------------------
-- Properties

module _ {P : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  length-equal : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
                 Lex P _≈_ _≺_ xs ys → m ≡ n
  length-equal (base _)         = refl
  length-equal (this x≺y m≡n)   = cong suc m≡n
  length-equal (next x≈y xs<ys) = cong suc (length-equal xs<ys)

module _ {P : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<ₗₑₓ_ = Lex P _≈_ _≺_

  ≰-this : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} →
           ¬ (x ≈ y) → ¬ (x ≺ y) → ¬ (x ∷ xs) <ₗₑₓ (y ∷ ys)
  ≰-this x≉y x≮y (this x≺y m≡n)   = contradiction x≺y x≮y
  ≰-this x≉y x≮y (next x≈y xs<ys) = contradiction x≈y x≉y

  ≰-next : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} →
           ¬ (x ≺ y) → ¬ (xs <ₗₑₓ ys) → ¬ (x ∷ xs) <ₗₑₓ (y ∷ ys)
  ≰-next x≮y xs≮ys (this x≺y m≡n)   = contradiction x≺y x≮y
  ≰-next x≮y xs≮ys (next x≈y xs<ys) = contradiction xs<ys xs≮ys

  P⇔[]<[] : P ⇔ [] <ₗₑₓ []
  P⇔[]<[] = equivalence base (λ { (base p) → p })

  toSum : ∀ {x y n} {xs ys : Vec A n} → (x ∷ xs) <ₗₑₓ (y ∷ ys) → (x ≺ y ⊎ (x ≈ y × xs <ₗₑₓ ys))
  toSum (this x≺y m≡n)   = inj₁ x≺y
  toSum (next x≈y xs<ys) = inj₂ (x≈y , xs<ys)

  ∷<∷-⇔ : ∀ {x y n} {xs ys : Vec A n} → (x ≺ y ⊎ (x ≈ y × xs <ₗₑₓ ys)) ⇔ (x ∷ xs) <ₗₑₓ (y ∷ ys)
  ∷<∷-⇔ = equivalence [ flip this refl , uncurry next ] toSum

  module _ (≈-equiv : IsPartialEquivalence _≈_)
           ((≺-respʳ-≈ , ≺-respˡ-≈) : _≺_ Respects₂ _≈_)
           (≺-trans : Transitive _≺_)
           (open IsPartialEquivalence ≈-equiv)
           where

    transitive′ : ∀ {m n o P₂} → Trans (Lex P _≈_ _≺_ {m} {n}) (Lex P₂ _≈_ _≺_ {n} {o}) (Lex (P × P₂) _≈_ _≺_)
    transitive′ (base p₁)        (base p₂)        = base (p₁ , p₂)
    transitive′ (this x≺y m≡n)   (this y≺z n≡o)   = this (≺-trans x≺y y≺z) (P.trans m≡n n≡o)
    transitive′ (this x≺y m≡n)   (next y≈z ys<zs) = this (≺-respʳ-≈ y≈z x≺y) (P.trans m≡n (length-equal ys<zs))
    transitive′ (next x≈y xs<ys) (this y≺z n≡o)   = this (≺-respˡ-≈ (sym x≈y) y≺z) (P.trans (length-equal xs<ys) n≡o)
    transitive′ (next x≈y xs<ys) (next y≈z ys<zs) = next (trans x≈y y≈z) (transitive′ xs<ys ys<zs)

    transitive : ∀ {m n o} → Trans (_<ₗₑₓ_ {m} {n}) (_<ₗₑₓ_ {n} {o}) _<ₗₑₓ_
    transitive xs<ys ys<zs = map-P proj₁ (transitive′ xs<ys ys<zs)

  module _ (≈-sym : Symmetric _≈_) (≺-irrefl : Irreflexive _≈_ _≺_) (≺-asym : Asymmetric _≺_) where

    antisym : ∀ {n} → Antisymmetric (_≋_ {n}) (_<ₗₑₓ_)
    antisym (base _)         (base _)         = []
    antisym (this x≺y m≡n)   (this y≺x n≡m)   = ⊥-elim (≺-asym x≺y y≺x)
    antisym (this x≺y m≡n)   (next y≈x ys<xs) = ⊥-elim (≺-irrefl (≈-sym y≈x) x≺y)
    antisym (next x≈y xs<ys) (this y≺x m≡n)   = ⊥-elim (≺-irrefl (≈-sym x≈y) y≺x)
    antisym (next x≈y xs<ys) (next y≈x ys<xs) = x≈y ∷ (antisym xs<ys ys<xs)

  module _ (≈-equiv : IsPartialEquivalence _≈_) (open IsPartialEquivalence ≈-equiv) where

    respectsˡ : _≺_ Respectsˡ _≈_ → ∀ {m n} → (_<ₗₑₓ_ {m} {n}) Respectsˡ _≋_
    respectsˡ resp []            (base p)         = base p
    respectsˡ resp (x≈y ∷ xs≋ys) (this x≺z m≡n)   = this (resp x≈y x≺z) m≡n
    respectsˡ resp (x≈y ∷ xs≋ys) (next x≈z xs<zs) = next (trans (sym x≈y) x≈z) (respectsˡ resp xs≋ys xs<zs)

    respectsʳ : _≺_ Respectsʳ _≈_ → ∀ {m n} → (_<ₗₑₓ_ {m} {n}) Respectsʳ _≋_
    respectsʳ resp [] (base p)                    = base p
    respectsʳ resp (x≈y ∷ xs≋ys) (this x≺z m≡n)   = this (resp x≈y x≺z) m≡n
    respectsʳ resp (x≈y ∷ xs≋ys) (next x≈z xs<zs) = next (trans x≈z x≈y) (respectsʳ resp xs≋ys xs<zs)

    respects₂ : _≺_ Respects₂ _≈_ → ∀ {n} → (_<ₗₑₓ_ {n} {n}) Respects₂ _≋_
    respects₂ (≺-resp-≈ʳ , ≺-resp-≈ˡ) = respectsʳ ≺-resp-≈ʳ , respectsˡ ≺-resp-≈ˡ

  module _ (P? : Dec P) (_≈?_ : Decidable _≈_) (_≺?_ : Decidable _≺_) where

    decidable : ∀ {m n} → Decidable (_<ₗₑₓ_ {m} {n})
    decidable {m} {n} xs ys with m Data.Nat.≟ n
    decidable {_} {_} []       []       | yes refl = Dec.map P⇔[]<[] P?
    decidable {_} {_} (x ∷ xs) (y ∷ ys) | yes refl = Dec.map ∷<∷-⇔ ((x ≺? y) ⊎-dec (x ≈? y) ×-dec (decidable xs ys))
    decidable {_} {_} _        _        | no  m≢n    = no (λ xs<ys → contradiction (length-equal xs<ys) m≢n)

  module _ (P-irrel  : Nullary.Irrelevant P)
           (≈-irrel  : Irrelevant _≈_)
           (≺-irrel  : Irrelevant _≺_)
           (≺-irrefl : Irreflexive _≈_ _≺_)
           where

    irrelevant : ∀ {m n} → Irrelevant (_<ₗₑₓ_ {m} {n})
    irrelevant (base p₁)          (base p₂)          rewrite P-irrel p₁ p₂                                = refl
    irrelevant (this x≺y₁ m≡n₁)   (this x≺y₂ m≡n₂)   rewrite ≺-irrel x≺y₁ x≺y₂ | ℕ.≡-irrelevant m≡n₁ m≡n₂ = refl
    irrelevant (this x≺y m≡n)     (next x≈y xs<ys₂)  = contradiction x≺y (≺-irrefl x≈y)
    irrelevant (next x≈y xs<ys₁)  (this x≺y m≡n)     = contradiction x≺y (≺-irrefl x≈y)
    irrelevant (next x≈y₁ xs<ys₁) (next x≈y₂ xs<ys₂) rewrite ≈-irrel x≈y₁ x≈y₂ | irrelevant xs<ys₁ xs<ys₂ = refl

