------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Binary.Lex.Core where

open import Data.Empty
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Function.Base using (flip)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary hiding (Irrelevant)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation
open import Level using (Level; _⊔_)

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {a ℓ₁ ℓ₂} {A : Set a} (P : Set) (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂) where
  base : (p : P) → Lex P _≈_ _≺_ [] []
  this : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} → (x≺y : x ≺ y) → (m≡n : m ≡ n) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} → (x≈y : x ≈ y) → (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

Lex-mapP : ∀ {a ℓ₁ ℓ₂} {A : Set a} {P₁ P₂ : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} → ∀ {m n} {xs : Vec A m} {ys : Vec A n} → (P₁ → P₂) → Lex P₁ _≈_ _≺_ xs ys → Lex P₂ _≈_ _≺_ xs ys
Lex-mapP f (base p) = base (f p)
Lex-mapP f (this x≺y m≡n) = this x≺y m≡n
Lex-mapP f (next x≈y xs<ys) = next x≈y (Lex-mapP f xs<ys)

-- Properties

module _ {a ℓ₁ ℓ₂} {A : Set a} {P : Set} {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<_ = Lex P _≈_ _≺_

  length-equal : ∀ {m n P} {xs : Vec A m} {ys : Vec A n} → Lex P _≈_ _≺_ xs ys → m ≡ n
  length-equal (base _)         = P.refl
  length-equal (this x≺y m≡n)   = P.cong ℕ.suc m≡n
  length-equal (next x≈y xs<ys) = P.cong ℕ.suc (length-equal xs<ys)

  ¬≤-this : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} → ¬ (x ≈ y) → ¬ (x ≺ y) → ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-this x≉y x≮y (this x≺y m≡n)   = contradiction x≺y x≮y
  ¬≤-this x≉y x≮y (next x≈y xs<ys) = contradiction x≈y x≉y

  ¬≤-next : ∀ {x y m n} {xs : Vec A m} {ys : Vec A n} → ¬ (x ≺ y) → ¬ (xs < ys) → ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-next x≮y xs≮ys (this x≺y m≡n)   = contradiction x≺y x≮y
  ¬≤-next x≮y xs≮ys (next x≈y xs<ys) = contradiction xs<ys xs≮ys

  module _ (≈-equiv : IsPartialEquivalence _≈_) (≺-resp-≈ : _≺_ Respects₂ _≈_) (≺-trans : Transitive _≺_) where
    Lex-trans′ : ∀ {m n o P₂} → Trans (Lex P _≈_ _≺_ {m} {n}) (Lex P₂ _≈_ _≺_ {n} {o}) (Lex (P × P₂) _≈_ _≺_)
    Lex-trans′ (base p₁)        (base p₂)        = base (p₁ , p₂)
    Lex-trans′ (this x≺y m≡n)   (this y≺z n≡o)   = this (≺-trans x≺y y≺z) (P.trans m≡n n≡o)
    Lex-trans′ (this x≺y m≡n)   (next y≈z ys<zs) = this (proj₁ ≺-resp-≈ y≈z x≺y) (P.trans m≡n (length-equal ys<zs))
    Lex-trans′ (next x≈y xs<ys) (this y≺z n≡o)   = this (proj₂ ≺-resp-≈ (IsPartialEquivalence.sym ≈-equiv x≈y) y≺z) (P.trans (length-equal xs<ys) n≡o)
    Lex-trans′ (next x≈y xs<ys) (next y≈z ys<zs) = next (IsPartialEquivalence.trans ≈-equiv x≈y y≈z) (Lex-trans′ xs<ys ys<zs)

    Lex-trans : ∀ {m n o} → Trans (_<_ {m} {n}) (_<_ {n} {o}) _<_
    Lex-trans xs<ys ys<zs = Lex-mapP proj₁ (Lex-trans′ xs<ys ys<zs)

  module _ (≈-sym : Symmetric _≈_) (≺-irrefl : Irreflexive _≈_ _≺_) (≺-asym : Asymmetric _≺_) where
    Lex-antisym : ∀ {n} → Antisymmetric (_≋_ {n}) (_<_)
    Lex-antisym (base _) (base _) = []
    Lex-antisym (this x≺y m≡n) (this y≺x n≡m) = ⊥-elim (≺-asym x≺y y≺x)
    Lex-antisym (this x≺y m≡n) (next y≈x ys<xs) = ⊥-elim (≺-irrefl (≈-sym y≈x) x≺y)
    Lex-antisym (next x≈y xs<ys) (this y≺x m≡n) = ⊥-elim (≺-irrefl (≈-sym x≈y) y≺x)
    Lex-antisym (next x≈y xs<ys) (next y≈x ys<xs) = x≈y ∷ (Lex-antisym xs<ys ys<xs)

  module _ (≈-equiv : IsPartialEquivalence _≈_) (≺-resp-≈ : _≺_ Respectsˡ _≈_) where
    open IsPartialEquivalence ≈-equiv
    Lex-respectsˡ : ∀ {m n} → _Respectsˡ_ (_<_ {m} {n}) (_≋_ {m} {m})
    Lex-respectsˡ []            (base p)         = base p
    Lex-respectsˡ (x≈y ∷ xs≋ys) (this x≺z m≡n)   = this (≺-resp-≈ x≈y x≺z) m≡n
    Lex-respectsˡ (x≈y ∷ xs≋ys) (next x≈z xs<zs) = next (trans (sym x≈y) x≈z) (Lex-respectsˡ xs≋ys xs<zs)

  module _ (≈-equiv : IsPartialEquivalence _≈_) (≺-resp-≈ : _≺_ Respectsʳ _≈_) where
    open IsPartialEquivalence ≈-equiv
    Lex-respectsʳ : ∀ {m n} → _Respectsʳ_ (_<_ {m} {n}) (_≋_ {n} {n})
    Lex-respectsʳ [] (base p)                    = base p
    Lex-respectsʳ (x≈y ∷ xs≋ys) (this x≺z m≡n)   = this (≺-resp-≈ x≈y x≺z) m≡n
    Lex-respectsʳ (x≈y ∷ xs≋ys) (next x≈z xs<zs) = next (trans x≈z x≈y) (Lex-respectsʳ xs≋ys xs<zs)

  Lex-respects₂ : ∀ {n} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → _Respects₂_ (_<_ {n} {n}) (_≋_ {n} {n})
  Lex-respects₂ eq (≺-resp-≈ʳ , ≺-resp-≈ˡ) = Lex-respectsʳ eq ≺-resp-≈ʳ , Lex-respectsˡ eq ≺-resp-≈ˡ

  []<[]-⇔ : P ⇔ [] < []
  []<[]-⇔ = equivalence base (λ { (base p) → p })

  toSum : ∀ {x y n} {xs ys : Vec A n} → (x ∷ xs) < (y ∷ ys) → (x ≺ y ⊎ (x ≈ y × xs < ys))
  toSum (this x≺y m≡n) = inj₁ x≺y
  toSum (next x≈y xs<ys) = inj₂ (x≈y , xs<ys)

  ∷<∷-⇔ : ∀ {x y n} {xs ys : Vec A n} → (x ≺ y ⊎ (x ≈ y × xs < ys)) ⇔ (x ∷ xs) < (y ∷ ys)
  ∷<∷-⇔ = equivalence [ flip this P.refl , uncurry next ] toSum

  module _ (P? : Dec P) (_≈?_ : Decidable _≈_) (_≺?_ : Decidable _≺_) where
    Lex? : ∀ {m n} → Decidable (_<_ {m} {n})
    Lex? {m} {n} xs ys with m Data.Nat.≟ n
    Lex? {_} {_}    []       []    | yes P.refl = Dec.map []<[]-⇔ P?
    Lex? {_} {_} (x ∷ xs) (y ∷ ys) | yes P.refl = Dec.map ∷<∷-⇔ ((x ≺? y) ⊎-dec (x ≈? y) ×-dec (Lex? xs ys))
    Lex? {_} {_}    _        _     | no  m≢n    = no (λ xs<ys → contradiction (length-equal xs<ys) m≢n)

  module _ (≺-irrefl : Irreflexive _≈_ _≺_) (P-irrelevant : Relation.Nullary.Irrelevant P) (≈-irrelevant : Irrelevant _≈_) (≺-irrelevant : Irrelevant _≺_) where
    import Data.Nat.Properties as ℕ
    Lex-irrelevant : ∀ {m n} → Irrelevant (_<_ {m} {n})
    Lex-irrelevant (base p₁)          (base p₂)          rewrite P-irrelevant p₁ p₂                                    = P.refl
    Lex-irrelevant (this x≺y₁ m≡n₁)   (this x≺y₂ m≡n₂)   rewrite ≺-irrelevant x≺y₁ x≺y₂ | ℕ.≡-irrelevant m≡n₁ m≡n₂     = P.refl
    Lex-irrelevant (this x≺y m≡n)     (next x≈y xs<ys₂)                                                                = ⊥-elim (≺-irrefl x≈y x≺y)
    Lex-irrelevant (next x≈y xs<ys₁)  (this x≺y m≡n)                                                                   = ⊥-elim (≺-irrefl x≈y x≺y)
    Lex-irrelevant (next x≈y₁ xs<ys₁) (next x≈y₂ xs<ys₂) rewrite ≈-irrelevant x≈y₁ x≈y₂ | Lex-irrelevant xs<ys₁ xs<ys₂ = P.refl
