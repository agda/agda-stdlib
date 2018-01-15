module Data.Fin.Vec where

open import Relation.Binary.PropositionalEquality
  as P using (_≡_; _→-setoid_; _≗_)
open import Relation.Binary using (Setoid)

open import Function using (_∘_)
open import Function.Inverse using (Inverse; _↔_)

private
  module List where
    open import Data.List.Properties public
    open import Data.List public
open List using (List; _∷_; [])
open import Data.Product as Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ)
open import Data.Bool using (true; false; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Fin
open import Data.Fin.Properties using (_≟_)

Vec : ∀ {a} (A : Set a) → ℕ → Set a
Vec A n = Fin n → A

module _ {a} {A : Set a} where

  Vec-setoid : ∀ n → Setoid _ _
  Vec-setoid n = Fin n →-setoid A

--------------------------------------------------------------------------------
--  List conversion
--------------------------------------------------------------------------------

  toList : ∀ {n} → Vec A n → List A
  toList {ℕ.zero} f = []
  toList {ℕ.suc n} f = f zero ∷ toList (f ∘ suc)

  fromList : (xs : List A) → Vec A (List.length xs)
  fromList [] ()
  fromList (x ∷ xs) zero = x
  fromList (x ∷ xs) (suc i) = fromList xs i

  private
    toList-cong : ∀ {n} {f g : Vec A n} → f ≗ g → toList f ≡ toList g
    toList-cong {ℕ.zero} p = P.refl
    toList-cong {ℕ.suc n} p = P.cong₂ _∷_ (p zero) (toList-cong (p ∘ suc))

    liftInj :
      ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : Set b}
      {k : A′ → A} → (∀ x → ∃ λ y → x ≡ k y)
      → {f g : A → B} → (f ∘ k) ≗ (g ∘ k) → f ≗ g
    liftInj k-admissible p x with k-admissible x
    liftInj k-admissible p ._ | y , P.refl = p y

    liftPseudoInj :
      ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : Set b}
      {k : A′ → A} {z : A} → (∀ x → x ≡ z ⊎ ∃ λ y → x ≡ k y)
      → {f g : A → B} → f z ≡ g z → (f ∘ k) ≗ (g ∘ k) → f ≗ g
    liftPseudoInj {k = k} {z} k-admissible p q = liftInj k′-admissible (maybe q p)
      where
        k′-admissible : ∀ x → ∃ λ y → x ≡ maybe k z y
        k′-admissible x with k-admissible x
        k′-admissible x | inj₁ r = nothing , r
        k′-admissible x | inj₂ (y , r) = just y , r

    liftPseudoInjOver :
      ∀ {i p a} {I : Set i} {P : I → Set p} {A : Set a}
        {h : I → I} {k : ∀ {i} → P i → P (h i)} {z : ∀ {i} → P (h i)}
        {i j : I} {f : P (h i) → A} {g : P (h j) → A}
      → (∀ {i} (x : P (h i)) → x ≡ z ⊎ ∃ λ y → x ≡ k y) → f z ≡ g z
      → OverΣ (λ {x} → _≗_ {A = P x}) (i , f ∘ k) (j , g ∘ k) → OverΣ (λ {x} → _≗_ {A = P x}) (h i , f) (h j , g)
    liftPseudoInjOver k-admissible p (P.refl , q) = P.refl , liftPseudoInj k-admissible p q

    fromList′ : List A → ∃ (Vec A)
    fromList′ = λ xs → List.length xs , fromList xs

    toList′ : ∃ (Vec A) → List A
    toList′ = toList ∘ proj₂

    fromList′-toList : ∀ {n} (f : Vec A n) → OverΣ _≗_ (fromList′ (toList f)) (n , f)
    fromList′-toList {ℕ.zero} f = P.refl , λ ()
    fromList′-toList {ℕ.suc n} f = liftPseudoInjOver decideFin P.refl (fromList′-toList (f ∘ suc))
      where
        decideFin : ∀ {n} (i : Fin (ℕ.suc n)) → i ≡ zero ⊎ ∃ λ j → i ≡ suc j
        decideFin zero = inj₁ P.refl
        decideFin (suc i) = inj₂ (i , P.refl)

    fromList′-toList′ : (x : ∃ (Vec A)) → OverΣ _≗_ (fromList′ (toList′ x)) x
    fromList′-toList′ (_ , f) = fromList′-toList f

    toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
    toList-fromList [] = P.refl
    toList-fromList (x ∷ xs) = P.cong₂ _∷_ P.refl (toList-fromList xs)

  -- Isomorphism between vectors with existential length and lists.
  ↔List : Inverse (OverΣ.setoid Vec-setoid) (P.setoid (List A))
  ↔List = record
    { to = record
      { _⟨$⟩_ = toList′
      ; cong = λ {(P.refl , p) → toList-cong p}
      }
    ; from = record
      { _⟨$⟩_ = fromList′
      ; cong = λ {P.refl → P.refl , λ _ → P.refl}
      }
    ; inverse-of = record
      { left-inverse-of = fromList′-toList′
      ; right-inverse-of = toList-fromList
      }
    }

  coerceLength : ∀ {m n} → m ≡ n → Vec A m → Vec A n
  coerceLength P.refl f = f

  coerceLength-correct : ∀ {m n} {f} (p : m ≡ n) → OverΣ _≗_ (m , f) (n , coerceLength p f)
  coerceLength-correct P.refl = P.refl , λ _ → P.refl

--------------------------------------------------------------------------------
--  Select
--------------------------------------------------------------------------------

  -- Picks a single value out of the vector and sets all other values to the
  -- given default.
  select : ∀ {n} → A → Fin n → Vec A n → Vec A n
  select z i f j = if ⌊ j ≟ i ⌋ then f i else z

  -- Selecting from any function is the same as selecting from a constant function.
  select-const : ∀ {n} z (i : Fin n) f j → select z i f j ≡ select z i (λ _ → f i) j
  select-const z i f j with ⌊ j ≟ i ⌋
  select-const z i f j | true = P.refl
  select-const z i f j | false = P.refl
