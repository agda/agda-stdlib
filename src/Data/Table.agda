module Data.Table where

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

private
  module Vec where
    open import Data.Vec.Properties public
    open import Data.Vec public
open Vec using (Vec; _∷_; [])

open import Data.Product as Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ)
open import Data.Bool using (true; false; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Fin
open import Data.Fin.Properties using (_≟_)

Table : ∀ {a} (A : Set a) → ℕ → Set a
Table A n = Fin n → A

setoid : ∀ {a} → Set a → ℕ → Setoid _ _
setoid A n = Fin n →-setoid A

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

map : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → Table A n → Table B n
map f t = f ∘ t

foldr : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B → B) → B → Table A n → B
foldr {n = ℕ.zero} f z t = z
foldr {n = ℕ.suc n} f z t = f (t zero) (foldr f z (t ∘ suc))

foldl : ∀ {a b} {A : Set a} {B : Set b} {n} → (B → A → B) → B → Table A n → B
foldl {n = ℕ.zero} f z t = z
foldl {n = ℕ.suc n} f z t = foldl f (f z (t zero)) (t ∘ suc)

module _ {a} {A : Set a} where

--------------------------------------------------------------------------------
--  List conversion
--------------------------------------------------------------------------------

  toList : ∀ {n} → Table A n → List A
  toList = List.tabulate

  fromList : (xs : List A) → Table A (List.length xs)
  fromList [] ()
  fromList (x ∷ xs) zero = x
  fromList (x ∷ xs) (suc i) = fromList xs i

  private
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

    fromList′ : List A → ∃ (Table A)
    fromList′ = λ xs → List.length xs , fromList xs

    toList′ : ∃ (Table A) → List A
    toList′ = toList ∘ proj₂

    fromList′-toList : ∀ {n} (f : Table A n) → OverΣ _≗_ (fromList′ (toList f)) (n , f)
    fromList′-toList {ℕ.zero} f = P.refl , λ ()
    fromList′-toList {ℕ.suc n} f = liftPseudoInjOver decideFin P.refl (fromList′-toList (f ∘ suc))
      where
        decideFin : ∀ {n} (i : Fin (ℕ.suc n)) → i ≡ zero ⊎ ∃ λ j → i ≡ suc j
        decideFin zero = inj₁ P.refl
        decideFin (suc i) = inj₂ (i , P.refl)

    fromList′-toList′ : (x : ∃ (Table A)) → OverΣ _≗_ (fromList′ (toList′ x)) x
    fromList′-toList′ (_ , f) = fromList′-toList f

    toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
    toList-fromList [] = P.refl
    toList-fromList (x ∷ xs) = P.cong₂ _∷_ P.refl (toList-fromList xs)

    fromVec : ∀ {n} → Vec A n → Table A n
    fromVec [] = λ ()
    fromVec (x ∷ xs) zero = x
    fromVec (x ∷ xs) (suc i) = fromVec xs i

    toVec : ∀ {n} → Table A n → Vec A n
    toVec = Vec.tabulate

    fromVec-toVec : ∀ {n} (t : Table A n) → fromVec (toVec t) ≗ t
    fromVec-toVec {ℕ.zero} t = λ ()
    fromVec-toVec {ℕ.suc n} t zero = P.refl
    fromVec-toVec {ℕ.suc n} t (suc i) = fromVec-toVec (t ∘ suc) i

    toVec-fromVec : ∀ {n} (v : Vec A n) → toVec (fromVec v) ≡ v
    toVec-fromVec [] = P.refl
    toVec-fromVec (x ∷ v) = P.cong₂ _∷_ P.refl (toVec-fromVec v)

  -- Isomorphism between tables and vectors.
  ↔Vec : ∀ {n} → Inverse (setoid A n) (P.setoid (Vec A n))
  ↔Vec = record
    { to = record { _⟨$⟩_ = toVec ; cong = Vec.tabulate-cong }
    ; from = P.→-to-⟶ fromVec
    ; inverse-of = record
      { left-inverse-of = fromVec-toVec
      ; right-inverse-of = toVec-fromVec
      }
    }

  -- Isomorphism between tables with existential length and lists.
  ↔List : Inverse (OverΣ.setoid (setoid A)) (P.setoid (List A))
  ↔List = record
    { to = record
      { _⟨$⟩_ = toList′
      ; cong = λ {(P.refl , p) → List.tabulate-cong p}
      }
    ; from = P.→-to-⟶ fromList′
    ; inverse-of = record
      { left-inverse-of = fromList′-toList′
      ; right-inverse-of = toList-fromList
      }
    }

--------------------------------------------------------------------------------
--  Coercion
--------------------------------------------------------------------------------

  coerceLength : ∀ {m n} → m ≡ n → Table A m → Table A n
  coerceLength P.refl t = t

  coerceLength-correct : ∀ {m n} {f} (p : m ≡ n) → OverΣ _≗_ (m , f) (n , coerceLength p f)
  coerceLength-correct P.refl = P.refl , λ _ → P.refl

--------------------------------------------------------------------------------
--  Select
--------------------------------------------------------------------------------

  -- Picks a single value out of the table and sets all other values to the
  -- given default.
  select : ∀ {n} → A → Fin n → Table A n → Table A n
  select z i t j = if ⌊ j ≟ i ⌋ then t i else z

  -- Selecting from any function is the same as selecting from a constant function.
  select-const : ∀ {n} z (i : Fin n) t j → select z i t j ≡ select z i (λ _ → t i) j
  select-const z i t j with ⌊ j ≟ i ⌋
  select-const z i t j | true = P.refl
  select-const z i t j | false = P.refl
