------------------------------------------------------------------------
-- The Agda standard library
--
-- Fixed-size tables of values, implemented as functions from 'Fin n'.
-- Similar to 'Data.Vec', but focusing on ease of retrieval instead of
-- ease of adding and removing elements.
------------------------------------------------------------------------

module Data.Table where

open import Data.Table.Base public

open import Relation.Binary.PropositionalEquality
  as P using (_≡_; _→-setoid_)
open import Relation.Binary using (Setoid)

open import Function using (_∘_; _on_; flip)
open import Function.Inverse using (Inverse; _↔_)
import Function.Equality as FE

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

setoid : ∀ {c p} → Setoid c p → ℕ → Setoid _ _
setoid S n = record
  { Carrier = Table Carrier n
  ; _≈_ = λ t t′ → ∀ i → lookup t i ≈ lookup t′ i
  ; isEquivalence = record
    { refl = λ i → refl
    ; sym = λ p → sym ∘ p
    ; trans = λ p q i → trans (p i) (q i)
    }
  }
  where open Setoid S

≡-setoid : ∀ {a} → Set a → ℕ → Setoid _ _
≡-setoid A = setoid (P.setoid A)

module _ {a} {A : Set a} {n} where
  open Setoid (≡-setoid A n) public
    using () renaming (_≈_ to _≗_)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

foldr : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B → B) → B → Table A n → B
foldr {n = ℕ.zero} f z t = z
foldr {n = ℕ.suc n} f z t = f (lookup t zero) (foldr f z (tail t))

foldl : ∀ {a b} {A : Set a} {B : Set b} {n} → (B → A → B) → B → Table A n → B
foldl {n = ℕ.zero} f z t = z
foldl {n = ℕ.suc n} f z t = foldl f (f z (lookup t zero)) (tail t)

pure : ∀ {n a} {A : Set a} → A → Table A n
pure x = tabulate (λ _ → x)

_⊛_ : ∀ {n a b} {A : Set a} {B : Set b} → Table (A → B) n → Table A n → Table B n
fs ⊛ xs = tabulate λ i → lookup fs i (lookup xs i)

permute : ∀ {m n a} {A : Set a} → Fin m ↔ Fin n → Table A n → Table A m
permute π = rearrange (Inverse.to π FE.⟨$⟩_)

module _ {a} {A : Set a} where

--------------------------------------------------------------------------------
--  List conversion
--------------------------------------------------------------------------------

  private
    liftInj :
      ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : Set b}
      {k : A′ → A} → (∀ x → ∃ λ y → x ≡ k y)
      → {f g : A → B} → (f ∘ k) P.≗ (g ∘ k) → f P.≗ g
    liftInj k-admissible p x with k-admissible x
    liftInj k-admissible p ._ | y , P.refl = p y

    liftPseudoInj :
      ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : Set b}
      {k : A′ → A} {z : A} → (∀ x → x ≡ z ⊎ ∃ λ y → x ≡ k y)
      → {f g : A → B} → f z ≡ g z → (f ∘ k) P.≗ (g ∘ k) → f P.≗ g
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
      → OverΣ (λ {x} → P._≗_ {A = P x}) (i , f ∘ k) (j , g ∘ k)
      → OverΣ (λ {x} → P._≗_ {A = P x}) (h i , f) (h j , g)
    liftPseudoInjOver k-admissible p (P.refl , q) = P.refl , liftPseudoInj k-admissible p q

    fromList′ : List A → ∃ (Table A)
    fromList′ = λ xs → List.length xs , fromList xs

    toList′ : ∃ (Table A) → List A
    toList′ = toList ∘ proj₂

    List-lookup-tabulate : ∀ {n} (f : Fin n → A) → OverΣ (λ {n} → P._≗_ {A = Fin n}) (List.length (List.tabulate f) , List.lookup (List.tabulate f)) (n , f)
    List-lookup-tabulate {ℕ.zero} _ = P.refl , λ ()
    List-lookup-tabulate {ℕ.suc n} f = liftPseudoInjOver decideFin P.refl (List-lookup-tabulate (f ∘ suc))
      where
        decideFin : ∀ {n} (i : Fin (ℕ.suc n)) → i ≡ zero ⊎ ∃ λ j → i ≡ suc j
        decideFin zero = inj₁ P.refl
        decideFin (suc i) = inj₂ (i , P.refl)

    fromList′-toList : ∀ {n} (t : Table A n) → OverΣ _≗_ (fromList′ (toList t)) (n , t)
    fromList′-toList = OverΣ.hom (λ p → p) ∘ List-lookup-tabulate ∘ lookup

    fromList′-toList′ : (x : ∃ (Table A)) → OverΣ _≗_ (fromList′ (toList′ x)) x
    fromList′-toList′ (_ , f) = fromList′-toList f

    toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
    toList-fromList [] = P.refl
    toList-fromList (x ∷ xs) = P.cong₂ _∷_ P.refl (toList-fromList xs)

    fromVec : ∀ {n} → Vec A n → Table A n
    fromVec = tabulate ∘ flip Vec.lookup

    toVec : ∀ {n} → Table A n → Vec A n
    toVec = Vec.tabulate ∘ lookup

    fromVec-toVec : ∀ {n} (t : Table A n) → fromVec (toVec t) ≗ t
    fromVec-toVec _ = Vec.lookup∘tabulate _

    toVec-fromVec : ∀ {n} (v : Vec A n) → toVec (fromVec v) ≡ v
    toVec-fromVec = Vec.tabulate∘lookup

  -- Isomorphism between tables and vectors.
  ↔Vec : ∀ {n} → Inverse (≡-setoid A n) (P.setoid (Vec A n))
  ↔Vec = record
    { to = record { _⟨$⟩_ = toVec ; cong = Vec.tabulate-cong }
    ; from = P.→-to-⟶ fromVec
    ; inverse-of = record
      { left-inverse-of = Vec.lookup∘tabulate ∘ lookup
      ; right-inverse-of = Vec.tabulate∘lookup
      }
    }

  -- Isomorphism between tables with existential length and lists.
  ↔List : Inverse (OverΣ.setoid (≡-setoid A)) (P.setoid (List A))
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
--  Select
--------------------------------------------------------------------------------

  -- Picks a single value out of the table and sets all other values to the
  -- given default.
  select : ∀ {n} → A → Fin n → Table A n → Table A n
  select z i t = tabulate λ j → if ⌊ j ≟ i ⌋ then lookup t i else z

  -- Selecting from any table is the same as selecting from a constant table.
  select-const : ∀ {n} z (i : Fin n) t → select z i t ≗ select z i (pure (lookup t i))
  select-const z i t j with ⌊ j ≟ i ⌋
  select-const z i t j | true = P.refl
  select-const z i t j | false = P.refl
