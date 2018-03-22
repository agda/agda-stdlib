------------------------------------------------------------------------
-- The Agda standard library
--
-- Table-related properties
------------------------------------------------------------------------

module Data.Table.Properties where

open import Data.Table
open import Data.Table.Relation.Equality

open import Data.Bool using (true; false; if_then_else_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Properties using (_≟_)
open import Data.List as L using (List; _∷_; [])
open import Data.List.Any using (here; there; index)
open import Data.List.Any.Membership.Propositional using (_∈_)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)
open import Data.Product.Relation.Pointwise.Dependent as ΣR using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec as V using (Vec; _∷_; [])
import Data.Vec.Properties as VP
open import Function using (_∘_; flip)
open import Function.Inverse using (Inverse)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Nullary using (yes; no)

map-toList-hom :
  ∀ {n a b} {A : Set a} {B : Set b} {f : A → B} (t : Table A n)
  → L.map f (toList t) ≡ toList (map f t)
map-toList-hom {ℕ.zero} t = P.refl
map-toList-hom {ℕ.suc n} t = P.cong₂ _∷_ P.refl (map-toList-hom (tail t))

module _ {a} {A : Set a} where

  fromList-∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → lookup (fromList xs) i ∈ xs
  fromList-∈ {[]}     ()
  fromList-∈ {x ∷ xs} zero    = here P.refl
  fromList-∈ {x ∷ xs} (suc i) = there (fromList-∈ i)

  index-fromList-∈ : ∀ {xs i} → index (fromList-∈ {xs} i) ≡ i
  index-fromList-∈ {[]}     {()}
  index-fromList-∈ {x ∷ xs} {zero}  = P.refl
  index-fromList-∈ {x ∷ xs} {suc i} = P.cong suc index-fromList-∈

  fromList-index : ∀ {xs} {x : A} (x∈xs : x ∈ xs) → lookup (fromList xs) (index x∈xs) ≡ x
  fromList-index (here px)    = P.sym px
  fromList-index (there x∈xs) = fromList-index x∈xs

  lookup∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → ∃ λ x → x ∈ xs
  lookup∈ i = _ , fromList-∈ i

  lookup∈-index : ∀ {x} {xs : List A} (p : x ∈ xs) → lookup∈ (index p) ≡ (x , p)
  lookup∈-index {_} (here P.refl) = P.refl
  lookup∈-index {x} (there p) with ΣR.≡⇒Pointwise-≡ (lookup∈-index p)
  lookup∈-index {x} (there p) | q , r = ΣR.Pointwise-≡⇒≡ (q , helper q r)
    where
    helper :
      ∀ {x y} {xs : List A} {i} {p : x ∈ xs}
      → L.lookup xs i ≡ x → fromList-∈ {xs} i ≅ p
      → there {x = y} (fromList-∈ i) ≅ there {x = y} p
    helper P.refl _≅_.refl = _≅_.refl

  -- Isomorphism between tables and vectors.

  private

    fromVec : ∀ {n} → Vec A n → Table A n
    fromVec = tabulate ∘ flip V.lookup

    toVec : ∀ {n} → Table A n → Vec A n
    toVec = V.tabulate ∘ lookup

    fromVec-toVec : ∀ {n} (t : Table A n) → fromVec (toVec t) ≗ t
    fromVec-toVec _ = VP.lookup∘tabulate _

    toVec-fromVec : ∀ {n} (v : Vec A n) → toVec (fromVec v) ≡ v
    toVec-fromVec = VP.tabulate∘lookup

  ↔Vec : ∀ {n} → Inverse (≡-setoid A n) (P.setoid (Vec A n))
  ↔Vec = record
    { to = record { _⟨$⟩_ = toVec ; cong = VP.tabulate-cong }
    ; from = P.→-to-⟶ fromVec
    ; inverse-of = record
      { left-inverse-of = VP.lookup∘tabulate ∘ lookup
      ; right-inverse-of = VP.tabulate∘lookup
      }
    }

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
    fromList′ = λ xs → L.length xs , fromList xs

    toList′ : ∃ (Table A) → List A
    toList′ = toList ∘ proj₂

    List-lookup-tabulate : ∀ {n} (f : Fin n → A) → OverΣ (λ {n} → P._≗_ {A = Fin n}) (L.length (L.tabulate f) , L.lookup (L.tabulate f)) (n , f)
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

  -- Isomorphism between tables with existential length and lists.
  ↔List : Inverse (OverΣ.setoid (≡-setoid A)) (P.setoid (List A))
  ↔List = record
    { to = record
      { _⟨$⟩_ = toList′
      ; cong = λ {(P.refl , p) → LP.tabulate-cong p}
      }
    ; from = P.→-to-⟶ fromList′
    ; inverse-of = record
      { left-inverse-of = fromList′-toList′
      ; right-inverse-of = toList-fromList
      }
    }


  -- Selecting from any table is the same as selecting from a constant table.

  select-const : ∀ {n} (z : A) (i : Fin n) t → select z i t ≗ select z i (replicate (lookup t i))
  select-const z i t j with j ≟ i
  ... | yes _ = P.refl
  ... | no  _ = P.refl
