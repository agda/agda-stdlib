------------------------------------------------------------------------
-- The Agda standard library
--
-- Table-related properties
------------------------------------------------------------------------

module Data.Table.Properties where

open import Data.Table
open import Data.Table.Relation.Equality

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; suc; zero; _≟_)
open import Data.List as L using (List; _∷_; [])
open import Data.List.Any using (here; there; index)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product as Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Product.Relation.Pointwise.Dependent as ΣR using (_,_)
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
map-toList-hom {zero} t = P.refl
map-toList-hom {suc n} t = P.cong₂ _∷_ P.refl (map-toList-hom (tail t))

module _ {a} {A : Set a} where

  fromList-∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → lookup (fromList xs) i ∈ xs
  fromList-∈ {[]}     ()
  fromList-∈ {x ∷ xs} zero    = here P.refl
  fromList-∈ {x ∷ xs} (suc i) = there (fromList-∈ i)

  index-fromList-∈ : ∀ {xs i} → index (fromList-∈ {xs} i) ≡ i
  index-fromList-∈ {[]}     {()}
  index-fromList-∈ {x ∷ xs} {zero}  = P.refl
  index-fromList-∈ {x ∷ xs} {suc i} = P.cong Fin.suc index-fromList-∈

  fromList-index : ∀ {xs} {x : A} (x∈xs : x ∈ xs) → lookup (fromList xs) (index x∈xs) ≡ x
  fromList-index (here px)    = P.sym px
  fromList-index (there x∈xs) = fromList-index x∈xs

  lookup∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → ∃ λ x → x ∈ xs
  lookup∈ i = _ , fromList-∈ i

  lookup∈-index : ∀ {x} {xs : List A} (p : x ∈ xs) → lookup∈ (index p) ≡ (x , p)
  lookup∈-index (here P.refl) = P.refl
  lookup∈-index (there {xs = xs} p) =
    let q , r = ΣR.≡⇒Pointwise-≡ (lookup∈-index p)
    in ΣR.Pointwise-≡⇒≡ (q , H.icong (λ y → y ∈ xs) q there r)

  -- Isomorphism between tables and vectors.

  private

    fromVec : ∀ {n} → Vec A n → Table A n
    fromVec = tabulate ∘ flip V.lookup

    toVec : ∀ {n} → Table A n → Vec A n
    toVec = V.tabulate ∘ lookup

  ↔Vec : ∀ {n} → Inverse (≡-setoid A n) (P.setoid (Vec A n))
  ↔Vec = record
    { to = record { _⟨$⟩_ = toVec ; cong = VP.tabulate-cong }
    ; from = P.→-to-⟶ fromVec
    ; inverse-of = record
      { left-inverse-of = VP.lookup∘tabulate ∘ lookup
      ; right-inverse-of = VP.tabulate∘lookup
      }
    }


  -- Selecting from any table is the same as selecting from a constant table.

  select-const : ∀ {n} (z : A) (i : Fin n) t → select z i t ≗ select z i (replicate (lookup t i))
  select-const z i t j with j ≟ i
  ... | yes _ = P.refl
  ... | no  _ = P.refl
