------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for Colists
------------------------------------------------------------------------

module Codata.Colist.Bisimilarity where

open import Level using (_⊔_)
open import Size
open import Codata.Thunk
open import Codata.Colist
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

data Bisim {a b r} {A : Set a} {B : Set b} (R : A → B → Set r) (i : Size) :
           (xs : Colist A ∞) (ys : Colist B ∞) → Set (r ⊔ a ⊔ b) where
  []  : Bisim R i [] []
  _∷_ : ∀ {x y xs ys} → R x y → Thunk^R (Bisim R) i xs ys → Bisim R i (x ∷ xs) (y ∷ ys)


module _ {a r} {A : Set a} {R : A → A → Set r} where

 reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
 reflexive refl^R {i} {[]}     = []
 reflexive refl^R {i} {r ∷ rs} = refl^R ∷ λ where .force → reflexive refl^R

module _ {a b} {A : Set a} {B : Set b}
         {r} {P : A → B → Set r} {Q : B → A → Set r} where

 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ []       = []
 symmetric sym^PQ (p ∷ ps) = sym^PQ p ∷ λ where .force → symmetric sym^PQ (ps .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

 transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
 transitive trans^PQR []       []       = []
 transitive trans^PQR (p ∷ ps) (q ∷ qs) =
   trans^PQR p q ∷ λ where .force → transitive trans^PQR (ps .force) (qs .force)

-- Pointwise Equality as a Bisimilarity
------------------------------------------------------------------------

module _ {ℓ} {A : Set ℓ} where

 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Colist A ∞ → Colist A ∞ → Set ℓ
 _⊢_≈_ = Bisim _≡_

 refl : ∀ {i} → Reflexive (i ⊢_≈_)
 refl = reflexive Eq.refl

 sym : ∀ {i} → Symmetric (i ⊢_≈_)
 sym = symmetric Eq.sym

 trans : ∀ {i} → Transitive (i ⊢_≈_)
 trans = transitive Eq.trans
