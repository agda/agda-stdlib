------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container where

open import Codata.Musical.M hiding (map)
open import Data.Product as Prod hiding (map)
open import Data.W hiding (map)
open import Function renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
import Function.Related as Related
open import Level
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Relation.Unary using (Pred ; _⊆_)

------------------------------------------------------------------------
-- Containers

-- A container is a set of shapes, and for every shape a set of
-- positions.

open import Data.Container.Core public
open Container public

-- The least and greatest fixpoints of a container.

μ : ∀ {s p} → Container s p → Set (s ⊔ p)
μ = W

ν : ∀ {s p} → Container s p → Set (s ⊔ p)
ν = M

-- Equality, parametrised on an underlying relation.

Eq : ∀ {s p x y e} (C : Container s p) {X : Set x} {Y : Set y} →
     (REL X Y e) → ⟦ C ⟧ X → ⟦ C ⟧ Y → Set (s ⊔ p ⊔ e)
Eq C _≈_ (s , f) (s′ , f′) =
  Σ[ eq ∈ s ≡ s′ ] (∀ p → f p ≈ f′ (P.subst (Position C) eq p))

private

  -- Note that, if propositional equality were extensional, then
  -- Eq _≡_ and _≡_ would coincide.

  Eq⇒≡ : ∀ {s p x} {C : Container s p} {X : Set x} {xs ys : ⟦ C ⟧ X} →
         P.Extensionality p x → Eq C _≡_ xs ys → xs ≡ ys
  Eq⇒≡ ext (P.refl , f≈f′) = P.cong -,_ (ext f≈f′)


module _ {s p x r} {X : Set x} (C : Container s p) (R : Rel X r) where

  refl : Reflexive R → Reflexive (Eq C R)
  refl R-refl = P.refl , λ p → R-refl

  sym : Symmetric R → Symmetric (Eq C R)
  sym R-sym (P.refl , f) = P.refl , λ p → R-sym (f p)

  trans : Transitive R → Transitive (Eq C R)
  trans R-trans (P.refl , f) (P.refl , g) = P.refl , λ p → R-trans (f p) (g p)

module _ {s p x e} (C : Container s p) (X : Setoid x e) where

  private
    module X = Setoid X
    _≈_ = Eq C X._≈_

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record
    { refl  = refl C X._≈_ X.refl
    ; sym   = sym C X._≈_ X.sym
    ; trans = λ {_ _ zs} → trans C X._≈_ X.trans {_} {_} {zs}
    }

  setoid : Setoid (s ⊔ p ⊔ x) (s ⊔ p ⊔ e)
  setoid = record
    { Carrier       = ⟦ C ⟧ X.Carrier
    ; _≈_           = _≈_
    ; isEquivalence = isEquivalence
    }

------------------------------------------------------------------------
-- Functoriality

-- Containers are functors.

map : ∀ {s p x y} {C : Container s p} {X : Set x} {Y : Set y} →
      (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Prod.map₂ (f ⟨∘⟩_)

module Map where

  identity :
    ∀ {s p x e} {C : Container s p} (X : Setoid x e) →
    let module X = Setoid X in (xs : ⟦ C ⟧ X.Carrier) → Eq C X._≈_ (map ⟨id⟩ xs) xs
  identity {C = C} X xs = Setoid.refl (setoid C X)

  composition :
    ∀ {s p x y z e} {C : Container s p} {X : Set x} {Y : Set y} (Z : Setoid z e) →
    let module Z = Setoid Z in
    (f : Y → Z.Carrier) (g : X → Y) (xs : ⟦ C ⟧ X) →
    Eq C Z._≈_ (map f (map g xs)) (map (f ⟨∘⟩ g) xs)
  composition {C = C} Z f g xs = Setoid.refl (setoid C Z)

------------------------------------------------------------------------
-- Container morphisms

module Morphism where

  -- Naturality.

  Natural : ∀ {s₁ s₂ p₁ p₂} x e {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} →
            (∀ {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) →
            Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂ ⊔ suc (x ⊔ e))
  Natural x e {C₁ = C₁} {C₂} m =
    ∀ {X : Set x} (Y : Setoid x e) → let module Y = Setoid Y in
    (f : X → Y.Carrier) (xs : ⟦ C₁ ⟧ X) →
    Eq C₂ Y._≈_ (m $ map f xs) (map f $ m xs)

  -- Natural transformations.

  NT : ∀ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) x e →
       Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂ ⊔ suc (x ⊔ e))
  NT C₁ C₂ x e = ∃ λ (m : ∀ {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) → Natural x e m

  -- Container morphisms are natural.

  natural : ∀ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
            (m : C₁ ⇒ C₂) x e → Natural x e ⟪ m ⟫
  natural m x e Y f xs = Setoid.refl (setoid _ Y)

  -- In fact, all natural functions of the right type are container
  -- morphisms.

  complete : ∀ {s₁ s₂ p₁ p₂ e} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
    (nt : NT C₁ C₂ p₁ e) →
      ∃ λ m → (X : Setoid p₁ e) → let module X = Setoid X in
      ∀ xs → Eq C₂ X._≈_ (proj₁ nt xs) (⟪ m ⟫ xs)
  complete {p₁ = p₁} {C₁ = C₁} {C₂} (nt , nat) =
    (m , λ X xs → nat X (proj₂ xs) (proj₁ xs , ⟨id⟩)) where

    m : C₁ ⇒ C₂
    m .shape    = λ s → proj₁ (nt (s , ⟨id⟩))
    m .position = proj₂ (nt (_ , ⟨id⟩))


----------
open Related public
  using (Kind; Symmetric-kind)
  renaming ( implication         to subset
           ; reverse-implication to superset
           ; equivalence         to set
           ; injection           to subbag
           ; reverse-injection   to superbag
           ; bijection           to bag
           )

--[_]-Order : ∀ {s p ℓ} → Kind → Container s p → Set ℓ →
  --          Preorder (s ⊔ p ⊔ ℓ) (s ⊔ p ⊔ ℓ) (p ⊔ ℓ)
--[ k ]-Order C X = Related.InducedPreorder₂ k (_∈_ {C = C} {X = X})

--[_]-Equality : ∀ {s p ℓ} → Symmetric-kind → Container s p → Set ℓ →
--               Setoid (s ⊔ p ⊔ ℓ) (p ⊔ ℓ)
--[ k ]-Equality C X = Related.InducedEquivalence₂ k (_∈_ {C = C} {X = X})

--infix 4 _∼[_]_

--_∼[_]_ : ∀ {s p x} {C : Container s p} {X : Set x} →
  --       ⟦ C ⟧ X → Kind → ⟦ C ⟧ X → Set (p ⊔ x)
--_∼[_]_ {C = C} {X} xs k ys = Preorder._∼_ ([ k ]-Order C X) xs ys
