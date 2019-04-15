------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to indexed containers that uses heterogeneous
-- equality
------------------------------------------------------------------------

-- The notation and presentation here is perhaps close to those used
-- by Hancock and Hyvernat in "Programming interfaces and basic
-- topology" (2006).

{-# OPTIONS --with-K --safe --guardedness #-}

module Data.Container.Indexed.WithK where

open import Axiom.Extensionality.Heterogeneous using (Extensionality)
open import Data.Container.Indexed hiding (module PlainMorphism)
open import Data.Product as Prod hiding (map)
open import Function renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Level
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Relation.Binary.Indexed.Heterogeneous

------------------------------------------------------------------------

-- Equality, parametrised on an underlying relation.

Eq : ∀ {i o c r ℓ} {I : Set i} {O : Set o} (C : Container I O c r)
     (X Y : Pred I ℓ) → IREL X Y ℓ → IREL (⟦ C ⟧ X) (⟦ C ⟧ Y) _
Eq C _ _ _≈_ {o₁} {o₂} (c , k) (c′ , k′) =
  o₁ ≡ o₂ × c ≅ c′ × (∀ r r′ → r ≅ r′ → k r ≈ k′ r′)

private

  -- Note that, if propositional equality were extensional, then Eq _≅_
  -- and _≅_ would coincide.

  Eq⇒≅ : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
         {C : Container I O c r} {X : Pred I ℓ} {o₁ o₂ : O}
         {xs : ⟦ C ⟧ X o₁} {ys : ⟦ C ⟧ X o₂} → Extensionality r ℓ →
         Eq C X X (λ x₁ x₂ → x₁ ≅ x₂) xs ys → xs ≅ ys
  Eq⇒≅ {xs = c , k} {.c , k′} ext (refl , refl , k≈k′) =
    H.cong (_,_ c) (ext (λ _ → refl) (λ r → k≈k′ r r refl))

setoid : ∀ {i o c r s} {I : Set i} {O : Set o} →
         Container I O c r → IndexedSetoid I s _ → IndexedSetoid O _ _
setoid C X = record
  { Carrier       = ⟦ C ⟧ X.Carrier
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl , refl , λ { r .r refl → X.refl }
    ; sym   = sym
    ; trans = λ { {_} {i = xs} {ys} {zs} → trans {_} {i = xs} {ys} {zs}  }
    }
  }
  where
  module X = IndexedSetoid X

  _≈_ : IRel (⟦ C ⟧ X.Carrier) _
  _≈_ = Eq C X.Carrier X.Carrier X._≈_

  sym : Symmetric (⟦ C ⟧ X.Carrier) _≈_
  sym {_} {._} {_ , _} {._ , _} (refl , refl , k) =
    refl , refl , λ { r .r refl → X.sym (k r r refl) }

  trans : Transitive (⟦ C ⟧ X.Carrier) _≈_
  trans {._} {_} {._} {_ , _} {._ , _} {._ , _}
    (refl , refl , k) (refl , refl , k′) =
      refl , refl , λ { r .r refl → X.trans (k r r refl) (k′ r r refl) }

------------------------------------------------------------------------
-- Functoriality

module Map where

  identity : ∀ {i o c r s} {I : Set i} {O : Set o} (C : Container I O c r)
             (X : IndexedSetoid I s _) → let module X = IndexedSetoid X in
             ∀ {o} {xs : ⟦ C ⟧ X.Carrier o} → Eq C X.Carrier X.Carrier
             X._≈_ xs (map C {X.Carrier} ⟨id⟩ xs)
  identity C X = IndexedSetoid.refl (setoid C X)

  composition : ∀ {i o c r s ℓ₁ ℓ₂} {I : Set i} {O : Set o}
                (C : Container I O c r) {X : Pred I ℓ₁} {Y : Pred I ℓ₂}
                (Z : IndexedSetoid I s _) → let module Z = IndexedSetoid Z in
                {f : Y ⊆ Z.Carrier} {g : X ⊆ Y} {o : O} {xs : ⟦ C ⟧ X o} →
                Eq C Z.Carrier Z.Carrier Z._≈_
                  (map C {Y} f (map C {X} g xs))
                  (map C {X} (f ⟨∘⟩ g) xs)
  composition C Z = IndexedSetoid.refl (setoid C Z)

------------------------------------------------------------------------
-- Plain morphisms

module PlainMorphism {i o c r} {I : Set i} {O : Set o} where

  open Data.Container.Indexed.PlainMorphism

  -- Naturality.

  Natural : ∀ {ℓ} {C₁ C₂ : Container I O c r} →
            ((X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X) → Set _
  Natural {C₁ = C₁} {C₂} m =
    ∀ {X} Y → let module Y = IndexedSetoid Y in (f : X ⊆ Y.Carrier) →
    ∀ {o} (xs : ⟦ C₁ ⟧ X o) →
      Eq C₂ Y.Carrier Y.Carrier Y._≈_
        (m Y.Carrier $ map C₁ {X} f xs) (map C₂ {X} f $ m X xs)

  -- Natural transformations.

  NT : ∀ {ℓ} (C₁ C₂ : Container I O c r) → Set _
  NT {ℓ} C₁ C₂ = ∃ λ (m : (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X) →
                 Natural m

  -- Container morphisms are natural.

  natural : ∀ {ℓ} (C₁ C₂ : Container I O c r) (m : C₁ ⇒ C₂) → Natural {ℓ} ⟪ m ⟫
  natural _ _ m {X} Y f _ = refl , refl , λ { r .r refl → lemma (coherent m) }
    where
    module Y = IndexedSetoid Y

    lemma : ∀ {i j} (eq : i ≡ j) {x} →
            P.subst Y.Carrier eq (f x) Y.≈ f (P.subst X eq x)
    lemma refl = Y.refl

  -- In fact, all natural functions of the right type are container
  -- morphisms.

  complete : ∀ {C₁ C₂ : Container I O c r} (nt : NT C₁ C₂) →
             ∃ λ m → (X : IndexedSetoid I _ _) →
                     let module X = IndexedSetoid X in
                     ∀ {o} (xs : ⟦ C₁ ⟧ X.Carrier o) →
                     Eq C₂ X.Carrier X.Carrier X._≈_
                       (proj₁ nt X.Carrier xs) (⟪ m ⟫ X.Carrier {o} xs)
  complete {C₁} {C₂} (nt , nat) = m , (λ X xs → nat X
    (λ { (r , eq) → P.subst (IndexedSetoid.Carrier X) eq (proj₂ xs r) })
    (proj₁ xs , (λ r → r , refl)))
    where

    m : C₁ ⇒ C₂
    m = record
      { command  = λ      c₁       → proj₁        (lemma c₁)
      ; response = λ {_} {c₁}  r₂  → proj₁ (proj₂ (lemma c₁) r₂)
      ; coherent = λ {_} {c₁} {r₂} → proj₂ (proj₂ (lemma c₁) r₂)
      }
      where
      lemma : ∀ {o} (c₁ : Command C₁ o) → Σ[ c₂ ∈ Command C₂ o ]
              ((r₂ : Response C₂ c₂) → Σ[ r₁ ∈ Response C₁ c₁ ]
              next C₁ c₁ r₁ ≡ next C₂ c₂ r₂)
      lemma c₁ = nt (λ i → Σ[ r₁ ∈ Response C₁ c₁ ] next C₁ c₁ r₁ ≡ i)
                    (c₁ , λ r₁ → r₁ , refl)

  -- Composition commutes with ⟪_⟫.

  ∘-correct : {C₁ C₂ C₃ : Container I O c r}
              (f : C₂ ⇒ C₃) (g : C₁ ⇒ C₂) (X : IndexedSetoid I (c ⊔ r) _) →
              let module X = IndexedSetoid X in
              ∀ {o} {xs : ⟦ C₁ ⟧ X.Carrier o} →
              Eq C₃ X.Carrier X.Carrier X._≈_
                (⟪ f ∘ g ⟫ X.Carrier xs)
                (⟪ f ⟫ X.Carrier (⟪ g ⟫ X.Carrier xs))
  ∘-correct f g X = refl , refl , λ { r .r refl → lemma (coherent g)
                                                        (coherent f) }
    where
    module X = IndexedSetoid X

    lemma : ∀ {i j k} (eq₁ : i ≡ j) (eq₂ : j ≡ k) {x} →
      P.subst X.Carrier (P.trans eq₁ eq₂) x
      X.≈
      P.subst X.Carrier eq₂ (P.subst X.Carrier eq₁ x)
    lemma refl refl = X.refl

------------------------------------------------------------------------
-- All and any

-- Membership.

infix 4 _∈_

_∈_ : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
      {C : Container I O c r} {X : Pred I (i ⊔ ℓ)} → IREL X (⟦ C ⟧ X) _
_∈_ {C = C} {X} x xs = ◇ C {X = X} ((x ≅_) ⟨∘⟩ proj₂) (-, xs)
