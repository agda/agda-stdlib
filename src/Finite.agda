------------------------------------------------------------------------
-- The Agda standard library
--
-- Notions of finiteness for setoids
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Finite where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base as ×
open import Data.Sum.Base as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function
open import Level renaming (suc to lsuc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetR
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    c ℓ c′ ℓ′ : Level

Ω : ∀ p → Setoid (lsuc p) p
Ω p = record
  { Carrier = Set p
  ; _≈_ = λ P Q → (P → Q) × (Q → P)
  ; isEquivalence = record
    { refl = id , id
    ; sym = swap
    ; trans = λ (f , g) (f′ , g′) → f′ ∘ f , g ∘ g′
    }
  }

Subset : Setoid c ℓ → (p : Level) → Set (c ⊔ ℓ ⊔ lsuc p)
Subset X p = Func X (Ω p)

FullSubset : {X : Setoid c ℓ} → Subset X 0ℓ
FullSubset = record { to = λ _ → ⊤ }

record EquivalenceRelation (X : Setoid c ℓ) r : Set (c ⊔ ℓ ⊔ lsuc r) where
  infix 4 _∼_
  open Setoid X
  field
    _∼_ : Rel Carrier r
    ∼-resp-≈ : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → x ∼ y → x′ ∼ y′
    ∼-isEquivalence : IsEquivalence _∼_

  open IsEquivalence ∼-isEquivalence public renaming
    ( refl                 to ∼-refl
    ; trans                to ∼-trans
    ; sym                  to ∼-sym
    ; reflexive            to ∼-reflexive
    ; isPartialEquivalence to ∼-isPartialEquivalence
    )

  ≈⇒∼ : ∀ {x y} → x ≈ y → x ∼ y
  ≈⇒∼ q = ∼-resp-≈ refl q ∼-refl

_⁻¹[_] : ∀ {p} {X : Setoid c ℓ} {Y : Setoid c′ ℓ′} →
  Func X Y → Subset Y p → Setoid (c ⊔ p) ℓ
_⁻¹[_] {X = X} f S =
  On.setoid {B = Σ[ x ∈ X.Carrier ] S.to (f.to x)} X proj₁
  where
  module X = Setoid X
  module f = Func f
  module S = Func S

_[_] : ∀ {p} {X : Setoid c ℓ} {Y : Setoid c′ ℓ′} →
  Func X Y → Subset X p → Setoid (c ⊔ p) ℓ′
_[_] {X = X} {Y} f S =
  On.setoid {B = Σ[ x ∈ X.Carrier ] S.to x} Y (f.to ∘ proj₁)
  where
  module X = Setoid X
  module f = Func f
  module S = Func S

↣⇒⊆ : ∀ {X : Setoid c ℓ} {Y : Setoid c′ ℓ′} → Injection Y X → Subset X (c′ ⊔ ℓ)
↣⇒⊆ {X = X} {Y} m = record
  { to = λ x → ∃ \ y → to y X.≈ x
  ; cong = λ p →
    (λ (y , q) → y , X.trans q p) , (λ (y , q) → y , X.trans q (X.sym p))
  }
  where
  module X = Setoid X
  module Y = Setoid Y
  open Injection m

_/_ : ∀ {r} (X : Setoid c ℓ) → EquivalenceRelation X r → Setoid c r
X / R = record
  { Carrier = Carrier
  ; _≈_ = _∼_
  ; isEquivalence = ∼-isEquivalence
  }
  where
  open Setoid X
  open EquivalenceRelation R

include-/ : ∀ {r} {X : Setoid c ℓ} (R : EquivalenceRelation X r) →
  Surjection X (X / R)
include-/ {X = X} R = record
  { to = id
  ; cong = ≈⇒∼
  ; surjective = λ y → y , ∼-refl
  }
  where
  open Setoid X
  open EquivalenceRelation R

record StrictlyFinite (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    inv : Inverse X (≡.setoid (Fin size))

record Subfinite (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    inj : Injection X (≡.setoid (Fin size))

record FinitelyEnumerable (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    srj : Surjection (≡.setoid (Fin size)) X

record SubFinitelyEnumerable (X : Setoid c ℓ) c′ ℓ′
       : Set (c ⊔ ℓ ⊔ lsuc (c′ ⊔ ℓ′)) where
  field
    Apex : Setoid c′ ℓ′
    finitelyEnumerable : FinitelyEnumerable Apex
    inj : Injection X Apex

  open FinitelyEnumerable finitelyEnumerable public

record SubfinitelyEnumerable (X : Setoid c ℓ) c′ ℓ′
       : Set (c ⊔ ℓ ⊔ lsuc (c′ ⊔ ℓ′)) where
  field
    Apex : Setoid c′ ℓ′
    subfinite : Subfinite Apex
    srj : Surjection Apex X

  open Subfinite subfinite public

lemma→ : {X : Setoid c ℓ} →
  SubFinitelyEnumerable X c′ ℓ′ → SubfinitelyEnumerable X (c ⊔ ℓ′) 0ℓ
lemma→ {X = X} sfe = record
  { Apex = e.function ⁻¹[ ↣⇒⊆ inj ]
  ; subfinite = record
    { size = size
    ; inj = record
      { to = proj₁
      ; cong = id
      ; injective = id
      }
    }
  ; srj = record
    { to = λ (i , x , q) → x
    ; cong = λ {(i , x , q)} {(i′ , x′ , q′)} p →
      let open SetR Apex in m.injective $ begin
      m.to x   ≈⟨ q ⟩
      e.to i   ≡⟨ ≡.cong e.to p ⟩
      e.to i′  ≈˘⟨ q′ ⟩
      m.to x′  ∎
    ; surjective = λ x →
      (e.to⁻ (m.to x) , x , A.sym (e.surjective (m.to x) .proj₂)) , X.refl
    }
  }
  where
  -- X --m--> Apex <--e-- Fin size
  open SubFinitelyEnumerable sfe
  module X = Setoid X
  module A = Setoid Apex
  module m = Injection inj
  module e = Surjection srj

lemma← : {X : Setoid c ℓ} →
  SubfinitelyEnumerable X c′ ℓ′ → SubFinitelyEnumerable X 0ℓ (ℓ ⊔ c′)
lemma← {X = X} se = record
  { Apex = ≡.setoid (Fin size) / R
  ; finitelyEnumerable = record
    { size = size
    ; srj = include-/ R
    }
  ; inj = record
    { to = λ x → m.to (e.to⁻ x)
    ; cong = λ {x y} q → let open SetR X in
      inj₂ ((e.to⁻ x , e.to⁻ y) , ≡.refl , ≡.refl , (begin
        e.to (e.to⁻ x)  ≈⟨ e.surjective x .proj₂ ⟩
        x               ≈⟨ q ⟩
        y               ≈˘⟨ e.surjective y .proj₂ ⟩
        e.to (e.to⁻ y)  ∎))
    ; injective = λ {x y} → λ where
      (inj₁ q) → let open SetR X in begin
        x               ≈˘⟨ e.surjective x .proj₂ ⟩
        e.to (e.to⁻ x)  ≈⟨ e.cong (m.injective q) ⟩
        e.to (e.to⁻ y)  ≈⟨ e.surjective y .proj₂ ⟩
        y               ∎
      (inj₂ ((f , g) , iq , jq , q)) → let open SetR X in begin
        x               ≈˘⟨ e.surjective x .proj₂ ⟩
        e.to (e.to⁻ x)  ≈˘⟨ e.cong (m.injective iq) ⟩
        e.to f          ≈⟨ q ⟩
        e.to g          ≈⟨ e.cong (m.injective jq) ⟩
        e.to (e.to⁻ y)  ≈⟨ e.surjective y .proj₂ ⟩
        y               ∎
    }
  }
  where
  -- X <--e-- Apex --m--> Fin size
  open SubfinitelyEnumerable se
  module X = Setoid X
  module A = Setoid Apex
  module m = Injection inj
  module e = Surjection srj

  R : EquivalenceRelation (≡.setoid (Fin size)) _
  R = record
    { _∼_ = λ i j → i ≡ j ⊎
      ∃ \ ((f , g) : A.Carrier × A.Carrier) →
        m.to f ≡ i × m.to g ≡ j × e.to f X.≈ e.to g
    ; ∼-resp-≈ = λ { ≡.refl ≡.refl → id }
    ; ∼-isEquivalence = record
      { refl = inj₁ ≡.refl
      ; sym = ⊎.map ≡.sym
        λ ((f , g) , iq , jq , q) → (g , f) , jq , iq , X.sym q
      ; trans = λ where
        (inj₁ ≡.refl) q → q
        (inj₂ p) (inj₁ ≡.refl) → inj₂ p
        (inj₂ ((f , g) , ip , jp , p)) (inj₂ ((f′ , g′) , iq , jq , q)) →
          inj₂ ((f , g′) , ip , jq , let open SetR X in begin
            e.to f   ≈⟨ p ⟩
            e.to g   ≈⟨ e.cong (m.injective (≡.trans jp (≡.sym iq))) ⟩
            e.to f′  ≈⟨ q ⟩
            e.to g′  ∎)
      }
    }
