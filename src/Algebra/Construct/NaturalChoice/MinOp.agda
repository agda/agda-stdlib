------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a min operator derived from a spec over a total
-- preorder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (TotalPreorder)
open import Algebra.Construct.NaturalChoice.Base using (MinOperator; MinOp⇒MaxOp)

module Algebra.Construct.NaturalChoice.MinOp
  {a ℓ₁ ℓ₂} {O : TotalPreorder a ℓ₁ ℓ₂} (minOp : MinOperator O) where

open import Algebra.Core using (Op₂)
open import Algebra.Bundles
  using (RawMagma; Magma; Semigroup; Band; CommutativeSemigroup; SelectiveMagma; Monoid)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_])
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_)
open import Relation.Binary.Core using (_Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (Maximum; Minimum)

open TotalPreorder O renaming
  ( Carrier   to A
  ; _≲_       to _≤_
  ; ≲-resp-≈  to ≤-resp-≈
  ; ≲-respʳ-≈ to ≤-respʳ-≈
  ; ≲-respˡ-≈ to ≤-respˡ-≈
  )
open MinOperator minOp

open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Relation.Binary.Reasoning.Preorder preorder

------------------------------------------------------------------------
-- Helpful properties

x⊓y≤x : ∀ x y → x ⊓ y ≤ x
x⊓y≤x x y with total x y
... | inj₁ x≤y = reflexive (x≤y⇒x⊓y≈x x≤y)
... | inj₂ y≤x = ≤-respˡ-≈ (Eq.sym (x≥y⇒x⊓y≈y y≤x)) y≤x

x⊓y≤y : ∀ x y → x ⊓ y ≤ y
x⊓y≤y x y with total x y
... | inj₁ x≤y = ≤-respˡ-≈ (Eq.sym (x≤y⇒x⊓y≈x x≤y)) x≤y
... | inj₂ y≤x = reflexive (x≥y⇒x⊓y≈y y≤x)

------------------------------------------------------------------------
-- Algebraic properties

⊓-comm : Commutative _⊓_
⊓-comm x y with total x y
... | inj₁ x≤y = Eq.trans (x≤y⇒x⊓y≈x x≤y) (Eq.sym (x≥y⇒x⊓y≈y x≤y))
... | inj₂ y≤x = Eq.trans (x≥y⇒x⊓y≈y y≤x) (Eq.sym (x≤y⇒x⊓y≈x y≤x))

⊓-congˡ : ∀ x → Congruent₁ (x ⊓_)
⊓-congˡ x {y} {r} y≈r with total x y
... | inj₁ x≤y = begin-equality
  x ⊓ y  ≈⟨  x≤y⇒x⊓y≈x x≤y ⟩
  x      ≈⟨ x≤y⇒x⊓y≈x (≤-respʳ-≈ y≈r x≤y) ⟨
  x ⊓ r  ∎
... | inj₂ y≤x = begin-equality
  x ⊓ y  ≈⟨  x≥y⇒x⊓y≈y y≤x ⟩
  y      ≈⟨  y≈r ⟩
  r      ≈⟨ x≥y⇒x⊓y≈y (≤-respˡ-≈ y≈r y≤x) ⟨
  x ⊓ r  ∎

⊓-congʳ : ∀ x → Congruent₁ (_⊓ x)
⊓-congʳ x {y₁} {y₂} y₁≈y₂ = begin-equality
  y₁ ⊓ x  ≈⟨ ⊓-comm x y₁ ⟨
  x  ⊓ y₁ ≈⟨  ⊓-congˡ x y₁≈y₂ ⟩
  x  ⊓ y₂ ≈⟨  ⊓-comm x y₂ ⟩
  y₂ ⊓ x  ∎

⊓-cong : Congruent₂ _⊓_
⊓-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ = Eq.trans (⊓-congˡ x₁ y₁≈y₂) (⊓-congʳ y₂ x₁≈x₂)

⊓-assoc : Associative _⊓_
⊓-assoc x y r with total x y | total y r
⊓-assoc x y r | inj₁ x≤y | inj₁ y≤r = begin-equality
  (x ⊓ y) ⊓ r  ≈⟨ ⊓-congʳ r (x≤y⇒x⊓y≈x x≤y) ⟩
  x ⊓ r        ≈⟨ x≤y⇒x⊓y≈x (trans x≤y y≤r) ⟩
  x            ≈⟨ x≤y⇒x⊓y≈x x≤y ⟨
  x ⊓ y        ≈⟨ ⊓-congˡ x (x≤y⇒x⊓y≈x y≤r) ⟨
  x ⊓ (y ⊓ r)  ∎
⊓-assoc x y r | inj₁ x≤y | inj₂ r≤y = begin-equality
  (x ⊓ y) ⊓ r  ≈⟨ ⊓-congʳ r (x≤y⇒x⊓y≈x x≤y) ⟩
  x ⊓ r        ≈⟨ ⊓-congˡ x (x≥y⇒x⊓y≈y r≤y) ⟨
  x ⊓ (y ⊓ r)  ∎
⊓-assoc x y r | inj₂ y≤x | _ = begin-equality
  (x ⊓ y) ⊓ r  ≈⟨ ⊓-congʳ r (x≥y⇒x⊓y≈y y≤x) ⟩
  y ⊓ r        ≈⟨ x≥y⇒x⊓y≈y (trans (x⊓y≤x y r) y≤x) ⟨
  x ⊓ (y ⊓ r)  ∎

⊓-idem : Idempotent _⊓_
⊓-idem x = x≤y⇒x⊓y≈x (refl {x})

⊓-sel : Selective _⊓_
⊓-sel x y = Sum.map x≤y⇒x⊓y≈x x≥y⇒x⊓y≈y (total x y)

⊓-identityˡ : ∀ {⊤} → Maximum _≤_ ⊤ → LeftIdentity ⊤ _⊓_
⊓-identityˡ max = x≥y⇒x⊓y≈y ∘ max

⊓-identityʳ : ∀ {⊤} → Maximum _≤_ ⊤ → RightIdentity ⊤ _⊓_
⊓-identityʳ max = x≤y⇒x⊓y≈x ∘ max

⊓-identity : ∀ {⊤} → Maximum _≤_ ⊤ → Identity ⊤ _⊓_
⊓-identity max = ⊓-identityˡ max , ⊓-identityʳ max

⊓-zeroˡ : ∀ {⊥} → Minimum _≤_ ⊥ → LeftZero ⊥ _⊓_
⊓-zeroˡ min = x≤y⇒x⊓y≈x ∘ min

⊓-zeroʳ : ∀ {⊥} → Minimum _≤_ ⊥ → RightZero ⊥ _⊓_
⊓-zeroʳ min = x≥y⇒x⊓y≈y ∘ min

⊓-zero : ∀ {⊥} → Minimum _≤_ ⊥ → Zero ⊥ _⊓_
⊓-zero min = ⊓-zeroˡ min , ⊓-zeroʳ min

------------------------------------------------------------------------
-- Structures

⊓-isMagma : IsMagma _⊓_
⊓-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = ⊓-cong
  }

⊓-isSemigroup : IsSemigroup _⊓_
⊓-isSemigroup = record
  { isMagma = ⊓-isMagma
  ; assoc   = ⊓-assoc
  }

⊓-isBand : IsBand _⊓_
⊓-isBand = record
  { isSemigroup = ⊓-isSemigroup
  ; idem        = ⊓-idem
  }

⊓-isCommutativeSemigroup : IsCommutativeSemigroup _⊓_
⊓-isCommutativeSemigroup = record
  { isSemigroup = ⊓-isSemigroup
  ; comm        = ⊓-comm
  }

⊓-isSelectiveMagma : IsSelectiveMagma _⊓_
⊓-isSelectiveMagma = record
  { isMagma = ⊓-isMagma
  ; sel     = ⊓-sel
  }

⊓-isMonoid : ∀ {⊤} → Maximum _≤_ ⊤ → IsMonoid _⊓_ ⊤
⊓-isMonoid max = record
  { isSemigroup = ⊓-isSemigroup
  ; identity    = ⊓-identity max
  }

------------------------------------------------------------------------
-- Raw bundles

⊓-rawMagma : RawMagma _ _
⊓-rawMagma = record { _≈_ = _≈_ ; _∙_ = _⊓_ }

------------------------------------------------------------------------
-- Bundles

⊓-magma : Magma _ _
⊓-magma = record
  { isMagma = ⊓-isMagma
  }

⊓-semigroup : Semigroup _ _
⊓-semigroup = record
  { isSemigroup = ⊓-isSemigroup
  }

⊓-band : Band _ _
⊓-band = record
  { isBand = ⊓-isBand
  }

⊓-commutativeSemigroup : CommutativeSemigroup _ _
⊓-commutativeSemigroup = record
  { isCommutativeSemigroup = ⊓-isCommutativeSemigroup
  }

⊓-selectiveMagma : SelectiveMagma _ _
⊓-selectiveMagma = record
  { isSelectiveMagma = ⊓-isSelectiveMagma
  }

⊓-monoid : ∀ {⊤} → Maximum _≤_ ⊤ → Monoid a ℓ₁
⊓-monoid max = record
  { isMonoid = ⊓-isMonoid max
  }

------------------------------------------------------------------------
-- Other properties

x⊓y≈x⇒x≤y : ∀ {x y} → x ⊓ y ≈ x → x ≤ y
x⊓y≈x⇒x≤y {x} {y} x⊓y≈x with total x y
... | inj₁ x≤y = x≤y
... | inj₂ y≤x = reflexive (Eq.trans (Eq.sym x⊓y≈x) (x≥y⇒x⊓y≈y y≤x))

x⊓y≈y⇒y≤x : ∀ {x y} → x ⊓ y ≈ y → y ≤ x
x⊓y≈y⇒y≤x {x} {y} x⊓y≈y = x⊓y≈x⇒x≤y (begin-equality
  y ⊓ x  ≈⟨ ⊓-comm y x ⟩
  x ⊓ y  ≈⟨ x⊓y≈y ⟩
  y      ∎)

mono-≤-distrib-⊓ : ∀ {f} → f Preserves _≈_ ⟶ _≈_ → f Preserves _≤_ ⟶ _≤_ →
                   ∀ x y → f (x ⊓ y) ≈ f x ⊓ f y
mono-≤-distrib-⊓ {f} cong mono x y with total x y
... | inj₁ x≤y = begin-equality
  f (x ⊓ y)  ≈⟨ cong (x≤y⇒x⊓y≈x x≤y) ⟩
  f x        ≈⟨ x≤y⇒x⊓y≈x (mono x≤y) ⟨
  f x ⊓ f y  ∎
... | inj₂ y≤x = begin-equality
  f (x ⊓ y)  ≈⟨ cong (x≥y⇒x⊓y≈y y≤x) ⟩
  f y        ≈⟨ x≥y⇒x⊓y≈y (mono y≤x) ⟨
  f x ⊓ f y  ∎

x≤y⇒x⊓z≤y : ∀ {x y} z → x ≤ y → x ⊓ z ≤ y
x≤y⇒x⊓z≤y z x≤y = trans (x⊓y≤x _ z) x≤y

x≤y⇒z⊓x≤y : ∀ {x y} z → x ≤ y → z ⊓ x ≤ y
x≤y⇒z⊓x≤y y x≤y = trans (x⊓y≤y y _) x≤y

x≤y⊓z⇒x≤y : ∀ {x} y z → x ≤ y ⊓ z → x ≤ y
x≤y⊓z⇒x≤y y z x≤y⊓z = trans x≤y⊓z (x⊓y≤x y z)

x≤y⊓z⇒x≤z : ∀ {x} y z → x ≤ y ⊓ z → x ≤ z
x≤y⊓z⇒x≤z y z x≤y⊓z = trans x≤y⊓z (x⊓y≤y y z)

⊓-mono-≤ : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
⊓-mono-≤ {x} {y} {u} {v} x≤y u≤v with ⊓-sel y v
... | inj₁ y⊓v≈y = ≤-respʳ-≈ (Eq.sym y⊓v≈y) (trans (x⊓y≤x x u) x≤y)
... | inj₂ y⊓v≈v = ≤-respʳ-≈ (Eq.sym y⊓v≈v) (trans (x⊓y≤y x u) u≤v)

⊓-monoˡ-≤ : ∀ x → (_⊓ x) Preserves _≤_ ⟶ _≤_
⊓-monoˡ-≤ x y≤z = ⊓-mono-≤ y≤z (refl {x})

⊓-monoʳ-≤ : ∀ x → (x ⊓_) Preserves _≤_ ⟶ _≤_
⊓-monoʳ-≤ x y≤z = ⊓-mono-≤ (refl {x}) y≤z

⊓-glb : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ y ⊓ z
⊓-glb {x} x≤y x≤z = ≤-respˡ-≈ (⊓-idem x) (⊓-mono-≤ x≤y x≤z)

⊓-triangulate : ∀ x y z → x ⊓ y ⊓ z ≈ (x ⊓ y) ⊓ (y ⊓ z)
⊓-triangulate x y z = begin-equality
  x ⊓ y ⊓ z           ≈⟨ ⊓-congʳ z (⊓-congˡ x (⊓-idem y)) ⟨
  x ⊓ (y ⊓ y) ⊓ z     ≈⟨  ⊓-assoc x _ _ ⟩
  x ⊓ ((y ⊓ y) ⊓ z)   ≈⟨  ⊓-congˡ x (⊓-assoc y y z) ⟩
  x ⊓ (y ⊓ (y ⊓ z))   ≈⟨ ⊓-assoc x y (y ⊓ z) ⟨
  (x ⊓ y) ⊓ (y ⊓ z)   ∎
