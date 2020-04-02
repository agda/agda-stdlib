module Data.Maybe.Relation.Binary.Extended where

open import Level
open import Data.Maybe
open import Data.Maybe.Relation.Binary.Pointwise
open import Relation.Binary

module _  {a ℓ₁ ℓ₂} (order : StrictTotalOrder a ℓ₁ ℓ₂) where
  private module O = StrictTotalOrder order

  data LT : Rel (Maybe O.Carrier) (a ⊔ ℓ₂) where
    just<just    : ∀ {a b} → a O.< b → LT (just a) (just b)
    nothing<just : ∀ {a} → LT nothing (just a)

  private lt-trans : Transitive LT
  lt-trans nothing<just  (just<just p) = nothing<just
  lt-trans (just<just p) (just<just q) = just<just (O.trans p q)

  private lt-compare : Trichotomous (Pointwise O._≈_) LT
  lt-compare nothing nothing = tri≈ (λ ()) nothing (λ ())
  lt-compare nothing (just x) = tri< nothing<just (λ ()) (λ ())
  lt-compare (just x) nothing = tri> (λ ()) (λ ()) nothing<just
  lt-compare (just x) (just y) with O.compare x y
  ... | tri< x<y ¬x≈y ¬x>y = tri< (just<just x<y) (λ where (just x≈y) → ¬x≈y x≈y) (λ where (just<just y<x) → ¬x>y y<x)
  ... | tri≈ ¬x<y x≈y ¬x>y = tri≈ (λ where (just<just x<y) → ¬x<y x<y) (just x≈y) (λ where (just<just y<x) → ¬x>y y<x)
  ... | tri> ¬x<y ¬x≈y x>y = tri> (λ where (just<just x<y) → ¬x<y x<y) (λ where (just x≈y) → ¬x≈y x≈y) (just<just x>y)

  isStrictTotalOrder : IsStrictTotalOrder (Pointwise O._≈_) LT
  isStrictTotalOrder = record
    { isEquivalence = isEquivalence O.isEquivalence
    ; trans = lt-trans
    ; compare = lt-compare }

  strictTotalOrder : StrictTotalOrder _ _ _
  strictTotalOrder = record { isStrictTotalOrder = isStrictTotalOrder }
