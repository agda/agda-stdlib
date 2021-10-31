module Relation.Binary.Properties.Apartness where

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Consequences using (comp⇒≁-trans)
open import Relation.Binary.Structures using (IsEquivalence; IsApartness)
open import Relation.Nullary using (¬_)

module _
  {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁}
  {_#_ : Rel A ℓ₂}
  where

  private
    _¬#_ : A → A → Set _
    x ¬# y = ¬ (x # y)

  ¬#-equiv : Reflexive _≈_ → IsApartness _≈_ _#_ → IsEquivalence _¬#_
  ¬#-equiv re apart = record
    { refl = irrefl re
    ; sym = λ x¬#y y#x → x¬#y (sym y#x)
    ; trans = comp⇒≁-trans comp
    }
    where open IsApartness apart