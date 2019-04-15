------------------------------------------------------------------------
-- The Agda standard library
--
-- The max operator derived from an arbitrary total order
------------------------------------------------------------------------

open import Algebra using (SelectiveMagma)

module Algebra.Construct.LiftedChoice
  {b ℓ} (∙-selectiveMagma : SelectiveMagma b ℓ)
  where

open import Algebra.FunctionProperties
open import Algebra.Structures
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_)
open import Level using (Level; _⊔_)
open import Function using (id; _on_)
open import Function.Injection using (Injection)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Unary using (Pred)
open import Relation.Nullary.Negation using (contradiction)

open SelectiveMagma ∙-selectiveMagma
  renaming (Carrier to B; sel to ∙-sel)
  hiding (isMagma)
open import Relation.Binary.Reasoning.Setoid setoid

private
  variable
    a p : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

Lift : (A → B) → Op₂ A
Lift f x y with ∙-sel (f x) (f y)
... | inj₁ _ = x
... | inj₂ _ = y

------------------------------------------------------------------------
-- Algebraic properties
 
sel : ∀ (f : A → B) → Selective _≡_ (Lift f)
sel f x y with ∙-sel (f x) (f y)
... | inj₁ _ = inj₁ P.refl
... | inj₂ _ = inj₂ P.refl

distrib : ∀ (f : A → B) → ∀ x y → ((f x) ∙ (f y)) ≈ f (Lift f x y)
distrib f x y with ∙-sel (f x) (f y)
... | inj₁ fx∙fy≈fx = fx∙fy≈fx
... | inj₂ fx∙fy≈fy = fx∙fy≈fy

module _ {ℓ} {_≈A_ : Rel A ℓ} {f : A → B} where

  private
    _◦_ = Lift f

  cong : (∀ {x y} → f x ≈ f y → x ≈A y) → f Preserves _≈A_ ⟶ _≈_ →
         Congruent₂ _≈A_ _◦_
  cong f-inj f-cong {x} {y} {u} {v} x≈y u≈v
    with ∙-sel (f x) (f u) | ∙-sel (f y) (f v)
  ... | inj₁ fx∙fu≈fx | inj₁ fy∙fv≈fy = x≈y
  ... | inj₂ fx∙fu≈fu | inj₂ fy∙fv≈fv = u≈v
  ... | inj₁ fx∙fu≈fx | inj₂ fy∙fv≈fv = f-inj (begin
    f x       ≈⟨ sym fx∙fu≈fx ⟩
    f x ∙ f u ≈⟨ ∙-cong (f-cong x≈y) (f-cong u≈v) ⟩
    f y ∙ f v ≈⟨ fy∙fv≈fv ⟩
    f v       ∎)
  ... | inj₂ fx∙fu≈fu | inj₁ fy∙fv≈fy = f-inj (begin
    f u       ≈⟨ sym fx∙fu≈fu ⟩
    f x ∙ f u ≈⟨ ∙-cong (f-cong x≈y) (f-cong u≈v) ⟩
    f y ∙ f v ≈⟨ fy∙fv≈fy ⟩
    f y       ∎)

  assoc : (∀ {x y} → f x ≈ f y → x ≈A y) →
          Associative _≈_ _∙_ → Associative _≈A_ _◦_
  assoc injective ∙-assoc x y z = injective (begin
    f ((x ◦ y) ◦ z)   ≈˘⟨ distrib f (x ◦ y) z ⟩
    f (x ◦ y) ∙ f z   ≈˘⟨ ∙-congʳ (distrib f x y) ⟩
    (f x ∙ f y) ∙ f z ≈⟨  ∙-assoc (f x) (f y) (f z) ⟩
    f x ∙ (f y ∙ f z) ≈⟨  ∙-congˡ (distrib f y z) ⟩
    f x ∙ f (y ◦ z)   ≈⟨  distrib f x (y ◦ z) ⟩
    f (x ◦ (y ◦ z))   ∎)

  comm : (∀ {x y} → f x ≈ f y → x ≈A y) →
         Commutative _≈_ _∙_ → Commutative _≈A_ _◦_
  comm injective ∙-comm x y = injective (begin
    f (x ◦ y) ≈˘⟨ distrib f x y ⟩
    f x ∙ f y ≈⟨  ∙-comm (f x) (f y) ⟩
    f y ∙ f x ≈⟨  distrib f y x ⟩
    f (y ◦ x) ∎)

------------------------------------------------------------------------
-- Algebraic structures

module _ {ℓ} {_≈A_ : Rel A ℓ} (≈A-isEquivalence : IsEquivalence _≈A_)
         {f : A → B} (f-inj : ∀ {x y} → f x ≈ f y → x ≈A y)
         (f-cong : f Preserves _≈A_ ⟶ _≈_)
         where

  private
    _◦_ = Lift f

  isMagma : IsMagma _≈A_ _◦_
  isMagma = record
    { isEquivalence = ≈A-isEquivalence
    ; ∙-cong        = cong (λ {x y} → f-inj {x} {y}) f-cong
    }

  isSemigroup : IsSemigroup _≈A_ _◦_
  isSemigroup = {!!}

------------------------------------------------------------------------
-- Other properties

module _ {ℓ} {_≈A_ : Rel A ℓ} {P : Pred A p} (f : A → B) where

  presᵒ : (∀ {x y} → P x → (f x ∙ f y) ≈ f y → P y) →
          (∀ {x y} → P y → (f x ∙ f y) ≈ f x → P x) →
          {!!} --Lift Preservesᵒ P
  presᵒ left right x y (inj₁ px) with ∙-sel (f x) (f y)
  ... | inj₁ _        = px
  ... | inj₂ fx∙fy≈fx = left px fx∙fy≈fx
  presᵒ left right x y (inj₂ py) with ∙-sel (f x) (f y)
  ... | inj₁ fx∙fy≈fy = right py fx∙fy≈fy
  ... | inj₂ _ = py

  presʳ : (∀ {x y} → P y → (f x ∙ f y) ≈ f x → P x) →
          {!!} --Lift Preservesʳ P
  presʳ right x {y} Py with ∙-sel (f x) (f y)
  ... | inj₁ fx∙fy≈fx = right Py fx∙fy≈fx
  ... | inj₂ fx∙fy≈fy = Py

  presᵇ : ∀ (P : Pred A p) → {!!} --Lift Preservesᵇ P
  presᵇ P {x} {y} Px Py with ∙-sel (f x) (f y)
  ... | inj₁ _ = Px
  ... | inj₂ _ = Py

  forcesᵇ : (∀ {x y} → P x → (f x ∙ f y) ≈ f x → P y) →
            (∀ {x y} → P y → (f x ∙ f y) ≈ f y → P x) →
            {!!} --Lift Forcesᵇ P
  forcesᵇ presˡ presʳ x y P[x∙y] with ∙-sel (f x) (f y)
  ... | inj₁ fx∙fy≈fx = P[x∙y] , presˡ P[x∙y] fx∙fy≈fx
  ... | inj₂ fx∙fy≈fy = presʳ P[x∙y] fx∙fy≈fy , P[x∙y]


{-
module _ {ℓ} {f : A → B} {_≈ᵇ_ : Rel B ℓ} {∙-sel : Selective _≈ᵇ_ _∙_} where
  --open EqReasoning S
  
  
  {-
  presᵒ : ∀ {p} → (P : Pred A p) → (∀ {x y} → (f x ∙ f y) ≈ᵇ f x → P y → P x) → _◦_ Preservesᵒ P
  presᵒ P impl a b Pa⊎Pb with ∙-sel (f a) (f b)
  ... | inj₁ fa∙fb≈fa = [ id , impl fa∙fb≈fa ] Pa⊎Pb
  ... | inj₂ fa∙fb≈fb = [ impl {!!} , id ] Pa⊎Pb
  -}

  module _ {ℓ₂} {_≈ᵃ_ : Rel A ℓ₂} where

    {-
    private
      Injective : (f : A → B) → Set _
      Injective = ∀ {x y} → f x ≈ᵇ f y → x ≈ᵃ y
    
    -}

-}

{-

-}
