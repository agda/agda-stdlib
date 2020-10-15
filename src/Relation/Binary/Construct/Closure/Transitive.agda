------------------------------------------------------------------------
-- The Agda standard library
--
-- Transitive closures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Transitive where

open import Function.Base
open import Function.Equivalence as Equiv using (_⇔_)
open import Level
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Transitive closure

infix 4 Plus

syntax Plus R x y = x [ R ]⁺ y

data Plus {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_]     : ∀ {x y} (x∼y : x ∼ y) → x [ _∼_ ]⁺ y
  _∼⁺⟨_⟩_ : ∀ x {y z} (x∼⁺y : x [ _∼_ ]⁺ y) (y∼⁺z : y [ _∼_ ]⁺ z) →
            x [ _∼_ ]⁺ z

module _ {_∼_ : Rel A ℓ} where

 []-injective : ∀ {x y p q} → (x [ _∼_ ]⁺ y ∋ [ p ]) ≡ [ q ] → p ≡ q
 []-injective refl = refl

 -- See also ∼⁺⟨⟩-injectiveˡ and ∼⁺⟨⟩-injectiveʳ in
 -- Relation.Binary.Construct.Closure.Transitive.WithK.

-- "Equational" reasoning notation. Example:
--
--   lemma =
--     x  ∼⁺⟨ [ lemma₁ ] ⟩
--     y  ∼⁺⟨ lemma₂ ⟩∎
--     z  ∎

finally : ∀ {_∼_ : Rel A ℓ} x y → x [ _∼_ ]⁺ y → x [ _∼_ ]⁺ y
finally _ _ = id

syntax finally x y x∼⁺y = x ∼⁺⟨ x∼⁺y ⟩∎ y ∎

infixr 2 _∼⁺⟨_⟩_
infix  3 finally

-- Map.

map : {_R₁_ : Rel A ℓ} {_R₂_ : Rel B ℓ₂} {f : A → B} →
      _R₁_ =[ f ]⇒ _R₂_ → Plus _R₁_ =[ f ]⇒ Plus _R₂_
map R₁⇒R₂ [ xRy ]             = [ R₁⇒R₂ xRy ]
map R₁⇒R₂ (x ∼⁺⟨ xR⁺z ⟩ zR⁺y) =
  _ ∼⁺⟨ map R₁⇒R₂ xR⁺z ⟩ map R₁⇒R₂ zR⁺y

------------------------------------------------------------------------
-- Alternative definition of transitive closure

-- A generalisation of Data.List.Nonempty.List⁺.

infixr 5 _∷_ _++_
infix  4 Plus′

syntax Plus′ R x y = x ⟨ R ⟩⁺ y

data Plus′ {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_] : ∀ {x y} (x∼y : x ∼ y) → x ⟨ _∼_ ⟩⁺ y
  _∷_ : ∀ {x y z} (x∼y : x ∼ y) (y∼⁺z : y ⟨ _∼_ ⟩⁺ z) → x ⟨ _∼_ ⟩⁺ z

-- Transitivity.

_++_ : ∀ {_∼_ : Rel A ℓ} {x y z} →
       x ⟨ _∼_ ⟩⁺ y → y ⟨ _∼_ ⟩⁺ z → x ⟨ _∼_ ⟩⁺ z
[ x∼y ]      ++ y∼⁺z = x∼y ∷ y∼⁺z
(x∼y ∷ y∼⁺z) ++ z∼⁺u = x∼y ∷ (y∼⁺z ++ z∼⁺u)

-- Plus and Plus′ are equivalent.

equivalent : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {x y} →
             Plus _∼_ x y ⇔ Plus′ _∼_ x y
equivalent {_∼_ = _∼_} = Equiv.equivalence complete sound
  where
  complete : Plus _∼_ ⇒ Plus′ _∼_
  complete [ x∼y ]             = [ x∼y ]
  complete (x ∼⁺⟨ x∼⁺y ⟩ y∼⁺z) = complete x∼⁺y ++ complete y∼⁺z

  sound : Plus′ _∼_ ⇒ Plus _∼_
  sound [ x∼y ]      = [ x∼y ]
  sound (x∼y ∷ y∼⁺z) = _ ∼⁺⟨ [ x∼y ] ⟩ sound y∼⁺z
