------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of linear maps between Modules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Properties.LinearMap where

open import Algebra        using (CommutativeRing; Field)
open import Algebra.Linear.Bundles
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
import      Algebra.Module.Morphism.ModuleHomomorphism as ModHomo
open import Axiom.DoubleNegationElimination
open import Data.List
import      Data.List.Relation.Binary.Equality.Setoid  as ListEq
open import Data.Product   hiding (map)
open import Function
import      Function.Relation.Binary.Equality          as ExtEq
open import Level          using (Level; suc; _⊔_)
open import Relation.Binary
import      Relation.Binary.PropositionalEquality      as Eq
open import Relation.Binary.Reasoning.MultiSetoid

------------------------------------------------------------------------
-- Properties of linear maps from vectors to their underlying scalars.
--
-- Note: We're using a derivative of `VectorSpace`: `DotProductSpace`,
--       because we need the properties of the dot product for some of
--       the proofs below and because, typically, when we speak of
--       linear maps from vectors to scalars we're assuming that a dot
--       product will be intimately involved.
--
-- Note: `f` in the code below refers to the linear function contained
--       within the `LinearMap`.
--
-- ToDo: `List` ==> `Foldable Functor`
module V⊸S
  {r ℓr m ℓm    : Level}
  {dotProdSpace : DotProductSpace r ℓr m ℓm}
  (lm           : LinearMap (DotProductSpace.mod dotProdSpace) ⟨module⟩)
  where

  open import Algebra.Linear.Properties.DotProductSpace dotProdSpace
  open DotProductSpace dotProdSpace
  open CommutativeRing (Field.ring fld)
    renaming (Carrier  to S)  -- "S" for scalar.
  open ExtEq setoid
  open LinearMap lm public
  open ListEq setoid using (_≋_; ≋-refl; ≋-setoid; ≋-sym)
    renaming ( _∷_  to _∷′_ )
  open ModHomo mod ⟨module⟩ homo
  open Module mod
    renaming (Carrierᴹ to V)  -- "V" for vector.
  open Setoid (≈ᴸᴹ-setoid mod ⟨module⟩) public using () renaming
    ( Carrier to LM
    ; _≈_     to _≈ᴸᴹ_
    )

  -- Every linear map from a vector to a scalar is equivalent to a vector.
  -- (This is proved in `Isomorphism 1`, near the bottom of this file.)
  -- Vector equivalent to `f` of linear map.
  fVec = vgen f basisSet

  -- Proof that the linear function in a `V⊸S` must be homomorphic
  -- over sums of products.
  vred : (V → S) → List V → S
  vred g = foldr (_+_ ∘ uncurry _*_ ∘ < g , f >) 0#

  foldr-homo : (g : V → S) → (xs : List V) → f (vgen g xs) ≈ vred g xs
  foldr-homo g []       = 0ᴹ-homo
  foldr-homo g (x ∷ xs) = begin⟨ setoid ⟩
    f (h x (foldr h 0ᴹ xs))
      ≈⟨ +ᴹ-homo (g x *ₗ x) (foldr h 0ᴹ xs) ⟩
    f (g x *ₗ x) + f (foldr h 0ᴹ xs)
      ≈⟨ +-congʳ (*ₗ-homo (g x) x) ⟩
    g x * f x + f (foldr h 0ᴹ xs)
      ≈⟨ +-congˡ (foldr-homo g xs) ⟩
    g x * f x + vred g xs
      ∎
    where
    h = _+ᴹ_ ∘ vscale g

  -- Proof that the linear function inside a `V⊸S` is always
  -- equivalent to taking the dot product with some vector.
  foldr-cong : ∀ {f g : V → S → S} {d e : S} →
               (∀ {y z} → y ≈ z → ∀ x → f x y ≈ g x z) → d ≈ e →
               foldr f d ≗ foldr g e
  foldr-cong f≈g d≈e []       = d≈e
  foldr-cong f≈g d≈e (x ∷ xs) = f≈g (foldr-cong f≈g d≈e xs) x

  f[u]⇔v∙u : ∀ {a} → f a ≈ fVec ∙ a
  f[u]⇔v∙u {a} = sym (begin⟨ setoid ⟩
    v′ ∙ a ≈⟨ ∙-comm ⟩
    a ∙ v′ ≈⟨ foldr-homo-∙ (vscale-cong f ⟦⟧-cong) basisSet ⟩
    foldr (_+_ ∘ (a ∙_) ∘ fScale) (a ∙ 0ᴹ) basisSet
      ≈⟨ foldr-cong (λ {y≈z _ → +-congˡ y≈z}) ∙-idʳ basisSet ⟩
    foldr (_+_ ∘ (a ∙_) ∘ (uncurry _*ₗ_) ∘ < f , id >) 0# basisSet
      ≈⟨ foldr-cong (λ y≈z _ → +-cong ∙-comm-*ₗ y≈z)
                    (reflexive Eq.refl) basisSet ⟩
    foldr (_+_ ∘ (uncurry _*_) ∘ < f , (a ∙_) >) 0# basisSet
      ≈⟨ foldr-cong (λ y≈z x → +-cong (*-comm (f x) (a ∙ x)) y≈z)
                    (reflexive Eq.refl) basisSet ⟩
    foldr (_+_ ∘ (uncurry _*_) ∘ < (a ∙_) , f >) 0# basisSet
      ≈⟨ sym (foldr-homo (a ∙_) basisSet) ⟩
    f (foldr (_+ᴹ_ ∘ (uncurry _*ₗ_) ∘ < (a ∙_) , id >) 0ᴹ basisSet)
      ≈⟨ ⟦⟧-cong (Setoid.sym ≈ᴹ-setoid basisOrthonorm) ⟩
    f a ∎)
    where
    v′ = fVec
    fScale : V → V
    fScale = vscale f

  -- Dot product extensional equivalence.
  x·z≈y·z⇒x≈y : DoubleNegationElimination ℓm → ∀ {x y} →
                ∃₂ (λ s z → ((s *ₗ (x +ᴹ -ᴹ y) ≈ᴹ z) × (f z ≉ 0#))) →
                (∀ {z} → x ∙ z ≈ y ∙ z) → x ≈ᴹ y
  x·z≈y·z⇒x≈y dne {x} {y} Σ[z]fz≉𝟘 x∙z≈y∙z = fx≈fy⇒x≈y {dne} Σ[z]fz≉𝟘 fx≈fy
    where
    v′ = fVec
    fx≈fy : f x ≈ f y
    fx≈fy = begin⟨ setoid ⟩
      f x   ≈⟨ f[u]⇔v∙u {x} ⟩
      v′ ∙ x ≈⟨ ∙-comm ⟩
      x ∙ v′ ≈⟨ x∙z≈y∙z ⟩
      y ∙ v′ ≈⟨ ∙-comm ⟩
      v′ ∙ y ≈⟨ sym (f[u]⇔v∙u {y}) ⟩
      f y   ∎

-- Isomorphism 1: (V ⊸ S) ↔ V
--
-- A linear map from a vector to its underlying scalar field is
-- isomorphic to a lone vector.
module _
  {r ℓr m ℓm    : Level}
  (dotProdSpace : DotProductSpace r ℓr m ℓm)
  where

  open import Algebra.Linear.Properties.DotProductSpace dotProdSpace
  open DotProductSpace dotProdSpace
  open CommutativeRing (Field.ring fld)
    renaming (Carrier to S)
  open Module mod
    renaming (Carrierᴹ to V)
  open Setoid (≈ᴸᴹ-setoid mod ⟨module⟩)
    renaming ( Carrier to V⊸S
             ; _≈_     to _≈ᴸᴹ_
             ; reflexive to reflexiveᴸᴹ
             )

  lmToVec : V⊸S → V
  lmToVec lm = vgen (LinearMap.f lm) basisSet

  V⊸S↔V : Inverse (≈ᴸᴹ-setoid mod ⟨module⟩) ≈ᴹ-setoid
  V⊸S↔V = record
    { to        = lmToVec
    ; from      = λ u  → mkLM (u ∙_) u∙-homo
    ; to-cong   = vgen-cong basisSet
    ; from-cong = λ z x → ∙-congʳ z
    ; inverse   = fwd , rev
    }
    where
    fwd : Inverseˡ _≈ᴸᴹ_ _≈ᴹ_ lmToVec (λ u → mkLM (u ∙_) u∙-homo)
    fwd v = begin⟨ ≈ᴹ-setoid ⟩
      vgen (v ∙_) basisSet ≈⟨ Setoid.sym ≈ᴹ-setoid basisOrthonorm ⟩
      v                    ∎
    rev : Inverseʳ _≈ᴸᴹ_ _≈ᴹ_ lmToVec (λ u → mkLM (u ∙_) u∙-homo)
    rev lm = begin⟨ ≈ᴸᴹ-setoid mod ⟨module⟩ ⟩
      mkLM (fVec ∙_) u∙-homo ≈⟨ g ⟩
      lm                     ∎
      where
      open V⊸S {dotProdSpace = dotProdSpace} lm
      g : (v : V) → (Setoid._≈_ setoid (fVec ∙ v)) (f v)
      g x = Setoid.sym setoid (f[u]⇔v∙u {x})
