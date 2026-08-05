------------------------------------------------------------------------
-- The Agda standard library
--
-- Group completion of a commutative monoid, i.e. the Grothendieck group
-- of the monoid.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Algebra.Construct.Add.Negatives.CommutativeMonoid where

open import Algebra.Bundles using (AbelianGroup; CommutativeMonoid)
import Algebra.Construct.DirectProduct as DirectProduct
import Algebra.Definitions as Definitions
open import Algebra.Morphism.Bundles using (MonoidHomomorphism)
open import Algebra.Morphism.Structures using
  (IsGroupHomomorphism; IsGroupIsomorphism; IsMonoidHomomorphism)
import Algebra.Properties.AbelianGroup as AbelianGroupProperties
import Algebra.Properties.CommutativeSemigroup
  as CommSemigroupProperties
open import Algebra.Structures using (IsAbelianGroup)
open import Data.Product.Base as Product
  using (∃-syntax; _,_; -,_; <_,_>; proj₁; proj₂; uncurry)
open import Function.Base using (const; id; _∘_; _∘₂_)
import Function.Consequences.Setoid as Consequences
open import Function.Definitions using (Bijective; Congruent)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)

module _ {m ℓ : Level} (monoid : CommutativeMonoid m ℓ) where

  private
    module M = CommutativeMonoid monoid
    open M using (commutativeSemigroup; rawMonoid; setoid)
      renaming
      ( Carrier   to Base         ; _≈_       to _≈ₘ_
      ; _∙_       to _+ₘ_         ; ε         to 0ₘ
      ; refl      to ≈ₘ-refl      ; sym       to ≈ₘ-sym
      ; ∙-cong    to +ₘ-cong
      ; ∙-congˡ   to +ₘ-congˡ     ; ∙-congʳ   to +ₘ-congʳ
      ; assoc     to +ₘ-assoc     ; comm      to +ₘ-comm
      ; identityˡ to +ₘ-identityˡ ; identityʳ to +ₘ-identityʳ
      )

    directProduct : CommutativeMonoid m ℓ
    directProduct = DirectProduct.commutativeMonoid monoid monoid

    module M² = CommutativeMonoid directProduct
    open CommSemigroupProperties commutativeSemigroup using (medial)

  open ≈-Reasoning setoid


  ------------------------------------------------------------------------
  -- Formal differences

  open M² public using (Carrier) renaming (_∙_ to _+_; ε to 0#)

  pos : Carrier → Base
  pos = proj₁

  neg : Carrier → Base
  neg = proj₂

  ------------------------------------------------------------------------
  -- Equality

  infix 4 _≈_

  _≈_ : Rel Carrier (m ⊔ ℓ)
  x ≈ y = ∃[ slack ]
    (pos x +ₘ neg y) +ₘ slack ≈ₘ (pos y +ₘ neg x) +ₘ slack

  open Definitions _≈_ using (Congruent₁; Congruent₂; LeftInverse)

  private
    rearrange : ∀ a b c d u v →
                ((a +ₘ c) +ₘ (b +ₘ d)) +ₘ (u +ₘ v) ≈ₘ
                ((a +ₘ b) +ₘ u) +ₘ ((c +ₘ d) +ₘ v)
    rearrange a b c d u v = begin
      ((a +ₘ c) +ₘ (b +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (medial a c b d) ⟩
      ((a +ₘ b) +ₘ (c +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ medial (a +ₘ b) (c +ₘ d) u v ⟩
      ((a +ₘ b) +ₘ u) +ₘ ((c +ₘ d) +ₘ v)  ∎

    composeˡ : ∀ a b c d u v →
               (a +ₘ b) +ₘ ((c +ₘ d) +ₘ (u +ₘ v)) ≈ₘ
               ((a +ₘ d) +ₘ u) +ₘ ((c +ₘ b) +ₘ v)
    composeˡ a b c d u v = begin
      (a +ₘ b) +ₘ ((c +ₘ d) +ₘ (u +ₘ v))
        ≈⟨ +ₘ-assoc (a +ₘ b) (c +ₘ d) (u +ₘ v) ⟨
      ((a +ₘ b) +ₘ (c +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (medial a b c d) ⟩
      ((a +ₘ c) +ₘ (b +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (+ₘ-congˡ (+ₘ-comm b d)) ⟩
      ((a +ₘ c) +ₘ (d +ₘ b)) +ₘ (u +ₘ v)
        ≈⟨ rearrange a d c b u v ⟩
      ((a +ₘ d) +ₘ u) +ₘ ((c +ₘ b) +ₘ v)  ∎

    composeʳ : ∀ a b c d u v →
               ((a +ₘ b) +ₘ u) +ₘ ((c +ₘ d) +ₘ v) ≈ₘ
               (c +ₘ b) +ₘ ((a +ₘ d) +ₘ (u +ₘ v))
    composeʳ a b c d u v = begin
      ((a +ₘ b) +ₘ u) +ₘ ((c +ₘ d) +ₘ v)
        ≈⟨ rearrange a b c d u v ⟨
      ((a +ₘ c) +ₘ (b +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (+ₘ-congˡ (+ₘ-comm b d)) ⟩
      ((a +ₘ c) +ₘ (d +ₘ b)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (medial a c d b) ⟩
      ((a +ₘ d) +ₘ (c +ₘ b)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (+ₘ-comm (a +ₘ d) (c +ₘ b)) ⟩
      ((c +ₘ b) +ₘ (a +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-assoc (c +ₘ b) (a +ₘ d) (u +ₘ v) ⟩
      (c +ₘ b) +ₘ ((a +ₘ d) +ₘ (u +ₘ v))  ∎

  ≈-from-parts : ∀ {x y} →
                 pos x ≈ₘ pos y → neg x ≈ₘ neg y → x ≈ y
  ≈-from-parts x⁺≈y⁺ x⁻≈y⁻ =
    0ₘ , +ₘ-congʳ (+ₘ-cong x⁺≈y⁺ (≈ₘ-sym x⁻≈y⁻))

  private
    pointwise⇒≈ : ∀ {x y} → M²._≈_ x y → x ≈ y
    pointwise⇒≈ = uncurry ≈-from-parts

    ≈-refl : Reflexive _≈_
    ≈-refl = pointwise⇒≈ M².refl

    ≈-trans : Transitive _≈_
    ≈-trans {a , b} {c , d} {e , f} =
      Product.zip (λ u v → (c +ₘ d) +ₘ (u +ₘ v))
      λ {u} {v} eq₁ eq₂ → begin
        (a +ₘ f) +ₘ ((c +ₘ d) +ₘ (u +ₘ v))
          ≈⟨ composeˡ a f c d u v ⟩
        ((a +ₘ d) +ₘ u) +ₘ ((c +ₘ f) +ₘ v)
          ≈⟨ +ₘ-cong eq₁ eq₂ ⟩
        ((c +ₘ b) +ₘ u) +ₘ ((e +ₘ d) +ₘ v)
          ≈⟨ composeʳ c b e d u v ⟩
        (e +ₘ b) +ₘ ((c +ₘ d) +ₘ (u +ₘ v))  ∎

  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record
    { refl  = ≈-refl
    ; sym   = Product.map₂ ≈ₘ-sym
    ; trans = ≈-trans
    }

  ------------------------------------------------------------------------
  -- Operations

  infix  8 -_

  -_ : Carrier → Carrier
  -_ = Product.swap

  +-cong : Congruent₂ _+_
  +-cong {a , b} {a′ , b′} {c , d} {c′ , d′} =
    Product.zip _+ₘ_ λ {u} {v} eq₁ eq₂ → begin
      ((a +ₘ c) +ₘ (b′ +ₘ d′)) +ₘ (u +ₘ v)
        ≈⟨ rearrange a b′ c d′ u v ⟩
      ((a +ₘ b′) +ₘ u) +ₘ ((c +ₘ d′) +ₘ v)
        ≈⟨ +ₘ-cong eq₁ eq₂ ⟩
      ((a′ +ₘ b) +ₘ u) +ₘ ((c′ +ₘ d) +ₘ v)
        ≈⟨ rearrange a′ b c′ d u v ⟨
      ((a′ +ₘ c′) +ₘ (b +ₘ d)) +ₘ (u +ₘ v)  ∎

  -‿cong : Congruent₁ -_
  -‿cong {a , b} {c , d} = Product.map₂ λ {u} eq → begin
    (b +ₘ c) +ₘ u  ≈⟨ +ₘ-congʳ (+ₘ-comm b c) ⟩
    (c +ₘ b) +ₘ u  ≈⟨ eq ⟨
    (a +ₘ d) +ₘ u  ≈⟨ +ₘ-congʳ (+ₘ-comm a d) ⟩
    (d +ₘ a) +ₘ u  ∎

  +-inverseˡ : LeftInverse 0# -_ _+_
  +-inverseˡ (a , b) = -, (begin
    ((b +ₘ a) +ₘ 0ₘ) +ₘ 0ₘ  ≈⟨ +ₘ-identityʳ _ ⟩
    (b +ₘ a) +ₘ 0ₘ          ≈⟨ +ₘ-congʳ (+ₘ-comm b a) ⟩
    (a +ₘ b) +ₘ 0ₘ  ≈⟨ +ₘ-congʳ (+ₘ-identityˡ _) ⟨
    (0ₘ +ₘ (a +ₘ b)) +ₘ 0ₘ  ∎)

  ------------------------------------------------------------------------
  -- Bundle

  completion-is-abelian-group : IsAbelianGroup _≈_ _+_ 0# -_
  completion-is-abelian-group = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = ≈-isEquivalence
            ; ∙-cong = +-cong
            }
          ; assoc = λ x → pointwise⇒≈ ∘₂ M².assoc x
          }
        ; identity = Product.map
            (pointwise⇒≈ ∘_) (pointwise⇒≈ ∘_) M².identity
        }
      ; inverse = +-inverseˡ , λ x →
          ≈-trans (pointwise⇒≈ (M².comm x (- x))) (+-inverseˡ x)
      ; ⁻¹-cong = -‿cong
      }
    ; comm = pointwise⇒≈ ∘₂ M².comm
    }

  abelianGroup : AbelianGroup m (m ⊔ ℓ)
  abelianGroup = record
    { Carrier        = Carrier
    ; _≈_            = _≈_
    ; _∙_            = _+_
    ; ε              = 0#
    ; _⁻¹            = -_
    ; isAbelianGroup = completion-is-abelian-group
    }

  open AbelianGroup abelianGroup
    using () renaming (rawMonoid to rawMonoid#)

  ------------------------------------------------------------------------
  -- Canonical embedding

  embed : Base → Carrier
  embed = < id , const 0ₘ >

  embed-cong : Congruent _≈ₘ_ _≈_ embed
  embed-cong x≈y = ≈-from-parts x≈y ≈ₘ-refl

  embed-∙ : ∀ x y → embed (x +ₘ y) ≈ embed x + embed y
  embed-∙ x y =
    ≈-from-parts ≈ₘ-refl (≈ₘ-sym (+ₘ-identityˡ 0ₘ))

  embed-isMonoidHomomorphism :
    IsMonoidHomomorphism rawMonoid rawMonoid# embed
  embed-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = embed-cong }
      ; ∙-homo            = embed-∙
      }
    ; ε-homo = ≈-refl
    }

  embed-monoidHomomorphism :
    MonoidHomomorphism rawMonoid rawMonoid#
  embed-monoidHomomorphism = record
    { ⟦_⟧                   = embed
    ; isMonoidHomomorphism = embed-isMonoidHomomorphism
    }

  decompose : ∀ x → x ≈ embed (pos x) + - embed (neg x)
  decompose (a , b) =
    ≈-from-parts (≈ₘ-sym (+ₘ-identityʳ a))
                 (≈ₘ-sym (+ₘ-identityˡ b))


  ------------------------------------------------------------------------
  -- Trivial completions

  open Definitions _≈ₘ_ using (RightZero)

  absorbing⇒trivial : (∞ : Base) → RightZero ∞ _+ₘ_ →
                      ∀ x → x ≈ 0#
  absorbing⇒trivial ∞ zeroʳ (a , b) = -, (begin
    (a +ₘ 0ₘ) +ₘ ∞  ≈⟨ zeroʳ (a +ₘ 0ₘ) ⟩
    ∞                ≈⟨ zeroʳ (0ₘ +ₘ b) ⟨
    (0ₘ +ₘ b) +ₘ ∞  ∎)


------------------------------------------------------------------------
-- Completion of an abelian group

module AlreadyGroup {m ℓ : Level} (G : AbelianGroup m ℓ) where

  private
    module G = AbelianGroup G
    module Gₚ = AbelianGroupProperties G
    open CommSemigroupProperties G.commutativeSemigroup using (medial)
    open Gₚ using
      (//-rightDividesˡ; ∙-cancelʳ; ε⁻¹≈ε
      ; ⁻¹-anti-homo‿-; ⁻¹-∙-comm)

    completion : AbelianGroup m (m ⊔ ℓ)
    completion = abelianGroup G.commutativeMonoid

    module C = AbelianGroup completion
    open Consequences C.setoid G.setoid using
      (inverseᵇ⇒bijective; strictlyInverseˡ⇒inverseˡ
      ; strictlyInverseʳ⇒inverseʳ)

    open G using () renaming
      ( _≈_       to _≈g_       ; _∙_       to _+g_
      ; ε         to 0g         ; _⁻¹       to -g_
      ; sym       to ≈g-sym
      ; ∙-congˡ   to +g-congˡ   ; ∙-congʳ   to +g-congʳ
      ; assoc     to +g-assoc   ; comm      to +g-comm
      ; identityʳ to +g-identityʳ
      )

    open ≈-Reasoning G.setoid

    reduce-difference : ∀ a b c →
      (a G.- b) +g (b +g c) ≈g a +g c
    reduce-difference a b c = begin
      (a G.- b) +g (b +g c)  ≈⟨ +g-assoc _ _ _ ⟨
      ((a G.- b) +g b) +g c ≈⟨ +g-congʳ (//-rightDividesˡ _ _) ⟩
      a +g c                 ∎

  self-completion-to-self : C.Carrier → G.Carrier
  self-completion-to-self = Product.uncurry G._-_

  to-self-cong : Congruent C._≈_ G._≈_ self-completion-to-self
  to-self-cong {a , b} {c , d} = Product.uncurry λ slack eq →
    ∙-cancelʳ (b +g d) _ _ (begin
      (a G.- b) +g (b +g d)  ≈⟨ reduce-difference a b d ⟩
      a +g d                 ≈⟨ ∙-cancelʳ slack _ _ eq ⟩
      c +g b                 ≈⟨ reduce-difference c d b ⟨
      (c G.- d) +g (d +g b)  ≈⟨ +g-congˡ (+g-comm b d) ⟨
      (c G.- d) +g (b +g d)  ∎)

  to-self-∙ : ∀ x y →
              self-completion-to-self (C._∙_ x y) ≈g
              self-completion-to-self x +g self-completion-to-self y
  to-self-∙ (a , b) (c , d) = begin
    (a +g c) G.- (b +g d)       ≡⟨⟩
    (a +g c) +g -g (b +g d)  ≈⟨ +g-congˡ (⁻¹-∙-comm _ _) ⟨
    (a +g c) +g (-g b +g -g d)  ≈⟨ medial a c (-g b) (-g d) ⟩
    (a +g -g b) +g (c +g -g d)  ≡⟨⟩
    (a G.- b) +g (c G.- d)      ∎

  to-self-embed : ∀ x →
    self-completion-to-self (embed G.commutativeMonoid x) ≈g x
  to-self-embed x = begin
    x G.- 0g      ≡⟨⟩
    x +g -g 0g    ≈⟨ +g-congˡ ε⁻¹≈ε ⟩
    x +g 0g       ≈⟨ +g-identityʳ x ⟩
    x             ∎

  to-self-⁻¹ : ∀ x →
               self-completion-to-self (C._⁻¹ x) ≈g
               -g self-completion-to-self x
  to-self-⁻¹ (a , b) = ≈g-sym (⁻¹-anti-homo‿- a b)

  to-self-isGroupHomomorphism :
    IsGroupHomomorphism C.rawGroup G.rawGroup self-completion-to-self
  to-self-isGroupHomomorphism = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = to-self-cong }
        ; ∙-homo            = to-self-∙
        }
      ; ε-homo = to-self-embed 0g
      }
    ; ⁻¹-homo = to-self-⁻¹
    }

  embed-to-self : ∀ x →
    embed G.commutativeMonoid (self-completion-to-self x) C.≈ x
  embed-to-self (a , b) = -, (begin
    ((a G.- b) +g b) +g 0g  ≈⟨ +g-identityʳ _ ⟩
    (a G.- b) +g b           ≈⟨ //-rightDividesˡ b a ⟩
    a                        ≈⟨ +g-identityʳ a ⟨
    a +g 0g                  ≈⟨ +g-identityʳ _ ⟨
    (a +g 0g) +g 0g          ∎)

  to-self-bijective :
    Bijective C._≈_ G._≈_ self-completion-to-self
  to-self-bijective = inverseᵇ⇒bijective
    ( strictlyInverseˡ⇒inverseˡ to-self-cong to-self-embed
    , strictlyInverseʳ⇒inverseʳ (embed-cong G.commutativeMonoid)
        embed-to-self
    )

  self-completion-≅ :
    IsGroupIsomorphism C.rawGroup G.rawGroup self-completion-to-self
  self-completion-≅ = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = to-self-isGroupHomomorphism
      ; injective           = proj₁ to-self-bijective
      }
    ; surjective = proj₂ to-self-bijective
    }
