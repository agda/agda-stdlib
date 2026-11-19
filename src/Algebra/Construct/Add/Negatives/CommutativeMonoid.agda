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
import Algebra.Properties.Monoid as MonoidProperties
open import Algebra.Structures using (IsAbelianGroup)
open import Data.Product.Base as Product
  using (∃-syntax; _,_; -,_; <_,_>; proj₁; proj₂; uncurry)
open import Function.Base using (const; id; _∘_; _∘₂_)
import Function.Consequences.Setoid as Consequences
open import Function.Definitions using (Bijective; Congruent)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)

module _ {m ℓ : Level} (monoid : CommutativeMonoid m ℓ) where

  private
    module M = CommutativeMonoid monoid
    module Mₚ = MonoidProperties M.monoid
    open M using (commutativeSemigroup; rawMonoid; setoid)
      renaming
      ( Carrier   to Base         ; _≈_       to _≈ₘ_
      ; _∙_       to _+ₘ_         ; ε         to 0ₘ
      ; refl      to ≈ₘ-refl      ; sym       to ≈ₘ-sym
      ; comm      to +ₘ-comm      ; ∙-cong    to +ₘ-cong
      ; ∙-congˡ   to +ₘ-congˡ     ; ∙-congʳ   to +ₘ-congʳ
      ; identityˡ to +ₘ-identityˡ ; identityʳ to +ₘ-identityʳ
      )

    module M² = CommutativeMonoid
      (DirectProduct.commutativeMonoid monoid monoid)
    open CommSemigroupProperties commutativeSemigroup using (medial)

  open ≈-Reasoning setoid


  ------------------------------------------------------------------------
  -- Formal differences

  open M² public using (Carrier) renaming (_∙_ to _+_; ε to 0#)

  ------------------------------------------------------------------------
  -- Equality

  infix 4 _≈₀_ _≈_

  -- The zero-slack balance relation. It need not be transitive unless
  -- the original monoid is cancellative.
  _≈₀_ : Rel Carrier ℓ
  (a , b) ≈₀ (c , d) = a +ₘ d ≈ₘ c +ₘ b

  -- The completion relation stabilizes _≈₀_ by a common left summand.
  _≈_ : Rel Carrier (m ⊔ ℓ)
  (a , b) ≈ (c , d) = ∃[ slack ]
    slack +ₘ (a +ₘ d) ≈ₘ slack +ₘ (c +ₘ b)

  open Definitions _≈_ using (Congruent₁; Congruent₂; LeftInverse)

  private
    rearrange : ∀ a b c d u v →
                (u +ₘ v) +ₘ ((a +ₘ c) +ₘ (b +ₘ d)) ≈ₘ
                (u +ₘ (a +ₘ b)) +ₘ (v +ₘ (c +ₘ d))
    rearrange a b c d u v = begin
      (u +ₘ v) +ₘ ((a +ₘ c) +ₘ (b +ₘ d))
        ≈⟨ +ₘ-comm _ _ ⟩
      ((a +ₘ c) +ₘ (b +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ +ₘ-congʳ (medial a c b d) ⟩
      ((a +ₘ b) +ₘ (c +ₘ d)) +ₘ (u +ₘ v)
        ≈⟨ medial (a +ₘ b) (c +ₘ d) u v ⟩
      ((a +ₘ b) +ₘ u) +ₘ ((c +ₘ d) +ₘ v)
        ≈⟨ +ₘ-cong (+ₘ-comm _ _) (+ₘ-comm _ _) ⟩
      (u +ₘ (a +ₘ b)) +ₘ (v +ₘ (c +ₘ d))  ∎

    composeˡ : ∀ a b c d u v →
               ((u +ₘ v) +ₘ (c +ₘ d)) +ₘ (a +ₘ b) ≈ₘ
               (u +ₘ (a +ₘ d)) +ₘ (v +ₘ (c +ₘ b))
    composeˡ a b c d u v = begin
      ((u +ₘ v) +ₘ (c +ₘ d)) +ₘ (a +ₘ b)
        ≈⟨ M.assoc (u +ₘ v) (c +ₘ d) (a +ₘ b) ⟩
      (u +ₘ v) +ₘ ((c +ₘ d) +ₘ (a +ₘ b))
        ≈⟨ +ₘ-congˡ (medial c d a b) ⟩
      (u +ₘ v) +ₘ ((c +ₘ a) +ₘ (d +ₘ b))
        ≈⟨ +ₘ-congˡ (+ₘ-congʳ (+ₘ-comm c a)) ⟩
      (u +ₘ v) +ₘ ((a +ₘ c) +ₘ (d +ₘ b))
        ≈⟨ rearrange a d c b u v ⟩
      (u +ₘ (a +ₘ d)) +ₘ (v +ₘ (c +ₘ b))  ∎

  ≈₀⇒≈ : ∀ {x y} → x ≈₀ y → x ≈ y
  ≈₀⇒≈ eq = 0ₘ , +ₘ-congˡ eq

  ≈-from-parts : ∀ {a b c d} → a ≈ₘ c → b ≈ₘ d → (a , b) ≈ (c , d)
  ≈-from-parts x⁺≈y⁺ x⁻≈y⁻ = ≈₀⇒≈ (+ₘ-cong x⁺≈y⁺ (≈ₘ-sym x⁻≈y⁻))

  private
    pointwise⇒≈ : ∀ {x y} → M²._≈_ x y → x ≈ y
    pointwise⇒≈ = uncurry ≈-from-parts

  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record
    { refl  = pointwise⇒≈ M².refl
    ; sym   = Product.map₂ ≈ₘ-sym
    ; trans = λ { {a , b} {c , d} {e , f} →
        Product.zip (λ u v → (u +ₘ v) +ₘ (c +ₘ d))
        λ {u} {v} eq₁ eq₂ → begin
          ((u +ₘ v) +ₘ (c +ₘ d)) +ₘ (a +ₘ f)
            ≈⟨ composeˡ a f c d u v ⟩
          (u +ₘ (a +ₘ d)) +ₘ (v +ₘ (c +ₘ f))
            ≈⟨ +ₘ-cong eq₁ eq₂ ⟩
          (u +ₘ (c +ₘ b)) +ₘ (v +ₘ (e +ₘ d))
            ≈⟨ +ₘ-comm _ _ ⟩
          (v +ₘ (e +ₘ d)) +ₘ (u +ₘ (c +ₘ b))
            ≈⟨ composeˡ e b c d v u ⟨
          ((v +ₘ u) +ₘ (c +ₘ d)) +ₘ (e +ₘ b)
            ≈⟨ +ₘ-congʳ (+ₘ-congʳ (+ₘ-comm v u)) ⟩
          ((u +ₘ v) +ₘ (c +ₘ d)) +ₘ (e +ₘ b)  ∎ }
    }

  private module ≈ = IsEquivalence ≈-isEquivalence

  ------------------------------------------------------------------------
  -- Operations

  infix  8 -_

  -_ : Carrier → Carrier
  -_ = Product.swap

  +-cong : Congruent₂ _+_
  +-cong {a , b} {a′ , b′} {c , d} {c′ , d′} =
    Product.zip _+ₘ_ λ {u} {v} eq₁ eq₂ → begin
      (u +ₘ v) +ₘ ((a +ₘ c) +ₘ (b′ +ₘ d′))  ≈⟨ rearrange a b′ c d′ u v ⟩
      (u +ₘ (a +ₘ b′)) +ₘ (v +ₘ (c +ₘ d′))  ≈⟨ +ₘ-cong eq₁ eq₂ ⟩
      (u +ₘ (a′ +ₘ b)) +ₘ (v +ₘ (c′ +ₘ d))  ≈⟨ rearrange a′ b c′ d u v ⟨
      (u +ₘ v) +ₘ ((a′ +ₘ c′) +ₘ (b +ₘ d))  ∎

  -‿cong : Congruent₁ -_
  -‿cong {a , b} {c , d} = Product.map₂ λ {u} eq → begin
    u +ₘ (b +ₘ c)  ≈⟨ +ₘ-congˡ (+ₘ-comm b c) ⟩
    u +ₘ (c +ₘ b)  ≈⟨ eq ⟨
    u +ₘ (a +ₘ d)  ≈⟨ +ₘ-congˡ (+ₘ-comm a d) ⟩
    u +ₘ (d +ₘ a)  ∎

  +-inverseˡ : LeftInverse 0# -_ _+_
  +-inverseˡ (a , b) = -, (begin
    0ₘ +ₘ ((b +ₘ a) +ₘ 0ₘ)  ≈⟨ +ₘ-identityˡ _ ⟩
    (b +ₘ a) +ₘ 0ₘ          ≈⟨ +ₘ-identityʳ _ ⟩
    b +ₘ a                  ≈⟨ +ₘ-comm b a ⟩
    a +ₘ b                  ≈⟨ +ₘ-identityˡ _ ⟨
    0ₘ +ₘ (a +ₘ b)          ≈⟨ +ₘ-congˡ (+ₘ-identityˡ _) ⟨
    0ₘ +ₘ (0ₘ +ₘ (a +ₘ b))  ∎)

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
      ; inverse = +-inverseˡ , +-inverseˡ ∘ -_
      ; ⁻¹-cong = -‿cong
      }
    ; comm = pointwise⇒≈ ∘₂ M².comm
    }

  abelianGroup : AbelianGroup m (m ⊔ ℓ)
  abelianGroup = record { isAbelianGroup = completion-is-abelian-group }

  open AbelianGroup abelianGroup
    using () renaming (rawMonoid to rawMonoid#)

  ------------------------------------------------------------------------
  -- Canonical embedding

  embed : Base → Carrier
  embed = < id , const 0ₘ >

  embed-cong : Congruent _≈ₘ_ _≈_ embed
  embed-cong x≈y = ≈-from-parts x≈y ≈ₘ-refl

  embed-∙ : ∀ x y → embed (x +ₘ y) ≈ embed x + embed y
  embed-∙ x y = ≈-from-parts ≈ₘ-refl (Mₚ.introˡ ≈ₘ-refl 0ₘ)

  embed-isMonoidHomomorphism :
    IsMonoidHomomorphism rawMonoid rawMonoid# embed
  embed-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = embed-cong }
      ; ∙-homo            = embed-∙
      }
    ; ε-homo = ≈.refl
    }

  embed-monoidHomomorphism :
    MonoidHomomorphism rawMonoid rawMonoid#
  embed-monoidHomomorphism = record
    { isMonoidHomomorphism = embed-isMonoidHomomorphism }

  decompose : ∀ x → x ≈ embed (proj₁ x) + - embed (proj₂ x)
  decompose (a , b) =
    ≈-from-parts (Mₚ.introʳ ≈ₘ-refl a)
                 (Mₚ.introˡ ≈ₘ-refl b)


  ------------------------------------------------------------------------
  -- Trivial completions

  open Definitions _≈ₘ_ using () renaming (LeftZero to LeftAbsorbing)

  absorbing⇒trivial : (∞ : Base) → LeftAbsorbing ∞ _+ₘ_ →
                      ∀ x → x ≈ 0#
  absorbing⇒trivial ∞ absorbˡ (a , b) = -, (begin
    ∞ +ₘ (a +ₘ 0ₘ)  ≈⟨ absorbˡ (a +ₘ 0ₘ) ⟩
    ∞               ≈⟨ absorbˡ (0ₘ +ₘ b) ⟨
    ∞ +ₘ (0ₘ +ₘ b)  ∎)


------------------------------------------------------------------------
-- Completion of an abelian group

module AlreadyGroup {m ℓ : Level} (G : AbelianGroup m ℓ) where

  private
    module G = AbelianGroup G
    module Gₚ = AbelianGroupProperties G
    module Gₘ = MonoidProperties G.monoid
    open CommSemigroupProperties G.commutativeSemigroup using (medial)
    open Gₘ using (cancelᶜ; elimʳ; introʳ)
    open Gₚ using
      (∙-cancelˡ; ∙-cancelʳ; ε⁻¹≈ε; ⁻¹-anti-homo‿-; ⁻¹-∙-comm)

    module C = AbelianGroup (abelianGroup G.commutativeMonoid)
    open Consequences C.setoid G.setoid using
      (inverseᵇ⇒bijective; strictlyInverseˡ⇒inverseˡ
      ; strictlyInverseʳ⇒inverseʳ)

    open ≈-Reasoning G.setoid

  self-completion-to-self : C.Carrier → G.Carrier
  self-completion-to-self = Product.uncurry G._-_

  to-self-cong : Congruent C._≈_ G._≈_ self-completion-to-self
  to-self-cong {a , b} {c , d} = Product.uncurry λ slack eq →
    ∙-cancelʳ (b G.∙ d) _ _ (begin
      (a G.- b) G.∙ (b G.∙ d)   ≈⟨ cancelᶜ (G.inverseˡ b) a d ⟩
      a G.∙ d                   ≈⟨ ∙-cancelˡ slack _ _ eq ⟩
      c G.∙ b                   ≈⟨ cancelᶜ (G.inverseˡ d) c b ⟨
      (c G.- d) G.∙ (d G.∙ b)   ≈⟨ G.∙-congˡ (G.comm b d) ⟨
      (c G.- d) G.∙ (b G.∙ d)   ∎)

  to-self-∙ : ∀ x y →
              self-completion-to-self (C._∙_ x y) G.≈
              self-completion-to-self x G.∙ self-completion-to-self y
  to-self-∙ (a , b) (c , d) = begin
    (a G.∙ c) G.- (b G.∙ d)           ≡⟨⟩
    (a G.∙ c) G.∙ (b G.∙ d) G.⁻¹      ≈⟨ G.∙-congˡ (⁻¹-∙-comm _ _) ⟨
    (a G.∙ c) G.∙ (b G.⁻¹ G.∙ d G.⁻¹) ≈⟨ medial a c (b G.⁻¹) (d G.⁻¹) ⟩
    (a G.∙ b G.⁻¹) G.∙ (c G.∙ d G.⁻¹) ≡⟨⟩
    (a G.- b) G.∙ (c G.- d)           ∎

  to-self-embed : ∀ x →
    self-completion-to-self (embed G.commutativeMonoid x) G.≈ x
  to-self-embed x = elimʳ ε⁻¹≈ε x

  to-self-⁻¹ : ∀ x →
               self-completion-to-self (C._⁻¹ x) G.≈
               self-completion-to-self x G.⁻¹
  to-self-⁻¹ (a , b) = G.sym (⁻¹-anti-homo‿- a b)

  to-self-isGroupHomomorphism :
    IsGroupHomomorphism C.rawGroup G.rawGroup self-completion-to-self
  to-self-isGroupHomomorphism = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = to-self-cong }
        ; ∙-homo            = to-self-∙
        }
      ; ε-homo = to-self-embed G.ε
      }
    ; ⁻¹-homo = to-self-⁻¹
    }

  embed-to-self : ∀ x →
    embed G.commutativeMonoid (self-completion-to-self x) C.≈ x
  embed-to-self (a , b) = -, (begin
    G.ε G.∙ ((a G.- b) G.∙ b)   ≈⟨ G.identityˡ _ ⟩
    (a G.- b) G.∙ b             ≈⟨ Gₘ.cancelʳ (G.inverseˡ b) a ⟩
    a                           ≈⟨ introʳ G.refl _ ⟩
    a G.∙ G.ε                   ≈⟨ G.identityˡ _ ⟨
    G.ε G.∙ (a G.∙ G.ε)         ∎)

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
