------------------------------------------------------------------------
-- The Agda standard library
--
-- Ring completion of a semiring, freely adjoining negatives
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Algebra.Construct.Add.Negatives.Semiring where

open import Algebra.Bundles
  using (AbelianGroup; CommutativeRing; Ring; Semiring)
import Algebra.Construct.Add.Negatives.CommutativeMonoid as Negatives
import Algebra.Definitions as Definitions
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)
open import Algebra.Morphism.Structures using
  (IsGroupIsomorphism; IsRingHomomorphism; IsRingIsomorphism
  ; IsSemiringHomomorphism)
import Algebra.Properties.CommutativeSemigroup as CSProperties
import Algebra.Properties.Monoid as MonoidProperties
import Algebra.Properties.Ring as RingProperties
open import Algebra.Structures using (IsRing)
open import Data.Product.Base as Product using (_,_; proj₁; proj₂)
open import Function.Definitions using (Congruent)
open import Level using (Level; _⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

module _ {m ℓ : Level} (semiring : Semiring m ℓ) where

  private
    module S = Semiring semiring
    module Sₘ = MonoidProperties S.+-monoid
    open CSProperties S.+-commutativeSemigroup using (medial)

    open S using () renaming
      ( Carrier to Base
      ; _+_     to _+ₛ_ ; _*_ to _*ₛ_ ; _≈_ to _≈ₛ_
      ; 0#      to 0ₛ   ; 1#  to 1ₛ
      )

  ----------------------------------------------------------------------
  -- Additive completion

  private
    -- Ring completion reuses the commutative-monoid completion verbatim
    -- for its additive structure and only extends multiplication below.
    module Additive = AbelianGroup
      (Negatives.abelianGroup S.+-commutativeMonoid)

  open Additive public using (Carrier)
    renaming (_≈_ to _≈_; _∙_ to _+_; ε to 0#; _⁻¹ to -_)
  open Additive using () renaming
    (∙-cong to +-cong; ⁻¹-cong to -‿cong)

  private
    pos neg : Carrier → Base
    pos = proj₁
    neg = proj₂

    ≈-from-parts : ∀ {x y} →
                   pos x S.≈ pos y → neg x S.≈ neg y → x ≈ y
    ≈-from-parts = Negatives.≈-from-parts S.+-commutativeMonoid

    variable
      x y z : Carrier
      a : Base

  open Definitions _≈_ using (Congruent₂)

  ----------------------------------------------------------------------
  -- Multiplication

  infixl 7 _*_

  private
    prod⁺ : Carrier → Carrier → Base
    prod⁺ (a , b) (c , d) = a *ₛ c +ₛ b *ₛ d

  _*_ : Carrier → Carrier → Carrier
  x * y = prod⁺ x y , prod⁺ x (- y)

  1# : Carrier
  1# = 1ₛ , 0ₛ

  private
    scaleˡ : Base → Carrier → Carrier
    scaleˡ a = Product.map (a *ₛ_) (a *ₛ_)

    scaleʳ : Carrier → Base → Carrier
    scaleʳ x a = Product.map (_*ₛ a) (_*ₛ a) x

    -- Mapping a completion equality changes its witness from `slack` to
    -- `f slack`, so the witness must be exposed here.
    map-cong : ∀ f → Congruent _≈ₛ_ _≈ₛ_ f →
      (∀ a b → f (a +ₛ b) ≈ₛ f a +ₛ f b) →
      Congruent _≈_ _≈_ (Product.map f f)
    map-cong f cong homo = Product.map f λ {slack} eq → begin
      f slack +ₛ (f _ +ₛ f _)  ≈⟨ S.+-congˡ (homo _ _) ⟨
      f slack +ₛ f (_ +ₛ _)    ≈⟨ homo slack (_ +ₛ _) ⟨
      f (slack +ₛ (_ +ₛ _))    ≈⟨ cong eq ⟩
      f (slack +ₛ (_ +ₛ _))    ≈⟨ homo slack (_ +ₛ _) ⟩
      f slack +ₛ f (_ +ₛ _)    ≈⟨ S.+-congˡ (homo _ _) ⟩
      f slack +ₛ (f _ +ₛ f _)  ∎
      where open ≈-Reasoning S.setoid

    scale-congˡ : Congruent _≈_ _≈_ (scaleˡ a)
    scale-congˡ {a} = map-cong (a *ₛ_) S.*-congˡ (S.distribˡ a)

    scale-congʳ : Congruent _≈_ _≈_ (λ x → scaleʳ x a)
    scale-congʳ {a} = map-cong (_*ₛ a) S.*-congʳ (S.distribʳ a)

    *-as-scalesʳ : x * y ≈ scaleʳ x (pos y) + - scaleʳ x (neg y)
    *-as-scalesʳ {(a , b)} {(c , d)} =
      ≈-from-parts S.refl (S.+-comm (a *ₛ d) (b *ₛ c))

    *-cong : Congruent₂ _*_
    *-cong {a , b} {a′ , b′} {y} {y′} x≈x′ y≈y′ = begin
      (a , b) * y
        ≈⟨ *-as-scalesʳ ⟩
      scaleʳ (a , b) (pos y) + - scaleʳ (a , b) (neg y)
        ≈⟨ +-cong (scale-congʳ x≈x′) (-‿cong (scale-congʳ x≈x′)) ⟩
      scaleʳ (a′ , b′) (pos y) + - scaleʳ (a′ , b′) (neg y)
        ≈⟨ *-as-scalesʳ ⟨
      (a′ , b′) * y
        ≈⟨ +-cong (scale-congˡ y≈y′) (-‿cong (scale-congˡ y≈y′)) ⟩
      (a′ , b′) * y′  ∎
      where open ≈-Reasoning Additive.setoid

  open ≈-Reasoning S.setoid

  ----------------------------------------------------------------------
  -- Ring laws

  private
    distrib⁺ˡ : ∀ x y z →
      prod⁺ x (y + z) ≈ₛ prod⁺ x y +ₛ prod⁺ x z
    distrib⁺ˡ (x⁺ , x⁻) (y⁺ , y⁻) (z⁺ , z⁻) = begin
      x⁺ *ₛ (y⁺ +ₛ z⁺) +ₛ x⁻ *ₛ (y⁻ +ₛ z⁻)
        ≈⟨ S.+-cong (S.distribˡ _ _ _) (S.distribˡ _ _ _) ⟩
      (x⁺ *ₛ y⁺ +ₛ x⁺ *ₛ z⁺) +ₛ (x⁻ *ₛ y⁻ +ₛ x⁻ *ₛ z⁻)
        ≈⟨ medial _ _ _ _ ⟩
      (x⁺ *ₛ y⁺ +ₛ x⁻ *ₛ y⁻) +ₛ (x⁺ *ₛ z⁺ +ₛ x⁻ *ₛ z⁻)  ∎

    distrib⁺ʳ : ∀ x y z →
      prod⁺ (x + y) z ≈ₛ prod⁺ x z +ₛ prod⁺ y z
    distrib⁺ʳ (x⁺ , x⁻) (y⁺ , y⁻) (z⁺ , z⁻) = begin
      (x⁺ +ₛ y⁺) *ₛ z⁺ +ₛ (x⁻ +ₛ y⁻) *ₛ z⁻
        ≈⟨ S.+-cong (S.distribʳ _ _ _) (S.distribʳ _ _ _) ⟩
      (x⁺ *ₛ z⁺ +ₛ y⁺ *ₛ z⁺) +ₛ (x⁻ *ₛ z⁻ +ₛ y⁻ *ₛ z⁻)
        ≈⟨ medial _ _ _ _ ⟩
      (x⁺ *ₛ z⁺ +ₛ x⁻ *ₛ z⁻) +ₛ (y⁺ *ₛ z⁺ +ₛ y⁻ *ₛ z⁻)  ∎

    scale-prod : ∀ a x y →
      prod⁺ (scaleˡ a x) y ≈ₛ a *ₛ prod⁺ x y
    scale-prod a (b , c) (d , e) = begin
      (a *ₛ b) *ₛ d +ₛ (a *ₛ c) *ₛ e
        ≈⟨ S.+-cong (S.*-assoc _ _ _) (S.*-assoc _ _ _) ⟩
      a *ₛ (b *ₛ d) +ₛ a *ₛ (c *ₛ e)
        ≈⟨ S.distribˡ _ _ _ ⟨
      a *ₛ (b *ₛ d +ₛ c *ₛ e)  ∎

    neg-scale-prod : ∀ a x y →
      prod⁺ (- scaleˡ a x) y ≈ₛ a *ₛ prod⁺ x (- y)
    neg-scale-prod a (b , c) (d , e) = begin
      (a *ₛ c) *ₛ d +ₛ (a *ₛ b) *ₛ e  ≈⟨ scale-prod a (c , b) (d , e) ⟩
      a *ₛ (c *ₛ d +ₛ b *ₛ e)         ≈⟨ S.*-congˡ (S.+-comm _ _) ⟩
      a *ₛ (b *ₛ e +ₛ c *ₛ d)         ∎

    assoc⁺ : ∀ x y z → prod⁺ (x * y) z ≈ₛ prod⁺ x (y * z)
    assoc⁺ (a , b) y z = begin
      prod⁺ ((a , b) * y) z
        ≡⟨⟩
      prod⁺ (scaleˡ a y + - scaleˡ b y) z
        ≈⟨ distrib⁺ʳ (scaleˡ a y) (- scaleˡ b y) z ⟩
      prod⁺ (scaleˡ a y) z +ₛ prod⁺ (- scaleˡ b y) z
        ≈⟨ S.+-cong (scale-prod a y z) (neg-scale-prod b y z) ⟩
      a *ₛ prod⁺ y z +ₛ b *ₛ prod⁺ y (- z)
        ≡⟨⟩
      prod⁺ (a , b) (y * z)  ∎

  ----------------------------------------------------------------------
  -- Bundle

  completion-is-ring : IsRing _≈_ _+_ _*_ -_ 0# 1#
  completion-is-ring = record
    { +-isAbelianGroup = Additive.isAbelianGroup
    ; *-cong           = *-cong
    ; *-assoc          = λ x y z → ≈-from-parts
        (assoc⁺ x y z) (assoc⁺ x y (- z))
    ; *-identity       =
        ( (λ { (x⁺ , x⁻) → ≈-from-parts
            (begin
              1ₛ *ₛ x⁺ +ₛ 0ₛ *ₛ x⁻  ≈⟨ S.+-congʳ (S.*-identityˡ _) ⟩
              x⁺ +ₛ 0ₛ *ₛ x⁻        ≈⟨ Sₘ.elimʳ (S.zeroˡ _) x⁺ ⟩
              x⁺                    ∎)
            (begin
              1ₛ *ₛ x⁻ +ₛ 0ₛ *ₛ x⁺  ≈⟨ S.+-congʳ (S.*-identityˡ _) ⟩
              x⁻ +ₛ 0ₛ *ₛ x⁺        ≈⟨ Sₘ.elimʳ (S.zeroˡ _) x⁻ ⟩
              x⁻                    ∎) })
        , (λ { (x⁺ , x⁻) → ≈-from-parts
            (begin
              x⁺ *ₛ 1ₛ +ₛ x⁻ *ₛ 0ₛ  ≈⟨ S.+-congʳ (S.*-identityʳ _) ⟩
              x⁺ +ₛ x⁻ *ₛ 0ₛ        ≈⟨ Sₘ.elimʳ (S.zeroʳ _) x⁺ ⟩
              x⁺                    ∎)
            (begin
              x⁺ *ₛ 0ₛ +ₛ x⁻ *ₛ 1ₛ  ≈⟨ S.+-congˡ (S.*-identityʳ _) ⟩
              x⁺ *ₛ 0ₛ +ₛ x⁻        ≈⟨ Sₘ.elimˡ (S.zeroʳ _) x⁻ ⟩
              x⁻                    ∎) })
        )
    ; distrib          =
        ( (λ x y z → ≈-from-parts
            (distrib⁺ˡ x y z) (distrib⁺ˡ x (- y) (- z)))
        , (λ x y z → ≈-from-parts
            (distrib⁺ʳ y z x) (distrib⁺ʳ y z (- x)))
        )
    }

  ring : Ring m (m ⊔ ℓ)
  ring = record { isRing = completion-is-ring }

  private module R = Semiring (Ring.semiring ring)
  open Definitions (_≈ₛ_)
    using (Commutative) renaming (LeftZero to LeftAbsorbing)

  ------------------------------------------------------------------------
  -- Commutative specialization

  commutativeRing : Commutative S._*_ → CommutativeRing m (m ⊔ ℓ)
  commutativeRing comm = record
    { isCommutativeRing = record
      { isRing = completion-is-ring
      ; *-comm = λ { (a , b) (c , d) → ≈-from-parts
          (S.+-cong (comm a c) (comm b d))
          (begin
            a *ₛ d +ₛ b *ₛ c  ≈⟨ S.+-cong (comm a d) (comm b c) ⟩
            d *ₛ a +ₛ c *ₛ b  ≈⟨ S.+-comm _ _ ⟩
            c *ₛ b +ₛ d *ₛ a  ∎) }
      }
    }


  ----------------------------------------------------------------------
  -- Canonical embedding

  embed : Base → Carrier
  embed = Negatives.embed S.+-commutativeMonoid

  decompose : ∀ x → x ≈ embed (proj₁ x) + - embed (proj₂ x)
  decompose = Negatives.decompose S.+-commutativeMonoid

  embed-* : ∀ x y → embed (x *ₛ y) ≈ embed x * embed y
  embed-* x y = ≈-from-parts
    (Sₘ.introʳ (S.zeroˡ 0ₛ) (x *ₛ y))
    (begin
      0ₛ                      ≈⟨ S.zeroˡ y ⟨
      0ₛ *ₛ y                 ≈⟨ Sₘ.introˡ (S.zeroʳ x) _ ⟩
      (x *ₛ 0ₛ) +ₛ (0ₛ *ₛ y)  ∎)

  embed-isSemiringHomomorphism :
    IsSemiringHomomorphism S.rawSemiring R.rawSemiring embed
  embed-isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism =
          Negatives.embed-isMonoidHomomorphism
            S.+-commutativeMonoid
      ; *-homo                 = embed-*
      }
    ; 1#-homo = Additive.refl
    }

  embed-semiringHomomorphism :
    SemiringHomomorphism S.rawSemiring R.rawSemiring
  embed-semiringHomomorphism = record
    { isSemiringHomomorphism = embed-isSemiringHomomorphism }


  ----------------------------------------------------------------------
  -- Trivial completions

  +-absorbing⇒trivial : (∞ : Base) → LeftAbsorbing ∞ S._+_ →
                        ∀ x → x ≈ 0#
  +-absorbing⇒trivial =
    Negatives.absorbing⇒trivial S.+-commutativeMonoid

  +-absorbing⇒1#≈0# : (∞ : Base) → LeftAbsorbing ∞ S._+_ →
                      1# ≈ 0#
  +-absorbing⇒1#≈0# ∞ absorbˡ = +-absorbing⇒trivial ∞ absorbˡ 1#


------------------------------------------------------------------------
-- Completion of a ring

module AlreadyRing {m ℓ : Level} (R : Ring m ℓ) where

  private
    module R = Ring R
    module Rₚ = RingProperties R
    open CSProperties R.+-commutativeSemigroup using (medial)
    module Additive = Negatives.AlreadyGroup R.+-abelianGroup
    module Additive≅ = IsGroupIsomorphism Additive.self-completion-≅

    module C = Ring (ring R.semiring)

    open ≈-Reasoning R.setoid

  self-completion-to-self : C.Carrier → R.Carrier
  self-completion-to-self = Product.uncurry R._-_

  to-self-* : ∀ x y →
              self-completion-to-self (C._*_ x y) R.≈
              self-completion-to-self x R.* self-completion-to-self y
  to-self-* (a , b) (c , d) = begin
    (a R.* c R.+ b R.* d) R.- (a R.* d R.+ b R.* c)  ≡⟨⟩
    (a R.* c R.+ b R.* d) R.+ R.-_ (a R.* d R.+ b R.* c)
      ≈⟨ R.+-congˡ (Rₚ.-‿+-comm (a R.* d) (b R.* c)) ⟨
    (a R.* c R.+ b R.* d) R.+
      (R.-_ (a R.* d) R.+ R.-_ (b R.* c))
      ≈⟨ medial (a R.* c) (b R.* d)
               (R.-_ (a R.* d)) (R.-_ (b R.* c)) ⟩
    (a R.* c R.- a R.* d) R.+ (b R.* d R.- b R.* c)
      ≈⟨ R.+-congˡ (Rₚ.⁻¹-anti-homo‿- (b R.* c) (b R.* d)) ⟨
    (a R.* c R.- a R.* d) R.- (b R.* c R.- b R.* d)
      ≈⟨ R.+-cong (Rₚ.x[y-z]≈xy-xz a c d)
                   (R.-‿cong (Rₚ.x[y-z]≈xy-xz b c d)) ⟨
    a R.* (c R.- d) R.- b R.* (c R.- d)
      ≈⟨ Rₚ.[y-z]x≈yx-zx (c R.- d) a b ⟨
    (a R.- b) R.* (c R.- d)                           ∎

  to-self-isRingHomomorphism :
    IsRingHomomorphism C.rawRing R.rawRing self-completion-to-self
  to-self-isRingHomomorphism = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = Additive≅.isMonoidHomomorphism
        ; *-homo                 = to-self-*
        }
      ; 1#-homo = Additive.to-self-embed R.1#
      }
    ; -‿homo = Additive≅.⁻¹-homo
    }

  self-completion-≅ :
    IsRingIsomorphism C.rawRing R.rawRing self-completion-to-self
  self-completion-≅ = record
    { isRingMonomorphism = record
      { isRingHomomorphism = to-self-isRingHomomorphism
      ; injective          = Additive≅.injective
      }
    ; surjective = Additive≅.surjective
    }
