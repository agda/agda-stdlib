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
import Algebra.Properties.Ring as RingProperties
open import Algebra.Structures using (IsRing)
open import Data.Product.Base as Product
  using (_,_; <_,_>)
open import Function.Base using (_∘_; _∘₂_)
open import Function.Definitions using (Congruent)
open import Level using (Level; _⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)

module _ {m ℓ : Level} (semiring : Semiring m ℓ) where

  private
    module S = Semiring semiring
    open CSProperties S.+-commutativeSemigroup using (medial)

    open S using () renaming
      ( Carrier to Base
      ; _+_     to _+ₛ_ ; _*_ to _*ₛ_ ; _≈_ to _≈ₛ_
      ; 0#      to 0ₛ   ; 1#  to 1ₛ
      )

  ----------------------------------------------------------------------
  -- Additive completion

  private
    +Group : AbelianGroup m (m ⊔ ℓ)
    +Group = Negatives.abelianGroup S.+-commutativeMonoid

    module Additive = AbelianGroup +Group

  open Additive public using (Carrier)
    renaming (_≈_ to _≈_; _∙_ to _+_; ε to 0#; _⁻¹ to -_)
  open Additive using () renaming
    (∙-cong to +-cong; ⁻¹-cong to -‿cong)

  pos neg : Carrier → Base
  pos = Negatives.pos S.+-commutativeMonoid
  neg = Negatives.neg S.+-commutativeMonoid

  private
    ≈-from-parts : ∀ {x y} →
                   pos x S.≈ pos y → neg x S.≈ neg y → x ≈ y
    ≈-from-parts = Negatives.≈-from-parts S.+-commutativeMonoid

    module ≈ = IsEquivalence Additive.isEquivalence

    variable
      x y z : Carrier
      a b c d : Base

    infix 4 _≈[_]_
    _≈[_]_ : Carrier → Base → Carrier → Set ℓ
    x ≈[ slack ] y =
      (pos x +ₛ neg y) +ₛ slack ≈ₛ (pos y +ₛ neg x) +ₛ slack

  open Definitions _≈_ using
    (Associative; Congruent₂; LeftCongruent; LeftIdentity
    ; RightCongruent; RightIdentity
    ; _DistributesOverˡ_; _DistributesOverʳ_)
  open Definitions (_≈ₛ_) using (Commutative; RightZero)

  ----------------------------------------------------------------------
  -- Addition permutations

  private
    swap-middle : ∀ p q r s →
                  (p +ₛ q) +ₛ (r +ₛ s) ≈ₛ
                  (p +ₛ r) +ₛ (s +ₛ q)
    swap-middle p q r s = S.trans
      (medial p q r s)
      (S.+-congˡ (S.+-comm q s))

  ----------------------------------------------------------------------
  -- Multiplication

  infixl 7 _*_

  private
    prod⁺ : Carrier → Carrier → Base
    prod⁺ = Product.uncurry′ S._+_ ∘₂ Product.zip′ S._*_ S._*_

  _*_ : Carrier → Carrier → Carrier
  _*_ x = < prod⁺ x , prod⁺ x ∘ -_ >

  1# : Carrier
  1# = 1ₛ , 0ₛ

  private
    scaleˡ : Base → Carrier → Carrier
    scaleˡ a = Product.map (a *ₛ_) (a *ₛ_)

    scaleʳ : Carrier → Base → Carrier
    scaleʳ x a = Product.map (_*ₛ a) (_*ₛ a) x

    map-cong : ∀ f → Congruent _≈ₛ_ _≈ₛ_ f →
      (∀ a b c → f ((a +ₛ b) +ₛ c) ≈ₛ
                   (f a +ₛ f b) +ₛ f c) →
      Congruent _≈_ _≈_ (Product.map f f)
    map-cong f cong distrib = Product.map f λ {slack} eq → begin
      (f _ +ₛ f _) +ₛ f slack  ≈⟨ distrib _ _ slack ⟨
      f ((_ +ₛ _) +ₛ slack)    ≈⟨ cong eq ⟩
      f ((_ +ₛ _) +ₛ slack)    ≈⟨ distrib _ _ slack ⟩
      (f _ +ₛ f _) +ₛ f slack  ∎
      where open ≈-Reasoning S.setoid

    scale-congˡ : Congruent _≈_ _≈_ (scaleˡ a)
    scale-congˡ {a} = map-cong (a *ₛ_) S.*-congˡ λ x y z →
      S.trans (S.distribˡ _ _ _) (S.+-congʳ (S.distribˡ _ _ _))

    scale-congʳ : Congruent _≈_ _≈_ (λ x → scaleʳ x a)
    scale-congʳ {a} = map-cong (_*ₛ a) S.*-congʳ λ x y z →
      S.trans (S.distribʳ _ _ _) (S.+-congʳ (S.distribʳ _ _ _))

    *-as-scalesʳ : x * y ≈ scaleʳ x (pos y) + - scaleʳ x (neg y)
    *-as-scalesʳ {(a , b)} {(c , d)} =
      ≈-from-parts S.refl (S.+-comm (a *ₛ d) (b *ₛ c))

  *-congʳ : RightCongruent _*_
  *-congʳ {y} {x} {x′} x≈x′ = begin
    x * y
      ≈⟨ *-as-scalesʳ ⟩
    scaleʳ x (pos y) + - scaleʳ x (neg y)
      ≈⟨ +-cong (scale-congʳ x≈x′)
                 (-‿cong (scale-congʳ x≈x′)) ⟩
    scaleʳ x′ (pos y) + - scaleʳ x′ (neg y)
      ≈⟨ *-as-scalesʳ ⟨
    x′ * y  ∎
    where open ≈-Reasoning Additive.setoid

  *-congˡ : LeftCongruent _*_
  *-congˡ {x} y≈y′ =
    +-cong (scale-congˡ y≈y′) (-‿cong (scale-congˡ y≈y′))

  *-cong : Congruent₂ _*_
  *-cong x≈ y≈ = ≈.trans (*-congʳ x≈) (*-congˡ y≈)

  open ≈-Reasoning S.setoid

  ----------------------------------------------------------------------
  -- Ring laws

  private
    distrib⁺ˡ : ∀ x y z →
      prod⁺ x (y + z) ≈ₛ prod⁺ x y +ₛ prod⁺ x z
    distrib⁺ˡ (x⁺ , x⁻) (y⁺ , y⁻) (z⁺ , z⁻) =
      S.trans
      (S.+-cong (S.distribˡ _ _ _) (S.distribˡ _ _ _))
      (medial (x⁺ *ₛ y⁺) (x⁺ *ₛ z⁺)
              (x⁻ *ₛ y⁻) (x⁻ *ₛ z⁻))

    distrib⁺ʳ : ∀ x y z →
      prod⁺ (x + y) z ≈ₛ prod⁺ x z +ₛ prod⁺ y z
    distrib⁺ʳ (x⁺ , x⁻) (y⁺ , y⁻) (z⁺ , z⁻) =
      S.trans
      (S.+-cong (S.distribʳ _ _ _) (S.distribʳ _ _ _))
      (medial (x⁺ *ₛ z⁺) (y⁺ *ₛ z⁺)
              (x⁻ *ₛ z⁻) (y⁻ *ₛ z⁻))

    assoc⁺ : ∀ x y z → prod⁺ (x * y) z ≈ₛ prod⁺ x (y * z)
    assoc⁺ (x⁺ , x⁻) (y⁺ , y⁻) (z⁺ , z⁻) = begin
      (((x⁺ *ₛ y⁺) +ₛ (x⁻ *ₛ y⁻)) *ₛ z⁺) +ₛ
        (((x⁺ *ₛ y⁻) +ₛ (x⁻ *ₛ y⁺)) *ₛ z⁻)
        ≈⟨ S.+-cong (S.distribʳ _ _ _) (S.distribʳ _ _ _) ⟩
      (((x⁺ *ₛ y⁺) *ₛ z⁺) +ₛ ((x⁻ *ₛ y⁻) *ₛ z⁺))
        +ₛ (((x⁺ *ₛ y⁻) *ₛ z⁻)
          +ₛ ((x⁻ *ₛ y⁺) *ₛ z⁻))
        ≈⟨ S.+-cong (S.+-cong (S.*-assoc _ _ _) (S.*-assoc _ _ _))
                     (S.+-cong (S.*-assoc _ _ _) (S.*-assoc _ _ _)) ⟩
      (x⁺ *ₛ (y⁺ *ₛ z⁺)) +ₛ (x⁻ *ₛ (y⁻ *ₛ z⁺))
        +ₛ ((x⁺ *ₛ (y⁻ *ₛ z⁻))
          +ₛ (x⁻ *ₛ (y⁺ *ₛ z⁻)))
        ≈⟨ swap-middle _ _ _ _ ⟩
      (x⁺ *ₛ (y⁺ *ₛ z⁺)) +ₛ (x⁺ *ₛ (y⁻ *ₛ z⁻))
        +ₛ ((x⁻ *ₛ (y⁺ *ₛ z⁻))
          +ₛ (x⁻ *ₛ (y⁻ *ₛ z⁺)))
        ≈⟨ S.+-cong (S.distribˡ _ _ _) (S.distribˡ _ _ _) ⟨
      (x⁺ *ₛ ((y⁺ *ₛ z⁺) +ₛ (y⁻ *ₛ z⁻))) +ₛ
        (x⁻ *ₛ ((y⁺ *ₛ z⁻) +ₛ (y⁻ *ₛ z⁺)))  ∎

    *-assoc : Associative _*_
    *-assoc x y z = ≈-from-parts
      (assoc⁺ x y z) (assoc⁺ x y (- z))

    *-identityˡ : LeftIdentity 1# _*_
    *-identityˡ (x⁺ , x⁻) = ≈-from-parts
      (S.trans (S.+-cong (S.*-identityˡ _) (S.zeroˡ _))
               (S.+-identityʳ x⁺))
      (S.trans (S.+-cong (S.*-identityˡ _) (S.zeroˡ _))
               (S.+-identityʳ x⁻))

    *-identityʳ : RightIdentity 1# _*_
    *-identityʳ (x⁺ , x⁻) = ≈-from-parts
      (S.trans (S.+-cong (S.*-identityʳ _) (S.zeroʳ _))
               (S.+-identityʳ x⁺))
      (S.trans (S.+-comm (x⁺ *ₛ 0ₛ) (x⁻ *ₛ 1ₛ))
        (S.trans (S.+-cong (S.*-identityʳ _) (S.zeroʳ _))
                 (S.+-identityʳ x⁻)))

    distribˡ : _*_ DistributesOverˡ _+_
    distribˡ x y z = ≈-from-parts
      (distrib⁺ˡ x y z) (distrib⁺ˡ x (- y) (- z))

    distribʳ : _*_ DistributesOverʳ _+_
    distribʳ x y z = ≈-from-parts
      (distrib⁺ʳ y z x) (distrib⁺ʳ y z (- x))

  ----------------------------------------------------------------------
  -- Bundle

  completion-is-ring : IsRing _≈_ _+_ _*_ -_ 0# 1#
  completion-is-ring = record
    { +-isAbelianGroup = AbelianGroup.isAbelianGroup +Group
    ; *-cong           = *-cong
    ; *-assoc          = *-assoc
    ; *-identity       = *-identityˡ , *-identityʳ
    ; distrib          = distribˡ , distribʳ
    }

  ring : Ring m (m ⊔ ℓ)
  ring = record
    { Carrier = Carrier
    ; _≈_     = _≈_
    ; _+_     = _+_
    ; _*_     = _*_
    ; -_      = -_
    ; 0#      = 0#
    ; 1#      = 1#
    ; isRing  = completion-is-ring
    }

  private module R = Semiring (Ring.semiring ring)

  ------------------------------------------------------------------------
  -- Commutative specialization

  private
    *-comm : Commutative S._*_ → ∀ x y → x * y ≈ y * x
    *-comm comm (a , b) (c , d) = ≈-from-parts
      (S.+-cong (comm a c) (comm b d))
      (begin
        (a *ₛ d) +ₛ (b *ₛ c)
          ≈⟨ S.+-cong (comm a d) (comm b c) ⟩
        (d *ₛ a) +ₛ (c *ₛ b)
          ≈⟨ S.+-comm (d *ₛ a) (c *ₛ b) ⟩
        (c *ₛ b) +ₛ (d *ₛ a)  ∎)

  commutativeRing : Commutative S._*_ → CommutativeRing m (m ⊔ ℓ)
  commutativeRing comm = record
    { isCommutativeRing = record
      { isRing = completion-is-ring
      ; *-comm = *-comm comm
      }
    }


  ----------------------------------------------------------------------
  -- Canonical embedding

  embed : Base → Carrier
  embed = Negatives.embed S.+-commutativeMonoid

  decompose : ∀ x → x ≈ embed (pos x) + - embed (neg x)
  decompose = Negatives.decompose S.+-commutativeMonoid

  embed-* : ∀ x y → embed (x *ₛ y) ≈ embed x * embed y
  embed-* x y = ≈-from-parts
    (begin
      x *ₛ y                  ≈⟨ S.+-identityʳ _ ⟨
      (x *ₛ y) +ₛ 0ₛ          ≈⟨ S.+-congˡ (S.zeroˡ _) ⟨
      (x *ₛ y) +ₛ (0ₛ *ₛ 0ₛ)  ∎)
    (begin
      0ₛ                     ≈⟨ S.+-identityˡ _ ⟨
      0ₛ +ₛ 0ₛ                ≈⟨ S.+-cong (S.zeroʳ _) (S.zeroˡ _) ⟨
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
    ; 1#-homo = ≈.refl
    }

  embed-semiringHomomorphism :
    SemiringHomomorphism S.rawSemiring R.rawSemiring
  embed-semiringHomomorphism = record
    { ⟦_⟧                     = embed
    ; isSemiringHomomorphism = embed-isSemiringHomomorphism
    }


  ----------------------------------------------------------------------
  -- Trivial completions

  +-absorbing⇒trivial : (∞ : Base) → RightZero ∞ S._+_ →
                        ∀ x → x ≈ 0#
  +-absorbing⇒trivial =
    Negatives.absorbing⇒trivial S.+-commutativeMonoid

  +-absorbing⇒1#≈0# : (∞ : Base) →
                      RightZero ∞ S._+_ → 1# ≈ 0#
  +-absorbing⇒1#≈0# ∞ zeroʳ = +-absorbing⇒trivial ∞ zeroʳ 1#


------------------------------------------------------------------------
-- Completion of a ring

module AlreadyRing {m ℓ : Level} (R : Ring m ℓ) where

  private
    module R = Ring R
    module Rₚ = RingProperties R
    open CSProperties R.+-commutativeSemigroup using (medial)
    module Additive = Negatives.AlreadyGroup R.+-abelianGroup
    module Additive≅ = IsGroupIsomorphism Additive.self-completion-≅

    completion : Ring m (m ⊔ ℓ)
    completion = ring R.semiring

    module C = Ring completion

    open R using () renaming
      ( _≈_         to _≈r_         ; _+_         to _+r_
      ; _*_         to _*r_         ; -_          to -r_
      ; 0#          to 0r           ; 1#          to 1r
      ; +-cong      to +r-cong      ; +-congˡ     to +r-congˡ
      )

    open ≈-Reasoning R.setoid

  self-completion-to-self : C.Carrier → R.Carrier
  self-completion-to-self = Product.uncurry R._-_

  to-self-* : ∀ x y →
              self-completion-to-self (C._*_ x y) ≈r
              self-completion-to-self x *r self-completion-to-self y
  to-self-* (a , b) (c , d) = begin
    (a *r c +r b *r d) R.- (a *r d +r b *r c)       ≡⟨⟩
    (a *r c +r b *r d) +r -r (a *r d +r b *r c)
      ≈⟨ +r-congˡ (Rₚ.-‿+-comm (a *r d) (b *r c)) ⟨
    (a *r c +r b *r d) +r (-r (a *r d) +r -r (b *r c))
      ≈⟨ medial (a *r c) (b *r d)
               (-r (a *r d)) (-r (b *r c)) ⟩
    (a *r c R.- a *r d) +r (b *r d R.- b *r c)
      ≈⟨ +r-congˡ (Rₚ.⁻¹-anti-homo‿- (b *r c) (b *r d)) ⟨
    (a *r c R.- a *r d) R.- (b *r c R.- b *r d)
      ≈⟨ +r-cong (Rₚ.x[y-z]≈xy-xz a c d)
                  (R.-‿cong (Rₚ.x[y-z]≈xy-xz b c d)) ⟨
    a *r (c R.- d) R.- b *r (c R.- d)
      ≈⟨ Rₚ.[y-z]x≈yx-zx (c R.- d) a b ⟨
    (a R.- b) *r (c R.- d)                           ∎

  to-self-isRingHomomorphism :
    IsRingHomomorphism C.rawRing R.rawRing self-completion-to-self
  to-self-isRingHomomorphism = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = Additive≅.isMonoidHomomorphism
        ; *-homo                 = to-self-*
        }
      ; 1#-homo = Additive.to-self-embed 1r
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
