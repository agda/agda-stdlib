------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of the lexicographic product of two operators.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Magma)
open import Algebra.Definitions
open import Data.Bool.Base using (true; false)
open import Data.Product.Base as Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×_)
open import Data.Sum.Base using (inj₁; inj₂; map)
open import Function.Base using (_∘_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable.Core using (does; yes; no)
open import Relation.Nullary.Negation.Core using (¬_; contradiction; contradiction₂)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

module Algebra.Construct.LexProduct
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (M : Magma ℓ₁ ℓ₂) (N : Magma ℓ₃ ℓ₄)
  (_≟₁_ : Decidable (Magma._≈_ M))
  where

open Magma M using (_∙_ ; ∙-cong)
  renaming
  ( Carrier  to A
  ; _≈_      to _≈₁_
  ; _≉_      to _≉₁_
  )

open Magma N using ()
  renaming
  ( Carrier to B
  ; _∙_     to _◦_
  ; _≈_     to _≈₂_
  ; refl    to ≈₂-refl
  )

import Algebra.Construct.LexProduct.Inner M N _≟₁_ as InnerLex

private
  infix 4 _≋_
  _≋_ : Rel (A Product.× B) _
  _≋_ = _≈₁_ × _≈₂_

  variable
    a b : A

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

open import Algebra.Construct.LexProduct.Base _∙_ _◦_ _≟₁_ public
  renaming (lex to _⊕_)

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------
-- Basic cases

case₁ : ∀ {a b} → (a ∙ b) ≈₁ a → (a ∙ b) ≉₁ b →
        ∀ x y → (a , x) ⊕ (b , y) ≋ (a , x)
case₁ ab≈a ab≉b _ _ = ab≈a , InnerLex.case₁ ab≈a ab≉b

case₂ : ∀ {a b} → (a ∙ b) ≉₁ a → (a ∙ b) ≈₁ b →
        ∀ x y → (a , x) ⊕ (b , y) ≋ (b , y)
case₂ ab≉a ab≈b _ _ = ab≈b , InnerLex.case₂ ab≉a ab≈b

case₃ : ∀ {a b} → (a ∙ b) ≈₁ a → (a ∙ b) ≈₁ b →
        ∀ x y → (a , x) ⊕ (b , y) ≋ (a , x ◦ y)
case₃ ab≈a ab≈b _ _ = ab≈a , InnerLex.case₃ ab≈a ab≈b

------------------------------------------------------------------------
-- Algebraic properties

cong : Congruent₂ _≋_ _⊕_
cong (a≈b , w≈x) (c≈d , y≈z) =
  ∙-cong a≈b c≈d ,
  InnerLex.cong a≈b c≈d w≈x y≈z

assoc : Associative _≈₁_ _∙_ → Commutative _≈₁_ _∙_ →
        Selective _≈₁_ _∙_ → Associative _≈₂_ _◦_ →
        Associative _≋_ _⊕_
assoc ∙-assoc ∙-comm ∙-sel ◦-assoc (a , x) (b , y) (c , z) =
  ∙-assoc a b c ,
  InnerLex.assoc ∙-assoc ∙-comm ∙-sel ◦-assoc a b c x y z

comm : Commutative _≈₁_ _∙_ → Commutative _≈₂_ _◦_ →
       Commutative _≋_ _⊕_
comm ∙-comm ◦-comm (a , x) (b , y) =
  ∙-comm a b ,
  InnerLex.comm ∙-comm ◦-comm a b x y

zeroʳ : ∀ {e f} → RightZero _≈₁_ e _∙_ → RightZero _≈₂_ f _◦_ →
        RightZero _≋_ (e , f) _⊕_
zeroʳ ze₁ ze₂ (x , a) = ze₁ x , InnerLex.zeroʳ ze₁ ze₂

identityʳ : ∀ {e f} → RightIdentity _≈₁_ e _∙_ → RightIdentity _≈₂_ f _◦_ →
            RightIdentity _≋_ (e , f) _⊕_
identityʳ id₁ id₂ (x , a) = id₁ x , InnerLex.identityʳ id₁ id₂

sel : Selective _≈₁_ _∙_ → Selective _≈₂_ _◦_ → Selective _≋_ _⊕_
sel ∙-sel ◦-sel (a , x) (b , y) with (a ∙ b) ≟₁ a | (a ∙ b) ≟₁ b
... | no  ab≉a | no  ab≉b  = contradiction₂ (∙-sel a b) ab≉a ab≉b
... | yes ab≈a | no  _     = inj₁ (ab≈a , ≈₂-refl)
... | no  _    | yes ab≈b  = inj₂ (ab≈b , ≈₂-refl)
... | yes ab≈a | yes ab≈b  = map (ab≈a ,_) (ab≈b ,_) (◦-sel x y)
