------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the inner lexicographic product of two operators.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Bool.Base using (false; true)
open import Data.Product using (_×_; _,_; swap; map; uncurry′)
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Negation
  using (contradiction; contradiction₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

import Algebra.Construct.LexProduct.Base as Base

module Algebra.Construct.LexProduct.Inner
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (M : Magma ℓ₁ ℓ₂) (N : Magma ℓ₃ ℓ₄)
  (_≟₁_ : Decidable (Magma._≈_ M))
  where

open module M = Magma M
  renaming
  ( Carrier  to A
  ; _≈_      to _≈₁_
  ; _≉_      to _≉₁_
  )

open module N = Magma N
  using ()
  renaming
  ( Carrier to B
  ; _∙_     to _◦_
  ; _≈_     to _≈₂_
  ; ∙-cong  to ◦-cong
  )

private
  variable
    a b c d : A
    w x y z : B

------------------------------------------------------------------------
-- Base definition

open Base _∙_ _◦_ _≟₁_ public
  using (innerLex)

-- Save ourselves some typing in this file
private
  lex = innerLex

------------------------------------------------------------------------
-- Properties

module NaturalOrder where

  -- It would be really nice if we could use
  -- `Relation.Binary.Construct.NaturalOrder.Left/Right` to prove these
  -- properties but the equalities are defined the wrong way around

  open SetoidReasoning M.setoid

  ≤∙ˡ-resp-≈ : a ∙ b ≈₁ b → a ≈₁ c → b ≈₁ d → c ∙ d ≈₁ d
  ≤∙ˡ-resp-≈ {a} {b} {c} {d} ab≈b a≈c b≈d = begin
    c ∙ d ≈⟨ ∙-cong (M.sym a≈c) (M.sym b≈d) ⟩
    a ∙ b ≈⟨ ab≈b ⟩
    b     ≈⟨ b≈d ⟩
    d     ∎

  ≤∙ʳ-resp-≈ : a ∙ b ≈₁ a → a ≈₁ c → b ≈₁ d → c ∙ d ≈₁ c
  ≤∙ʳ-resp-≈ {a} {b} {c} {d} ab≈b a≈c b≈d = begin
    c ∙ d ≈⟨ ∙-cong (M.sym a≈c) (M.sym b≈d) ⟩
    a ∙ b ≈⟨ ab≈b ⟩
    a     ≈⟨ a≈c ⟩
    c     ∎

  ≤∙ˡ-trans : Associative _≈₁_ _∙_ → (a ∙ b) ≈₁ b → (b ∙ c) ≈₁ c → (a ∙ c) ≈₁ c
  ≤∙ˡ-trans {a} {b} {c} ∙-assoc ab≈b bc≈c = begin
    a ∙ c        ≈˘⟨ ∙-congˡ bc≈c ⟩
    a ∙ (b ∙ c)  ≈˘⟨ ∙-assoc a b c ⟩
    (a ∙ b) ∙ c  ≈⟨  ∙-congʳ ab≈b ⟩
    b ∙ c        ≈⟨  bc≈c ⟩
    c            ∎

  ≰∙ˡ-trans : Commutative _≈₁_ _∙_ → (a ∙ b) ≉₁ a → (a ∙ c) ≈₁ c → (b ∙ c) ≈₁ c → (a ∙ c) ≉₁ a
  ≰∙ˡ-trans {a} {b} {c} ∙-comm ab≉a ac≈c bc≈c ac≈a = ab≉a (begin
    a ∙ b  ≈⟨ ∙-congʳ (M.trans (M.sym ac≈a) ac≈c) ⟩
    c ∙ b  ≈⟨ ∙-comm c b ⟩
    b ∙ c  ≈⟨ bc≈c ⟩
    c      ≈⟨ M.trans (M.sym ac≈c) ac≈a ⟩
    a      ∎)

  <∙ˡ-trans : Associative _≈₁_ _∙_ → Commutative _≈₁_ _∙_ →
              (a ∙ b) ≈₁ b → (a ∙ b) ≉₁ a → (b ∙ c) ≈₁ c →
              (a ∙ c) ≉₁ a × (a ∙ c) ≈₁ c
  <∙ˡ-trans {a} {b} {c} ∙-assoc ∙-comm ab≈b ab≉a bc≈c = ac≉a , ac≈c
    where
    ac≈c = ≤∙ˡ-trans ∙-assoc ab≈b bc≈c
    ac≉a = ≰∙ˡ-trans ∙-comm ab≉a ac≈c bc≈c

  <∙ʳ-trans : Associative _≈₁_ _∙_ → Commutative _≈₁_ _∙_ →
              (a ∙ b) ≈₁ a → (b ∙ c) ≈₁ b → (b ∙ c) ≉₁ c →
              (a ∙ c) ≈₁ a × (a ∙ c) ≉₁ c
  <∙ʳ-trans {a} {b} {c} assoc comm ab≈a bc≈b bc≉c = map
    (M.trans (comm a c))
    (_∘ M.trans (comm c a))
    (swap (<∙ˡ-trans assoc comm
      (M.trans (comm c b) bc≈b)
      (bc≉c ∘ M.trans (comm b c))
      (M.trans (comm b a) ab≈a)))

------------------------------------------------------------------------
-- Basic properties

open SetoidReasoning N.setoid
open NaturalOrder

case₁ : a ∙ b ≈₁ a → a ∙ b ≉₁ b → lex a b x y ≈₂ x
case₁ {a} {b} ab≈a ab≉b with (a ∙ b) ≟₁ a | (a ∙ b) ≟₁ b
... | no  ab≉a | _        = contradiction ab≈a ab≉a
... | yes _    | yes ab≈b = contradiction ab≈b ab≉b
... | yes _    | no  _    = N.refl

case₂ : a ∙ b ≉₁ a → a ∙ b ≈₁ b → lex a b x y ≈₂ y
case₂ {a} {b} ab≉a ab≈b with (a ∙ b) ≟₁ a | (a ∙ b) ≟₁ b
... | yes ab≈a | _        = contradiction ab≈a ab≉a
... | no _     | no  ab≉b = contradiction ab≈b ab≉b
... | no _     | yes _    = N.refl

case₃ : a ∙ b ≈₁ a → a ∙ b ≈₁ b → lex a b x y ≈₂ (x ◦ y)
case₃ {a} {b} ab≈a ab≈b with (a ∙ b) ≟₁ a | (a ∙ b) ≟₁ b
... | no  ab≉a | _        = contradiction ab≈a ab≉a
... | yes _    | no  ab≉b = contradiction ab≈b ab≉b
... | yes _    | yes _    = N.refl

------------------------------------------------------------------------
-- Algebraic properties

cong : a ≈₁ b → c ≈₁ d → w ≈₂ x → y ≈₂ z → lex a c w y ≈₂ lex b d x z
cong {a} {b} {c} {d} a≈b c≈d w≈x y≈z
  with (a ∙ c) ≟₁ a | (a ∙ c) ≟₁ c | (b ∙ d) ≟₁ b | (b ∙ d) ≟₁ d
... | yes _    | yes _    | yes _    | yes _    = ◦-cong w≈x y≈z
... | yes _    | yes _    | no  _    | no  _    = ◦-cong w≈x y≈z
... | no  _    | no  _    | yes _    | yes _    = ◦-cong w≈x y≈z
... | no  _    | no  _    | no  _    | no  _    = ◦-cong w≈x y≈z
... | yes _    | no  _    | yes _    | no  _    = w≈x
... | no  _    | yes _    | no  _    | yes _    = y≈z
... | _        | yes ac≈c | _        | no bd≉d  = contradiction (≤∙ˡ-resp-≈ ac≈c a≈b c≈d) bd≉d
... | yes ac≈a | _        | no  bd≉b | _        = contradiction (≤∙ʳ-resp-≈ ac≈a a≈b c≈d) bd≉b
... | _        | no  ac≉c | _        | yes bd≈d = contradiction (≤∙ˡ-resp-≈ bd≈d (M.sym a≈b) (M.sym c≈d)) ac≉c
... | no  ac≉a | _        | yes bd≈b | _        = contradiction (≤∙ʳ-resp-≈ bd≈b (M.sym a≈b) (M.sym c≈d)) ac≉a

cong₁₂ : a ≈₁ b → c ≈₁ d → lex a c x y ≈₂ lex b d x y
cong₁₂ a≈b c≈d = cong a≈b c≈d N.refl N.refl

cong₁ : a ≈₁ b → lex a c x y ≈₂ lex b c x y
cong₁ a≈b = cong₁₂ a≈b M.refl

cong₂ : b ≈₁ c → lex a b x y ≈₂ lex a c x y
cong₂ = cong₁₂ M.refl

-- It is possible to relax this. Instead of ∙ being selective and ◦ being associative it's also
-- possible for _◦_ to return a single idempotent element.
assoc : Associative _≈₁_ _∙_ → Commutative _≈₁_ _∙_ →
        Selective _≈₁_ _∙_ → Associative _≈₂_ _◦_ →
        ∀ a b c x y z  → lex (a ∙ b) c (lex a b x y) z  ≈₂ lex a (b ∙ c) x (lex b c y z)
assoc ∙-assoc ∙-comm ∙-sel ◦-assoc a b c x y z
  with (a ∙ b) ≟₁ a | (a ∙ b) ≟₁ b | (b ∙ c) ≟₁ b | (b ∙ c) ≟₁ c
... | _        | _        | no  bc≉b | no  bc≉c = contradiction₂ (∙-sel b c) bc≉b bc≉c
... | no  ab≉a | no  ab≉b | _        | _        = contradiction₂ (∙-sel a b) ab≉a ab≉b
... | yes ab≈a | no  ab≉b | no  bc≉b | yes bc≈c = cong₁₂ ab≈a (M.sym bc≈c)
... | no ab≉a  | yes ab≈b | yes bc≈b | yes bc≈c = begin
  lex (a ∙ b) c y z        ≈⟨  cong₁ ab≈b ⟩
  lex b c y z              ≈⟨  case₃ bc≈b bc≈c ⟩
  y ◦ z                    ≈˘⟨ case₂ ab≉a ab≈b ⟩
  lex a b x (y ◦ z)        ≈˘⟨ cong₂ bc≈b ⟩
  lex a (b ∙ c) x (y ◦ z)  ∎
... | no ab≉a  | yes ab≈b | yes bc≈b | no bc≉c = begin
  lex (a ∙ b) c y z        ≈⟨  cong₁ ab≈b ⟩
  lex b c y z              ≈⟨  case₁ bc≈b bc≉c ⟩
  y                        ≈˘⟨ case₂ ab≉a ab≈b ⟩
  lex a b x y              ≈˘⟨ cong₂ bc≈b ⟩
  lex a (b ∙ c) x y        ∎
... | yes ab≈a | yes ab≈b | yes bc≈b | no bc≉c = begin
  lex (a ∙ b) c (x ◦ y) z  ≈⟨  cong₁ ab≈b ⟩
  lex b c (x ◦ y) z        ≈⟨  case₁ bc≈b bc≉c ⟩
  x ◦ y                    ≈˘⟨ case₃ ab≈a ab≈b ⟩
  lex a b x y              ≈˘⟨ cong₂ bc≈b ⟩
  lex a (b ∙ c) x y        ∎
... | yes ab≈a | yes ab≈b | yes bc≈b | yes bc≈c = begin
  lex (a ∙ b) c (x ◦ y) z  ≈⟨  cong₁ ab≈b ⟩
  lex b c (x ◦ y) z        ≈⟨  case₃ bc≈b bc≈c  ⟩
  (x ◦ y) ◦ z              ≈⟨  ◦-assoc x y z ⟩
  x ◦ (y ◦ z)              ≈˘⟨ case₃ ab≈a ab≈b ⟩
  lex a b x (y ◦ z)        ≈˘⟨ cong₂ bc≈b ⟩
  lex a (b ∙ c) x (y ◦ z)  ∎
... | yes ab≈a | yes ab≈b | no bc≉b | yes bc≈c = begin
  lex (a ∙ b) c (x ◦ y) z  ≈⟨  cong₁ ab≈b ⟩
  lex b c (x ◦ y) z        ≈⟨  case₂ bc≉b bc≈c ⟩
  z                        ≈˘⟨ case₂ bc≉b bc≈c ⟩
  lex b c x z              ≈˘⟨ cong₁₂ (M.trans (M.sym ab≈a) ab≈b) bc≈c ⟩
  lex a (b ∙ c) x z        ∎
... | yes ab≈a | no ab≉b | yes bc≈b | yes bc≈c = begin
  lex (a ∙ b) c x z        ≈⟨  cong₁₂ ab≈a (M.trans (M.sym bc≈c) bc≈b) ⟩
  lex a b x z              ≈⟨  case₁ ab≈a ab≉b ⟩
  x                        ≈˘⟨ case₁ ab≈a ab≉b ⟩
  lex a b x (y ◦ z)        ≈˘⟨ cong₂ bc≈b ⟩
  lex a (b ∙ c) x (y ◦ z)  ∎
... | no ab≉a | yes ab≈b | no bc≉b | yes bc≈c = begin
  lex (a ∙ b) c y z        ≈⟨  cong₁ ab≈b ⟩
  lex b c y z              ≈⟨  case₂ bc≉b bc≈c ⟩
  z                        ≈˘⟨ uncurry′ case₂ (<∙ˡ-trans ∙-assoc ∙-comm ab≈b ab≉a bc≈c) ⟩
  lex a c x z              ≈˘⟨ cong₂ bc≈c ⟩
  lex a (b ∙ c) x z        ∎
... | yes ab≈a | no ab≉b | yes bc≈b | no bc≉c = begin
  lex (a ∙ b) c x z        ≈⟨  cong₁ ab≈a ⟩
  lex a c x z              ≈⟨  uncurry′ case₁ (<∙ʳ-trans ∙-assoc ∙-comm ab≈a bc≈b bc≉c) ⟩
  x                        ≈˘⟨ case₁ ab≈a ab≉b ⟩
  lex a b x y              ≈˘⟨ cong₂ bc≈b ⟩
  lex a (b ∙ c) x y        ∎

comm : Commutative _≈₁_ _∙_ → Commutative _≈₂_ _◦_ →
       ∀ a b x y → lex a b x y ≈₂ lex b a y x
comm ∙-comm ◦-comm a b x y
  with (a ∙ b) ≟₁ a | (a ∙ b) ≟₁ b | (b ∙ a) ≟₁ b | (b ∙ a) ≟₁ a
... | yes ab≈a | _        | _        | no  ba≉a = contradiction (M.trans (∙-comm b a) ab≈a) ba≉a
... | no  ab≉a | _        | _        | yes ba≈a = contradiction (M.trans (∙-comm a b) ba≈a) ab≉a
... | _        | yes ab≈b | no  ba≉b | _        = contradiction (M.trans (∙-comm b a) ab≈b) ba≉b
... | _        | no  ab≉b | yes ba≈b | _        = contradiction (M.trans (∙-comm a b) ba≈b) ab≉b
... | yes _    | yes _    | yes _    | yes _    = ◦-comm x y
... | yes _    | no  _    | no  _    | yes _    = N.refl
... | no  _    | yes _    | yes _    | no  _    = N.refl
... | no  _    | no  _    | no  _    | no  _    = ◦-comm x y

idem : Idempotent _≈₂_ _◦_ → ∀ a b x → lex a b x x ≈₂ x
idem ◦-idem a b x with does ((a ∙ b) ≟₁ a) | does ((a ∙ b) ≟₁ b)
... | false | false = ◦-idem x
... | false | true  = N.refl
... | true  | false = N.refl
... | true  | true  = ◦-idem x

zeroʳ : ∀ {e f} → RightZero _≈₁_ e _∙_ → RightZero _≈₂_ f _◦_ →
        lex a e x f ≈₂ f
zeroʳ {a} {x} {e} {f} ze₁ ze₂ with (a ∙ e) ≟₁ a | (a ∙ e) ≟₁ e
... | _     | no  a∙e≉e = contradiction (ze₁ a) a∙e≉e
... | no  _ | yes _     = N.refl
... | yes _ | yes _     = ze₂ x

identityʳ : ∀ {e f} → RightIdentity _≈₁_ e _∙_ → RightIdentity _≈₂_ f _◦_ →
            lex a e x f ≈₂ x
identityʳ {a} {x} {e} {f} id₁ id₂ with (a ∙ e) ≟₁ a | (a ∙ e) ≟₁ e
... | no  a∙e≉a | _     = contradiction (id₁ a) a∙e≉a
... | yes _     | no  _ = N.refl
... | yes _     | yes _ = id₂ x
