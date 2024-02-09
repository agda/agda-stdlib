------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers mod n, properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; NonZero; NonTrivial; _<_; _∸_)

module Data.Integer.Modulo.Properties (n : ℕ) .{{_ : NonTrivial n}} where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawNearSemiring; RawSemiring; RawRing)
open import Algebra.Bundles
  using (Magma; Monoid; NearSemiring; Semiring; Ring)
import Algebra.Definitions as Definitions
import Algebra.Structures as Structures
open import Data.Integer.Base as ℤ using (ℤ; _◂_; signAbs)
open import Data.Nat.BoundedORIG as ℕ< hiding (module Literals)
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base as Product using (_,_)
open import Data.Sign.Base as Sign using (Sign)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; isEquivalence; module ≡-Reasoning)

open import Data.Integer.Modulo n as Modulo using (ℤmod_; +-*-rawRing)
open Definitions (_≡_ {A = ℤmod_})
open Structures (_≡_ {A = ℤmod_})
  using ( IsMagma; IsSemigroup; IsMonoid
        ; IsGroup; IsAbelianGroup
        ; IsNearSemiring; IsSemiring
        ; IsRing)

private
  variable
    m o : ℕ
    i j k : ℤmod_

  instance
    _ = ℕ.nonTrivial⇒nonZero n

open RawRing +-*-rawRing
open ≡-Reasoning

+-cong₂ : Congruent₂ _+_
+-cong₂ = cong₂ _+_

+-isMagma : IsMagma _+_
+-isMagma = record { isEquivalence = isEquivalence ; ∙-cong = +-cong₂ }

+-assoc : Associative _+_
+-assoc x y z = begin
  x + y + z ≡⟨⟩
  fromℕ (((⟦ x ⟧ ℕ.+ ⟦ y ⟧) ℕ.% n) ℕ.+ ⟦ z ⟧) ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩
  fromℕ (⟦ x ⟧ ℕ.+ ((⟦ y ⟧ ℕ.+ ⟦ z ⟧) ℕ.% n)) ≡⟨⟩
  x + (y + z) ∎

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record { isMagma = +-isMagma ; assoc = +-assoc }

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ x = ⟦⟧≡⟦⟧⇒bounded≡ (ℕ.m<n⇒m%n≡m (ℕ<.isBounded x))

+-identityʳ : RightIdentity 0# _+_
+-identityʳ x = ⟦⟧≡⟦⟧⇒bounded≡ $
  trans (cong (ℕ._% n) (ℕ.+-identityʳ _)) (ℕ.m<n⇒m%n≡m (ℕ<.isBounded x))

+-identity : Identity 0# _+_
+-identity = +-identityˡ , +-identityʳ

+-isMonoid : IsMonoid _+_ 0#
+-isMonoid = record { isSemigroup = +-isSemigroup ; identity = +-identity }

+-inverseˡ : LeftInverse 0# -_ _+_
+-inverseˡ = {!!}

+-inverseʳ : RightInverse 0# -_ _+_
+-inverseʳ = {!!}

+-inverse : Inverse 0# -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

+-0-isGroup : IsGroup _+_ 0# -_
+-0-isGroup = record { isMonoid = +-isMonoid ; inverse = +-inverse ; ⁻¹-cong = cong -_ }

+-comm : Commutative _+_
+-comm x y = cong fromℕ (ℕ.+-comm ⟦ x ⟧ ⟦ y ⟧)

+-0-isAbelianGroup : IsAbelianGroup _+_ 0# -_
+-0-isAbelianGroup = record { isGroup = +-0-isGroup ; comm = +-comm }

*-cong₂ : Congruent₂ _*_
*-cong₂ = cong₂ _*_

*-assoc : Associative _*_
*-assoc x y z = begin
  x * y * z ≡⟨⟩
  fromℕ (((⟦ x ⟧ ℕ.* ⟦ y ⟧) ℕ.% n) ℕ.* ⟦ z ⟧) ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩
  fromℕ (⟦ x ⟧ ℕ.* ((⟦ y ⟧ ℕ.* ⟦ z ⟧) ℕ.% n)) ≡⟨⟩
  x * (y * z) ∎

*-identityˡ : LeftIdentity 1# _*_
*-identityˡ x = ⟦⟧≡⟦⟧⇒bounded≡ $
  {!!}

*-identityʳ : RightIdentity 1# _*_
*-identityʳ x with eq ← ⟦1⟧≡1 {n = n} = ⟦⟧≡⟦⟧⇒bounded≡ $
  {!trans (cong (ℕ._% n) (ℕ.*-identityʳ _)) (ℕ.m<n⇒m%n≡m (ℕ<.isBounded x))!}

*-identity : Identity 1# _*_
*-identity = *-identityˡ , *-identityʳ

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = {!!}

+-*-isRing : IsRing _+_ _*_ -_ 0# 1#
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = *-cong₂
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }
