------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers mod n, properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; NonZero; NonTrivial; _<_; _∸_; _%_)

module Data.Integer.Modulo.Properties n .{{_ : NonTrivial n}} where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawNearSemiring; RawSemiring; RawRing)
open import Algebra.Bundles
  using (Magma; Monoid; NearSemiring; Semiring; Ring)
import Algebra.Definitions as Definitions
import Algebra.Structures as Structures
open import Data.Integer.Base as ℤ using (ℤ; _◂_; signAbs)
open import Data.Nat.Bounded.Base as ℕ< hiding (fromℕ; _∼_)
import Data.Nat.Bounded.Properties as ℕ<
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base as Product using (_,_)
open import Data.Sign.Base as Sign using (Sign)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; isEquivalence; module ≡-Reasoning)

open import Data.Integer.Modulo.Base n as Modulo
  using (ℤmod; fromℕ; fromℤ; _∼_; ≡-Mod; +-*-rawRing)

open Definitions (_≡_ {A = ℤmod})
open Structures (_≡_ {A = ℤmod})
  using ( IsMagma; IsSemigroup; IsMonoid
        ; IsGroup; IsAbelianGroup
        ; IsNearSemiring; IsSemiring
        ; IsRing)

private
  variable
    m o : ℕ
    i j k : ℤmod

  instance
    _ = ℕ.nonTrivial⇒nonZero n

open RawRing +-*-rawRing
open ≡-Reasoning

+-cong₂ : Congruent₂ _+_
+-cong₂ = cong₂ _+_

+-isMagma : IsMagma _+_
+-isMagma = record { isEquivalence = isEquivalence ; ∙-cong = +-cong₂ }

+-assoc : Associative _+_
+-assoc i j k = begin
  i + j + k
   ≡⟨⟩
  fromℕ (((⟦ i ⟧ ℕ.+ ⟦ j ⟧) % n) ℕ.+ ⟦ k ⟧)
   ≡⟨ ℕ<.≡-mod⇒fromℕ≡fromℕ ≡-mod ⟩
  fromℕ (⟦ i ⟧ ℕ.+ ((⟦ j ⟧ ℕ.+ ⟦ k ⟧) % n))
   ≡⟨⟩
  i + (j + k) ∎
  where
  ≡-mod : (((⟦ i ⟧ ℕ.+ ⟦ j ⟧) % n) ℕ.+ ⟦ k ⟧)
          ≡
          (⟦ i ⟧ ℕ.+ ((⟦ j ⟧ ℕ.+ ⟦ k ⟧) % n))
          modℕ n
  ≡-mod = ℕ<.≡-mod-trans (ℕ<.+-distribˡ-% (⟦ i ⟧ ℕ.+ ⟦ j ⟧) ⟦ k ⟧)
          (ℕ<.≡-mod-trans (ℕ<.≡-mod-reflexive (ℕ.+-assoc ⟦ i ⟧ ⟦ j ⟧ ⟦ k ⟧))
           (ℕ<.≡-mod-sym (ℕ<.+-distribʳ-% ⟦ i ⟧ (⟦ j ⟧ ℕ.+ ⟦ k ⟧))))

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record { isMagma = +-isMagma ; assoc = +-assoc }

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ = ℕ<.fromℕ∘toℕ≐id

+-identityʳ : RightIdentity 0# _+_
+-identityʳ i = trans (cong fromℕ (ℕ.+-identityʳ _)) (ℕ<.fromℕ∘toℕ≐id i)

+-identity : Identity 0# _+_
+-identity = +-identityˡ , +-identityʳ

+-isMonoid : IsMonoid _+_ 0#
+-isMonoid = record { isSemigroup = +-isSemigroup ; identity = +-identity }

+-inverseˡ : LeftInverse 0# -_ _+_
+-inverseˡ (⟦ zero ⟧<    _) = +-identityˡ 0#
+-inverseˡ i@(⟦ suc _ ⟧< _) = ℕ<.+-inverseˡ (ℕ<.isBounded i)

+-inverseʳ : RightInverse 0# -_ _+_
+-inverseʳ (⟦ zero ⟧<        _) = +-identityʳ 0#
+-inverseʳ i@(⟦ m@(suc _) ⟧< _) = ℕ<.+-inverseʳ (ℕ<.isBounded i)

+-inverse : Inverse 0# -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

+-0-isGroup : IsGroup _+_ 0# -_
+-0-isGroup = record { isMonoid = +-isMonoid ; inverse = +-inverse ; ⁻¹-cong = cong -_ }

+-comm : Commutative _+_
+-comm i j = cong fromℕ (ℕ.+-comm ⟦ i ⟧ ⟦ j ⟧)

+-0-isAbelianGroup : IsAbelianGroup _+_ 0# -_
+-0-isAbelianGroup = record { isGroup = +-0-isGroup ; comm = +-comm }

*-cong₂ : Congruent₂ _*_
*-cong₂ = cong₂ _*_

*-assoc : Associative _*_
*-assoc i j k = begin
  i * j * k
   ≡⟨⟩
  fromℕ (((⟦ i ⟧ ℕ.* ⟦ j ⟧) % n) ℕ.* ⟦ k ⟧)
   ≡⟨ ℕ<.≡-mod⇒fromℕ≡fromℕ ≡-mod ⟩
  fromℕ (⟦ i ⟧ ℕ.* ((⟦ j ⟧ ℕ.* ⟦ k ⟧) % n))
   ≡⟨⟩
  i * (j * k) ∎
  where
  ≡-mod : (((⟦ i ⟧ ℕ.* ⟦ j ⟧) % n) ℕ.* ⟦ k ⟧)
          ≡
          (⟦ i ⟧ ℕ.* ((⟦ j ⟧ ℕ.* ⟦ k ⟧) % n))
          modℕ n
  ≡-mod = ℕ<.≡-mod-trans (ℕ<.*-distribˡ-% (⟦ i ⟧ ℕ.* ⟦ j ⟧) ⟦ k ⟧)
          (ℕ<.≡-mod-trans (ℕ<.≡-mod-reflexive (ℕ.*-assoc ⟦ i ⟧ ⟦ j ⟧ ⟦ k ⟧))
           (ℕ<.≡-mod-sym (ℕ<.*-distribʳ-% ⟦ i ⟧ (⟦ j ⟧ ℕ.* ⟦ k ⟧))))

*-identityˡ : LeftIdentity 1# _*_
*-identityˡ i with eq ← ℕ<.⟦1⟧≡1 {n = n} rewrite eq
  = trans (cong fromℕ (ℕ.*-identityˡ _)) (ℕ<.fromℕ≐⟦⟧< (ℕ<.isBounded i))

*-identityʳ : RightIdentity 1# _*_
*-identityʳ i with eq ← ℕ<.⟦1⟧≡1 {n = n} rewrite eq
  = trans (cong fromℕ (ℕ.*-identityʳ _)) (ℕ<.fromℕ≐⟦⟧< (ℕ<.isBounded i))

*-identity : Identity 1# _*_
*-identity = *-identityˡ , *-identityʳ

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ i j k = ℕ<.≡-mod⇒fromℕ≡fromℕ ≡-mod
  where
  ≡-mod : (⟦ i ⟧ ℕ.* ⟦ j + k ⟧)
          ≡
          (⟦ i * j ⟧ ℕ.+ ⟦ i * k ⟧)
          modℕ n
  ≡-mod = ℕ<.≡-mod-trans (ℕ<.*-distribʳ-% ⟦ i ⟧ (⟦ j ⟧ ℕ.+ ⟦ k ⟧))
          (ℕ<.≡-mod-trans (ℕ<.≡-mod-reflexive (ℕ.*-distribˡ-+ ⟦ i ⟧ ⟦ j ⟧ ⟦ k ⟧))
           (ℕ<.≡-mod-sym (ℕ<.+-distrib-% (⟦ i ⟧ ℕ.* ⟦ j ⟧) (⟦ i ⟧ ℕ.* ⟦ k ⟧))))

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ i j k = ℕ<.≡-mod⇒fromℕ≡fromℕ ≡-mod
  where
  ≡-mod : (⟦ j + k ⟧ ℕ.* ⟦ i ⟧)
          ≡
          (⟦ j * i ⟧ ℕ.+ ⟦ k * i ⟧)
          modℕ n
  ≡-mod = ℕ<.≡-mod-trans (ℕ<.*-distribˡ-% (⟦ j ⟧ ℕ.+ ⟦ k ⟧) ⟦ i ⟧)
          (ℕ<.≡-mod-trans (ℕ<.≡-mod-reflexive (ℕ.*-distribʳ-+ ⟦ i ⟧ ⟦ j ⟧ ⟦ k ⟧))
           (ℕ<.≡-mod-sym (ℕ<.+-distrib-% (⟦ j ⟧ ℕ.* ⟦ i ⟧) (⟦ k ⟧ ℕ.* ⟦ i ⟧))))

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

+-*-isRing : IsRing _+_ _*_ -_ 0# 1#
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = *-cong₂
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }

ring : Ring _ _
ring = record { isRing = +-*-isRing }
