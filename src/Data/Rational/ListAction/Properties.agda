------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers: properties of sum and product
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.ListAction.Properties where

open import Data.List.Base using ([]; _∷_; _++_; map)
open import Data.List.Effectful.Foldable using (foldr-congruent)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭⇒↭ₛ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Rational.Base using (0ℚ; _+_; _*_)
open import Data.Rational.ListAction using (sum; product)
open import Data.Rational.Properties
  using (+-identityˡ; +-assoc; *-identityˡ; *-assoc
        ; *-zeroˡ; *-zeroʳ; *-distribˡ-+; *-distribʳ-+
        ; p*q≡0⇒p≡0∨q≡0
        ; +-0-commutativeMonoid; *-1-commutativeMonoid)
open import Data.Sum.Base using ([_,_]′)
open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; module ≡-Reasoning)

------------------------------------------------------------------------
-- Properties

-- sum

sum-++ : ∀ ps qs → sum (ps ++ qs) ≡ sum ps + sum qs
sum-++ [] qs = sym (+-identityˡ (sum qs))
sum-++ (p ∷ ps) qs = begin
  p + sum (ps ++ qs)    ≡⟨ cong (p +_) (sum-++ ps qs) ⟩
  p + (sum ps + sum qs) ≡⟨ +-assoc p (sum ps) (sum qs) ⟨
  (p + sum ps) + sum qs ∎
  where open ≡-Reasoning

*-distribˡ-sum : ∀ p qs → p * sum qs ≡ sum (map (p *_) qs)
*-distribˡ-sum p [] = *-zeroʳ p
*-distribˡ-sum p (q ∷ qs) = begin
  p * (q + sum qs)            ≡⟨ *-distribˡ-+ p q (sum qs) ⟩
  p * q + p * sum qs          ≡⟨ cong (p * q +_) (*-distribˡ-sum p qs) ⟩
  p * q + sum (map (p *_) qs) ∎
  where open ≡-Reasoning

*-distribʳ-sum : ∀ p qs → sum qs * p ≡ sum (map (_* p) qs)
*-distribʳ-sum p [] = *-zeroˡ p
*-distribʳ-sum p (q ∷ qs) = begin
  (q + sum qs) * p            ≡⟨ *-distribʳ-+ p q (sum qs) ⟩
  q * p + sum qs * p          ≡⟨ cong (q * p +_) (*-distribʳ-sum p qs) ⟩
  q * p + sum (map (_* p) qs) ∎
  where open ≡-Reasoning

sum-↭ : sum Preserves _↭_ ⟶ _≡_
sum-↭ p = foldr-congruent +-0-commutativeMonoid (↭⇒↭ₛ p)


-- product

product-++ : ∀ ps qs → product (ps ++ qs) ≡ product ps * product qs
product-++ [] qs = sym (*-identityˡ (product qs))
product-++ (p ∷ ps) qs = begin
  p * product (ps ++ qs)        ≡⟨ cong (p *_) (product-++ ps qs) ⟩
  p * (product ps * product qs) ≡⟨ *-assoc p (product ps) (product qs) ⟨
  (p * product ps) * product qs ∎
  where open ≡-Reasoning

product-locate : ∀ ps → product ps ≡ 0ℚ → 0ℚ ∈ ps
product-locate (p ∷ ps) = [ here ∘′ sym , there ∘′ product-locate ps ]′ ∘′ p*q≡0⇒p≡0∨q≡0

product-↭ : product Preserves _↭_ ⟶ _≡_
product-↭ p = foldr-congruent *-1-commutativeMonoid (↭⇒↭ₛ p)
