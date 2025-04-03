------------------------------------------------------------------------
-- The Agda standard library
--
-- Equational reasoning for semigroups
-- (Utilities for associativity reasoning, pulling and pushing operations)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semigroup)

module Algebra.Properties.Semigroup.Reasoning {o ℓ} (S : Semigroup o ℓ) where

open import Algebra.Structures using (IsMagma)

open Semigroup S
    using (Carrier; _∙_; _≈_; setoid; trans; refl; sym; assoc; ∙-cong; isMagma)
open import Relation.Binary.Reasoning.Setoid setoid
open IsMagma isMagma using (∙-congˡ; ∙-congʳ)

private
 variable
    u v w x y z : Carrier

module Assoc4  {u v w x : Carrier} where
  [[u∙v]∙w]∙x≈u∙[[v∙w]∙x] : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ ((v ∙ w) ∙ x)
  [[u∙v]∙w]∙x≈u∙[[v∙w]∙x] = trans (∙-congʳ (assoc u v w)) (assoc u (v ∙ w) x)

  [[u∙v]∙w]∙x≈u∙[v∙[w∙x]] : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [[u∙v]∙w]∙x≈u∙[v∙[w∙x]] = trans (assoc (u ∙ v) w x) (assoc u v (w ∙ x))

  [u∙[v∙w]]∙x≈[u∙v]∙[w∙x] : (u ∙ (v ∙ w)) ∙ x ≈ (u ∙ v) ∙ (w ∙ x)
  [u∙[v∙w]]∙x≈[u∙v]∙[w∙x] = trans (sym (∙-congʳ (assoc u v w))) (assoc (u ∙ v) w x)

  [u∙[v∙w]]∙x≈u∙[v∙[w∙x]] : (u ∙ (v ∙ w)) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [u∙[v∙w]]∙x≈u∙[v∙[w∙x]] = trans (assoc u (v ∙ w) x) (∙-congˡ (assoc v w x))

  [u∙v]∙[w∙x]≈[u∙[v∙w]]∙x : (u ∙ v) ∙ (w ∙ x) ≈ (u ∙ (v ∙ w)) ∙ x
  [u∙v]∙[w∙x]≈[u∙[v∙w]]∙x = trans (sym (assoc (u ∙ v) w x)) (∙-congʳ (assoc u v w))

  [u∙v]∙[w∙x]≈u∙[[v∙w]]∙x] : (u ∙ v) ∙ (w ∙ x) ≈ u ∙ ((v ∙ w) ∙ x)
  [u∙v]∙[w∙x]≈u∙[[v∙w]]∙x] = begin
    (u ∙ v) ∙ (w ∙ x) ≈⟨ assoc u v (w ∙ x) ⟩
    u ∙ (v ∙ (w ∙ x)) ≈⟨ ∙-congˡ (sym (assoc v w x)) ⟩
    u ∙ ((v ∙ w) ∙ x) ∎

  u∙[[v∙w]∙x]≈[[u∙v]∙w]∙x : u ∙ ((v ∙ w) ∙ x) ≈ ((u ∙ v) ∙ w) ∙ x
  u∙[[v∙w]∙x]≈[[u∙v]∙w]∙x = sym (trans (∙-congʳ (assoc u v w)) (assoc u (v ∙ w) x))

  u∙[v∙w]]∙x]≈[u∙v]∙[w∙x] : u ∙ ((v ∙ w) ∙ x) ≈ (u ∙ v) ∙ (w ∙ x)
  u∙[v∙w]]∙x]≈[u∙v]∙[w∙x] = begin
    u ∙ ((v ∙ w) ∙ x) ≈⟨ ∙-congˡ (assoc v w x) ⟩
    u ∙ (v ∙ (w ∙ x)) ≈⟨ assoc u v (w ∙ x) ⟨
    (u ∙ v) ∙ (w ∙ x) ∎

  u∙[v∙[w∙x]]≈[[u∙v]∙w]∙x : u ∙ (v ∙ (w ∙ x)) ≈ ((u ∙ v) ∙ w) ∙ x
  u∙[v∙[w∙x]]≈[[u∙v]∙w]∙x = sym (trans (assoc (u ∙ v) w x) (assoc u v (w ∙ x)))

  u∙[v∙[w∙x]]≈[u∙[v∙w]]∙x : u ∙ (v ∙ (w ∙ x)) ≈ (u ∙ (v ∙ w)) ∙ x
  u∙[v∙[w∙x]]≈[u∙[v∙w]]∙x = sym (trans (assoc u (v ∙ w) x) (∙-congˡ (assoc v w x)))

open Assoc4 public

module Pulls (uv≡w : u ∙ v ≈ w) where
    pullʳ : ∀ {x} → (x ∙ u) ∙ v ≈ x ∙ w
    pullʳ {x = x} = begin
        (x ∙ u) ∙ v ≈⟨ assoc x u v ⟩
        x ∙ (u ∙ v) ≈⟨ ∙-congˡ uv≡w ⟩
        x ∙ w       ∎

    pullˡ : ∀ {x} → u ∙ (v ∙ x) ≈ w ∙ x
    pullˡ {x = x} = begin
        u ∙ (v ∙ x) ≈⟨ assoc u v x ⟨
        (u ∙ v) ∙ x ≈⟨ ∙-congʳ uv≡w ⟩
        w ∙ x       ∎

    pull-first : ∀ {x y} → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ (x ∙ y)
    pull-first {x = x} {y = y} = begin
      u ∙ ((v ∙ x) ∙ y) ≈⟨ ∙-congˡ (assoc v x y) ⟩
      u ∙ (v ∙ (x ∙ y)) ≈⟨ pullˡ ⟩
      w ∙ (x ∙ y)       ∎

    pull-center : ∀ {x y} → x ∙ (u ∙ (v ∙ y)) ≈ x ∙ (w ∙ y)
    pull-center {x = x} {y = y} = ∙-congˡ (pullˡ)

    -- could be called pull₃ʳ
    pull-last : ∀ {x y} → (x ∙ (y ∙ u)) ∙ v ≈ x ∙ (y ∙ w)
    pull-last {x = x} {y = y} = begin
      (x ∙ (y ∙ u)) ∙ v ≈⟨ assoc x (y ∙ u) v ⟩
      x ∙ ((y ∙ u) ∙ v) ≈⟨ ∙-congˡ (pullʳ {x = y}) ⟩
      x ∙ (y ∙ w)       ∎

open Pulls public

module Pushes (uv≡w : u ∙ v ≈ w) where
    pushʳ : x ∙ w ≈ (x ∙ u) ∙ v
    pushʳ = sym (pullʳ uv≡w)

    pushˡ : w ∙ x ≈ u ∙ (v ∙ x)
    pushˡ = sym (pullˡ uv≡w)

open Pushes public

module Center (eq : u ∙ v ≈ w) where
  center : (x ∙ u) ∙ (v ∙ y) ≈ x ∙ (w ∙ y)
  center = pullʳ (pullˡ eq)

  center⁻¹ : x ∙ y ≈ z →  u ∙ ((v ∙ x) ∙ y) ≈ w ∙ z
  center⁻¹ {x = x} {y = y} {z = z} xy≈z = begin
    u ∙ ((v ∙ x) ∙ y) ≈⟨ ∙-congˡ (pullʳ xy≈z) ⟩
    u ∙ (v ∙ z)       ≈⟨ pullˡ eq ⟩
    w ∙ z             ∎

  push-center : x ∙ (w ∙ y) ≈ x ∙ (u ∙ (v ∙ y))
  push-center = sym (pull-center eq)

open Center public

module Extends {u v w x : Carrier} (s : u ∙ v ≈ w ∙ x) where
  extendˡ : (y ∙ u) ∙ v ≈ (y ∙ w) ∙ x
  extendˡ {y = y} = begin
    (y ∙ u) ∙ v ≈⟨ pullʳ s ⟩
    y ∙ (w ∙ x) ≈⟨ assoc y w x ⟨
    (y ∙ w) ∙ x ∎

  extendʳ : u ∙ (v ∙ y) ≈ w ∙ (x ∙ y)
  extendʳ {y = y} = begin
    u ∙ (v ∙ y) ≈⟨ pullˡ s ⟩
    (w ∙ x) ∙ y ≈⟨ assoc w x y ⟩
    w ∙ (x ∙ y) ∎

  extend² : ∀ y z → (y ∙ u) ∙ (v ∙ z) ≈ (y ∙ w) ∙ (x ∙ z)
  extend² y z = begin
    (y ∙ u) ∙ (v ∙ z) ≈⟨ pullʳ (extendʳ {y = z}) ⟩
    y ∙ (w ∙ (x ∙ z)) ≈⟨ assoc y w (x ∙ z) ⟨
    (y ∙ w) ∙ (x ∙ z) ∎

open Extends public

 