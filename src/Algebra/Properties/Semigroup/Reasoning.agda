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
  using (Carrier; _∙_; _≈_; setoid; trans; refl; sym; assoc; ∙-cong; isMagma
  ; ∙-congˡ; ∙-congʳ)
open import Relation.Binary.Reasoning.Setoid setoid

private
 variable
    u v w x y z : Carrier

module Assoc4  {u v w x : Carrier} where
  [uv∙w]x≈u[vw∙x] : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ ((v ∙ w) ∙ x)
  [uv∙w]x≈u[vw∙x] = trans (∙-congʳ (assoc u v w)) (assoc u (v ∙ w) x)

  [uv∙w]x≈u[v∙wx] : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [uv∙w]x≈u[v∙wx] = trans (assoc (u ∙ v) w x) (assoc u v (w ∙ x))

  [u∙vw]x≈uv∙wx : (u ∙ (v ∙ w)) ∙ x ≈ (u ∙ v) ∙ (w ∙ x)
  [u∙vw]x≈uv∙wx = trans (sym (∙-congʳ (assoc u v w))) (assoc (u ∙ v) w x)

  [u∙vw]x≈u[v∙wx] : (u ∙ (v ∙ w)) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [u∙vw]x≈u[v∙wx] = trans (assoc u (v ∙ w) x) (∙-congˡ (assoc v w x))

  uv∙wx≈[u∙vw]x : (u ∙ v) ∙ (w ∙ x) ≈ (u ∙ (v ∙ w)) ∙ x
  uv∙wx≈[u∙vw]x = trans (sym (assoc (u ∙ v) w x)) (∙-congʳ (assoc u v w))

  uv∙wx≈u[vw∙x] : (u ∙ v) ∙ (w ∙ x) ≈ u ∙ ((v ∙ w) ∙ x)
  uv∙wx≈u[vw∙x] = trans (assoc u v (w ∙ x)) (∙-congˡ (sym (assoc v w x)))

  u[vw∙x]≈[uv∙w]x : u ∙ ((v ∙ w) ∙ x) ≈ ((u ∙ v) ∙ w) ∙ x
  u[vw∙x]≈[uv∙w]x = sym (trans (∙-congʳ (assoc u v w)) (assoc u (v ∙ w) x))

  u[vw∙x]≈uv∙wx : u ∙ ((v ∙ w) ∙ x) ≈ (u ∙ v) ∙ (w ∙ x)
  u[vw∙x]≈uv∙wx = trans (∙-congˡ (assoc v w x)) (sym (assoc u v (w ∙ x)))

  u[v∙wx]≈[uv∙w]x : u ∙ (v ∙ (w ∙ x)) ≈ ((u ∙ v) ∙ w) ∙ x
  u[v∙wx]≈[uv∙w]x = sym (trans (assoc (u ∙ v) w x) (assoc u v (w ∙ x)))

  u[v∙wx]≈[u∙vw]x : u ∙ (v ∙ (w ∙ x)) ≈ (u ∙ (v ∙ w)) ∙ x
  u[v∙wx]≈[u∙vw]x  = sym (trans (assoc u (v ∙ w) x) (∙-congˡ (assoc v w x)))

open Assoc4 public

module Pulls (uv≡w : u ∙ v ≈ w) where
    uv≡w⇒xu∙v≈xw : ∀ {x} → (x ∙ u) ∙ v ≈ x ∙ w
    uv≡w⇒xu∙v≈xw {x = x} =  trans (assoc x u v) (∙-congˡ uv≡w)

    uv≡w⇒u∙vx≈wx : ∀ {x} → u ∙ (v ∙ x) ≈ w ∙ x
    uv≡w⇒u∙vx≈wx {x = x} = trans (sym (assoc u v x)) (∙-congʳ uv≡w)

    uv≡w⇒u[vx∙y]≈w∙xy : ∀ {x y} → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ (x ∙ y)
    uv≡w⇒u[vx∙y]≈w∙xy {x = x} {y = y} = trans (∙-congˡ (assoc v x y)) uv≡w⇒u∙vx≈wx

    uv≡w⇒x[uv∙y]≈x∙wy : ∀ {x y} → x ∙ (u ∙ (v ∙ y)) ≈ x ∙ (w ∙ y)
    uv≡w⇒x[uv∙y]≈x∙wy {x = x} {y = y} = ∙-congˡ (uv≡w⇒u∙vx≈wx)

    uv≡w⇒[x∙yu]v≈x∙yw : ∀ {x y} → (x ∙ (y ∙ u)) ∙ v ≈ x ∙ (y ∙ w)
    uv≡w⇒[x∙yu]v≈x∙yw  {x = x} {y = y} = trans (assoc x (y ∙ u) v) (∙-congˡ (uv≡w⇒xu∙v≈xw {x = y}))

open Pulls public

module Pushes (uv≡w : u ∙ v ≈ w) where
    uv≡w⇒xw≈xu∙v : x ∙ w ≈ (x ∙ u) ∙ v
    uv≡w⇒xw≈xu∙v = sym (uv≡w⇒xu∙v≈xw uv≡w)

    uv≡w⇒wx≈u∙vx : w ∙ x ≈ u ∙ (v ∙ x)
    uv≡w⇒wx≈u∙vx = sym (uv≡w⇒u∙vx≈wx uv≡w)

open Pushes public

module Center (eq : u ∙ v ≈ w) where
  uv≡w⇒xu∙vy≈x∙wy : (x ∙ u) ∙ (v ∙ y) ≈ x ∙ (w ∙ y)
  uv≡w⇒xu∙vy≈x∙wy = uv≡w⇒xu∙v≈xw(uv≡w⇒u∙vx≈wx eq)

  uv≡w⇒xy≡z⇒u[vx∙y]≈wz : ∀ z → x ∙ y ≈ z → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ z
  uv≡w⇒xy≡z⇒u[vx∙y]≈wz z xy≈z = trans (∙-congˡ (uv≡w⇒xu∙v≈xw xy≈z)) (uv≡w⇒u∙vx≈wx eq)

  uv≡w⇒x∙wy≈x∙[u∙vy] : x ∙ (w ∙ y) ≈ x ∙ (u ∙ (v ∙ y))
  uv≡w⇒x∙wy≈x∙[u∙vy] = sym (uv≡w⇒x[uv∙y]≈x∙wy eq)

open Center public

module Extends {u v w x : Carrier} (s : u ∙ v ≈ w ∙ x) where
  uv≈wx⇒yu∙v≈yw∙x : (y ∙ u) ∙ v ≈ (y ∙ w) ∙ x
  uv≈wx⇒yu∙v≈yw∙x  {y = y} = trans (uv≡w⇒xu∙v≈xw s) (sym (assoc y w x))

  uv≈wx⇒u∙vy≈w∙xy : ∀ y → u ∙ (v ∙ y) ≈ w ∙ (x ∙ y)
  uv≈wx⇒u∙vy≈w∙xy y = trans (uv≡w⇒u∙vx≈wx s) (assoc w x y)

  uv≈wx⇒yu∙vz≈yw∙xz : ∀ y z → (y ∙ u) ∙ (v ∙ z) ≈ (y ∙ w) ∙ (x ∙ z)
  uv≈wx⇒yu∙vz≈yw∙xz y z = trans (uv≡w⇒xu∙v≈xw (uv≈wx⇒u∙vy≈w∙xy z))(sym (assoc y w (x ∙ z)))

open Extends public

