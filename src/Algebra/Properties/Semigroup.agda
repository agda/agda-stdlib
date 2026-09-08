------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)

module Algebra.Properties.Semigroup {a ℓ} (S : Semigroup a ℓ) where

open import Data.Product.Base using (_,_)

open Semigroup S
  using (Carrier; _∙_; _≈_; setoid; trans ; refl; sym; assoc; ∙-cong; ∙-congˡ; ∙-congʳ)
open import Algebra.Definitions _≈_
  using (Alternative; LeftAlternative; RightAlternative; Flexible)

private
  variable
    u v w x y z : Carrier

x∙yz≈xy∙z : ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z
x∙yz≈xy∙z x y z = sym (assoc x y z)

alternativeˡ : LeftAlternative _∙_
alternativeˡ x y = assoc x x y

alternativeʳ : RightAlternative _∙_
alternativeʳ x y = sym (assoc x y y)

alternative : Alternative _∙_
alternative = alternativeˡ , alternativeʳ

flexible : Flexible _∙_
flexible x y = assoc x y x

module _ (uv≈w : u ∙ v ≈ w) where
  uv≈w⇒xu∙v≈xw : ∀ x → (x ∙ u) ∙ v ≈ x ∙ w
  uv≈w⇒xu∙v≈xw x = trans (assoc x u v) (∙-congˡ uv≈w)

  uv≈w⇒u∙vx≈wx : ∀ x → u ∙ (v ∙ x) ≈ w ∙ x
  uv≈w⇒u∙vx≈wx x = trans (sym (assoc u v x)) (∙-congʳ uv≈w)

  uv≈w⇒u[vx∙y]≈w∙xy : ∀ x y → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ (x ∙ y)
  uv≈w⇒u[vx∙y]≈w∙xy x y = trans (∙-congˡ (assoc v x y)) (uv≈w⇒u∙vx≈wx (x ∙ y))

  uv≈w⇒x[uv∙y]≈x∙wy : ∀ x y → x ∙ (u ∙ (v ∙ y)) ≈ x ∙ (w ∙ y)
  uv≈w⇒x[uv∙y]≈x∙wy x y = ∙-congˡ (uv≈w⇒u∙vx≈wx y)

  uv≈w⇒[x∙yu]v≈x∙yw : ∀ x y → (x ∙ (y ∙ u)) ∙ v ≈ x ∙ (y ∙ w)
  uv≈w⇒[x∙yu]v≈x∙yw x y = trans (assoc x (y ∙ u) v) (∙-congˡ (uv≈w⇒xu∙v≈xw y))

  uv≈w⇒[xu∙v]y≈x∙wy : ∀ x y → ((x ∙ u) ∙ v) ∙ y ≈ x ∙ (w ∙ y)
  uv≈w⇒[xu∙v]y≈x∙wy x y = trans (∙-congʳ (uv≈w⇒xu∙v≈xw x)) (assoc x w y)

  uv≈w⇒[xy∙u]v≈x∙yw : ∀ x y → ((x ∙ y) ∙ u) ∙ v ≈ x ∙ (y ∙ w)
  uv≈w⇒[xy∙u]v≈x∙yw x y = trans (∙-congʳ (assoc x y u)) (uv≈w⇒[x∙yu]v≈x∙yw x y )

module _ (uv≈w : u ∙ v ≈ w) where

  uv≈w⇒xu∙vy≈x∙wy : ∀ x y → (x ∙ u) ∙ (v ∙ y) ≈ x ∙ (w ∙ y)
  uv≈w⇒xu∙vy≈x∙wy x y = uv≈w⇒xu∙v≈xw (uv≈w⇒u∙vx≈wx uv≈w y) x

  uv≈w⇒xy≈z⇒u[vx∙y]≈wz : ∀ x y → x ∙ y ≈ z → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ z
  uv≈w⇒xy≈z⇒u[vx∙y]≈wz x y xy≈z = trans (∙-congˡ (uv≈w⇒xu∙v≈xw xy≈z v)) (uv≈w⇒u∙vx≈wx uv≈w _)

  uv≈w⇒x∙wy≈x∙[u∙vy] : x ∙ (w ∙ y) ≈ x ∙ (u ∙ (v ∙ y))
  uv≈w⇒x∙wy≈x∙[u∙vy] = sym (uv≈w⇒x[uv∙y]≈x∙wy uv≈w _ _)

module _ u v w x where
  [uv∙w]x≈u[vw∙x] : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ ((v ∙ w) ∙ x)
  [uv∙w]x≈u[vw∙x] = uv≈w⇒[xu∙v]y≈x∙wy refl u x

  [uv∙w]x≈u[v∙wx] : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [uv∙w]x≈u[v∙wx] = uv≈w⇒[xy∙u]v≈x∙yw refl u v

  [u∙vw]x≈uv∙wx : (u ∙ (v ∙ w)) ∙ x ≈ (u ∙ v) ∙ (w ∙ x)
  [u∙vw]x≈uv∙wx = trans (sym (∙-congʳ (assoc u v w))) (assoc (u ∙ v) w x)

  [u∙vw]x≈u[v∙wx] : (u ∙ (v ∙ w)) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [u∙vw]x≈u[v∙wx] = uv≈w⇒[x∙yu]v≈x∙yw refl u v

  uv∙wx≈u[vw∙x] : (u ∙ v) ∙ (w ∙ x) ≈ u ∙ ((v ∙ w) ∙ x)
  uv∙wx≈u[vw∙x] = uv≈w⇒xu∙vy≈x∙wy refl u x

module _ (uv≈wx : u ∙ v ≈ w ∙ x) where
  uv≈wx⇒yu∙v≈yw∙x : ∀ y → (y ∙ u) ∙ v ≈ (y ∙ w) ∙ x
  uv≈wx⇒yu∙v≈yw∙x y = trans (uv≈w⇒xu∙v≈xw uv≈wx y) (sym (assoc y w x))

  uv≈wx⇒u∙vy≈w∙xy : ∀ y → u ∙ (v ∙ y) ≈ w ∙ (x ∙ y)
  uv≈wx⇒u∙vy≈w∙xy y = trans (uv≈w⇒u∙vx≈wx uv≈wx y) (assoc w x y)

  uv≈wx⇒yu∙vz≈yw∙xz : ∀ y z → (y ∙ u) ∙ (v ∙ z) ≈ (y ∙ w) ∙ (x ∙ z)
  uv≈wx⇒yu∙vz≈yw∙xz y z = trans (uv≈w⇒xu∙v≈xw (uv≈wx⇒u∙vy≈w∙xy z) y) (sym (assoc y w (x ∙ z)))
