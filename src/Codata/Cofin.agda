------------------------------------------------------------------------
-- The Agda standard library
--
-- "Finite" sets indexed on coinductive "natural" numbers
------------------------------------------------------------------------

module Codata.Cofin where

open import Size
open import Codata.Thunk
open import Codata.Conat as Conat hiding (fromℕ; fromMusical; toMusical)
open import Codata.Conat.Bisimilarity as Bisim using (_⊢_≲_ ; s≲s)
open import Data.Nat
open import Data.Fin as Fin hiding (fromℕ; fromℕ≤; toℕ)
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The type

-- Note that `Cofin infnity` is /not/ finite. Note also that this is not a
-- coinductive type, but it is indexed on a coinductive type.

data Cofin : Conat ∞ → Set where
  zero : ∀ {n} → Cofin (suc n)
  suc  : ∀ {n} → Cofin (n .force) → Cofin (suc n)

suc-injective : ∀ {n} {p q : Cofin (n .force)} →
                (Cofin (suc n) ∋ suc p) ≡ suc q → p ≡ q
suc-injective refl = refl

------------------------------------------------------------------------
-- Some operations

fromℕ< : ∀ {n k} → k ℕ< n → Cofin n
fromℕ< {zero}  ()
fromℕ< {suc n} {zero}  (sℕ≤s p) = zero
fromℕ< {suc n} {suc k} (sℕ≤s p) = suc (fromℕ< p)

fromℕ : ℕ → Cofin infinity
fromℕ k = fromℕ< (suc k ℕ≤infinity)

toℕ : ∀ {n} → Cofin n → ℕ
toℕ zero    = zero
toℕ (suc i) = suc (toℕ i)

fromFin : ∀ {n} → Fin n → Cofin (Conat.fromℕ n)
fromFin zero    = zero
fromFin (suc i) = suc (fromFin i)

toFin : ∀ n → Cofin (Conat.fromℕ n) → Fin n
toFin zero    ()
toFin (suc n) zero    = zero
toFin (suc n) (suc i) = suc (toFin n i)

open import Codata.Musical.Notation using (♭; ♯_)
import Codata.Musical.Cofin as M

fromMusical : ∀ {n} → M.Cofin n → Cofin (Conat.fromMusical n)
fromMusical M.zero    = zero
fromMusical (M.suc n) = suc (fromMusical n)

toMusical : ∀ {n} → Cofin n → M.Cofin (Conat.toMusical n)
toMusical zero    = M.zero
toMusical (suc n) = M.suc (toMusical n)
