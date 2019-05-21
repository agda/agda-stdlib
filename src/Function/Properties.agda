------------------------------------------------------------------------
-- The Agda standard library
--
-- Some generic function properties.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties where

open import Data.Product    using (∃)
open import Relation.Binary using (Rel)
open import Relation.Unary  using (Pred)


--****************************************************************************
module _ {α β} {A : Set α} {B : Set β}
  where
  Injective :  ∀ {α= β=} → Rel A α= → Rel B β= → Pred (A → B) _
  Injective _~_ _~'_ f =
                       {x y : A} → f x ~' f y → x ~ y

  Surjective :  ∀ {β=} → Rel B β= → Pred (A → B) _
  Surjective _~_ f =
                   (y : B) → ∃ (\x → f x ~ y)
