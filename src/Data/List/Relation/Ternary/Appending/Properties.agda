------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the generalised view of appending two lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Ternary.Appending.Properties where

open import Data.List.Base using (List)
open import Data.List.Relation.Ternary.Appending
open import Data.List.Relation.Binary.Pointwise as Pw using (Pointwise; []; _∷_)
open import Level using (Level)
open import Relation.Binary using (REL; Rel; Trans)

private
  variable
    a b c l r : Level
    A : Set a
    B : Set b
    C : Set c
    L : REL A C l
    R : REL A B r
    as : List A
    bs : List B
    cs ds : List C

module _  {e} {E : Rel C e} {L′ : REL A C l} {R′ : REL B C r}
          (LEL′ : Trans L E L′) (RER′ : Trans R E R′)
          where

  transitive : Appending L R as bs cs → Pointwise E cs ds → Appending L′ R′ as bs ds
  transitive ([]++ rs) es       = []++ Pw.transitive RER′ rs es
  transitive (l ∷ lrs) (e ∷ es) = LEL′ l e ∷ transitive lrs es
