------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection utilities
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.TCM.Utilities where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Unit using (⊤; tt)
open import Effect.Applicative using (RawApplicative; mkRawApplicative)
open import Function using (case_of_)
open import Reflection.AST.Meta using (Meta)
open import Reflection.AST.Term using (Term)
open import Reflection.TCM using (TC; pure; blockTC; blockerAll; blockerMeta)

import Reflection.AST.Traversal as Traversal

blockOnMetas : Term → TC ⊤
blockOnMetas t =
  case traverseTerm actions (0 , []) t of λ where
    []         → pure tt
    xs@(_ ∷ _) → blockTC (blockerAll (map blockerMeta xs))
  where
  applicative : ∀ {ℓ} → RawApplicative {ℓ} (λ _ → List Meta)
  applicative = mkRawApplicative (λ _ → List Meta) (λ _ → []) _++_

  open Traversal applicative

  actions : Actions
  actions = record defaultActions { onMeta = λ _ x → x ∷ [] }
