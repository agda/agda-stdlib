------------------------------------------------------------------------
-- The Agda standard library
--
-- Alpha equality over terms
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.AlphaEquality where

open import Data.Bool.Base             using (Bool; true; false; _∧_)
open import Data.List.Base             using ([]; _∷_)
open import Data.Nat.Base as ℕ        using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product.Base          using (_,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary            using (DecidableEquality)

open import Reflection.AST.Abstraction
open import Reflection.AST.Argument
open import Reflection.AST.Argument.Information as ArgInfo
open import Reflection.AST.Argument.Modality    as Modality
open import Reflection.AST.Argument.Visibility  as Visibility
open import Reflection.AST.Meta                 as Meta
open import Reflection.AST.Name                 as Name
open import Reflection.AST.Literal              as Literal
open import Reflection.AST.Term
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

record AlphaEquality (A : Set) : Set where
  constructor mkAlphaEquality
  infix 4 _=α=_
  field
    _=α=_ : A → A → Bool

open AlphaEquality {{...}} public

------------------------------------------------------------------------
-- Utilities

≟⇒α : DecidableEquality A → AlphaEquality A
≟⇒α _≟_ = mkAlphaEquality (λ x y → ⌊ x ≟ y ⌋)

------------------------------------------------------------------------
-- Propositional cases

-- In the following cases alpha equality coincides with propositiona
-- equality

instance
  α-Visibility : AlphaEquality Visibility
  α-Visibility = ≟⇒α Visibility._≟_

  α-Modality : AlphaEquality Modality
  α-Modality = ≟⇒α Modality._≟_

  α-ArgInfo : AlphaEquality ArgInfo
  α-ArgInfo = ≟⇒α ArgInfo._≟_

  α-Literal : AlphaEquality Literal
  α-Literal = ≟⇒α Literal._≟_

  α-Meta : AlphaEquality Meta
  α-Meta = ≟⇒α Meta._≟_

  α-Name : AlphaEquality Name
  α-Name = ≟⇒α Name._≟_

------------------------------------------------------------------------
-- Interesting cases

-- This is where we deviate from propositional equality and ignore the
-- names of the binders.

-- Unfortunately we can't declare these as instances directly as the
-- termination checker isn't clever enough to peer inside the records.

mutual
  _=α=-AbsTerm_ : Abs Term → Abs Term → Bool
  (abs s a) =α=-AbsTerm (abs s′ a′) = a =α=-Term a′

  _=α=-Telescope_ : Telescope → Telescope → Bool
  []             =α=-Telescope []                = true
  ((s , x) ∷ xs) =α=-Telescope ((s' , x′) ∷ xs′) = (x =α=-ArgTerm x′) ∧ (xs =α=-Telescope xs′)
  []             =α=-Telescope (_ ∷ _)           = false
  (_ ∷ _)        =α=-Telescope []                = false

------------------------------------------------------------------------
-- Remaining cases

-- The following cases simply recurse over the remaining AST in exactly
-- the same way as propositional equality.

  _=α=-ArgTerm_ : Arg Term → Arg Term → Bool
  (arg i a) =α=-ArgTerm (arg i′ a′) = a =α=-Term a′

  _=α=-ArgPattern_ : Arg Pattern → Arg Pattern → Bool
  (arg i a) =α=-ArgPattern (arg i′ a′) = a =α=-Pattern a′

  _=α=-Term_ : Term → Term → Bool
  (var     x  args) =α=-Term (var     x′  args′) = (x  ℕ.≡ᵇ  x′)  ∧ (args =α=-ArgsTerm args′)
  (con     c  args) =α=-Term (con     c′  args′) = (c  =α= c′)  ∧ (args =α=-ArgsTerm args′)
  (def     f  args) =α=-Term (def     f′  args′) = (f  =α= f′)  ∧ (args =α=-ArgsTerm args′)
  (meta    x  args) =α=-Term (meta     x′ args′) = (x  =α= x′)  ∧ (args =α=-ArgsTerm args′)
  (pat-lam cs args) =α=-Term (pat-lam cs′ args′) = (cs =α=-Clauses cs′) ∧ (args =α=-ArgsTerm args′)
  (pi t₁ t₂  )      =α=-Term (pi t₁′ t₂′  )      = (t₁ =α=-ArgTerm t₁′) ∧ (t₂   =α=-AbsTerm t₂′)
  (sort s    )      =α=-Term (sort s′     )      = s   =α=-Sort s′
  (lam v t   )      =α=-Term (lam v′ t′   )      = (v  =α= v′)  ∧ (t =α=-AbsTerm t′)
  (lit l     )      =α=-Term (lit l′      )      = l   =α= l′
  (unknown   )      =α=-Term (unknown     )      = true

  (var x args )     =α=-Term (con c args′)       = false
  (var x args )     =α=-Term (def f args′)       = false
  (var x args )     =α=-Term (lam v t    )       = false
  (var x args )     =α=-Term (pi t₁ t₂   )       = false
  (var x args )     =α=-Term (sort _     )       = false
  (var x args )     =α=-Term (lit _      )       = false
  (var x args )     =α=-Term (meta _ _   )       = false
  (var x args )     =α=-Term (unknown    )       = false
  (con c args )     =α=-Term (var x args′)       = false
  (con c args )     =α=-Term (def f args′)       = false
  (con c args )     =α=-Term (lam v t    )       = false
  (con c args )     =α=-Term (pi t₁ t₂   )       = false
  (con c args )     =α=-Term (sort _     )       = false
  (con c args )     =α=-Term (lit _      )       = false
  (con c args )     =α=-Term (meta _ _   )       = false
  (con c args )     =α=-Term (unknown    )       = false
  (def f args )     =α=-Term (var x args′)       = false
  (def f args )     =α=-Term (con c args′)       = false
  (def f args )     =α=-Term (lam v t    )       = false
  (def f args )     =α=-Term (pi t₁ t₂   )       = false
  (def f args )     =α=-Term (sort _     )       = false
  (def f args )     =α=-Term (lit _      )       = false
  (def f args )     =α=-Term (meta _ _   )       = false
  (def f args )     =α=-Term (unknown    )       = false
  (lam v t    )     =α=-Term (var x args )       = false
  (lam v t    )     =α=-Term (con c args )       = false
  (lam v t    )     =α=-Term (def f args )       = false
  (lam v t    )     =α=-Term (pi t₁ t₂   )       = false
  (lam v t    )     =α=-Term (sort _     )       = false
  (lam v t    )     =α=-Term (lit _      )       = false
  (lam v t    )     =α=-Term (meta _ _   )       = false
  (lam v t    )     =α=-Term (unknown    )       = false
  (pi t₁ t₂   )     =α=-Term (var x args )       = false
  (pi t₁ t₂   )     =α=-Term (con c args )       = false
  (pi t₁ t₂   )     =α=-Term (def f args )       = false
  (pi t₁ t₂   )     =α=-Term (lam v t    )       = false
  (pi t₁ t₂   )     =α=-Term (sort _     )       = false
  (pi t₁ t₂   )     =α=-Term (lit _      )       = false
  (pi t₁ t₂   )     =α=-Term (meta _ _   )       = false
  (pi t₁ t₂   )     =α=-Term (unknown    )       = false
  (sort _     )     =α=-Term (var x args )       = false
  (sort _     )     =α=-Term (con c args )       = false
  (sort _     )     =α=-Term (def f args )       = false
  (sort _     )     =α=-Term (lam v t    )       = false
  (sort _     )     =α=-Term (pi t₁ t₂   )       = false
  (sort _     )     =α=-Term (lit _      )       = false
  (sort _     )     =α=-Term (meta _ _   )       = false
  (sort _     )     =α=-Term (unknown    )       = false
  (lit _      )     =α=-Term (var x args )       = false
  (lit _      )     =α=-Term (con c args )       = false
  (lit _      )     =α=-Term (def f args )       = false
  (lit _      )     =α=-Term (lam v t    )       = false
  (lit _      )     =α=-Term (pi t₁ t₂   )       = false
  (lit _      )     =α=-Term (sort _     )       = false
  (lit _      )     =α=-Term (meta _ _   )       = false
  (lit _      )     =α=-Term (unknown    )       = false
  (meta _ _   )     =α=-Term (var x args )       = false
  (meta _ _   )     =α=-Term (con c args )       = false
  (meta _ _   )     =α=-Term (def f args )       = false
  (meta _ _   )     =α=-Term (lam v t    )       = false
  (meta _ _   )     =α=-Term (pi t₁ t₂   )       = false
  (meta _ _   )     =α=-Term (sort _     )       = false
  (meta _ _   )     =α=-Term (lit _      )       = false
  (meta _ _   )     =α=-Term (unknown    )       = false
  (unknown    )     =α=-Term (var x args )       = false
  (unknown    )     =α=-Term (con c args )       = false
  (unknown    )     =α=-Term (def f args )       = false
  (unknown    )     =α=-Term (lam v t    )       = false
  (unknown    )     =α=-Term (pi t₁ t₂   )       = false
  (unknown    )     =α=-Term (sort _     )       = false
  (unknown    )     =α=-Term (lit _      )       = false
  (unknown    )     =α=-Term (meta _ _   )       = false
  (pat-lam _ _)     =α=-Term (var x args )       = false
  (pat-lam _ _)     =α=-Term (con c args )       = false
  (pat-lam _ _)     =α=-Term (def f args )       = false
  (pat-lam _ _)     =α=-Term (lam v t    )       = false
  (pat-lam _ _)     =α=-Term (pi t₁ t₂   )       = false
  (pat-lam _ _)     =α=-Term (sort _     )       = false
  (pat-lam _ _)     =α=-Term (lit _      )       = false
  (pat-lam _ _)     =α=-Term (meta _ _   )       = false
  (pat-lam _ _)     =α=-Term (unknown    )       = false
  (var x args )     =α=-Term (pat-lam _ _)       = false
  (con c args )     =α=-Term (pat-lam _ _)       = false
  (def f args )     =α=-Term (pat-lam _ _)       = false
  (lam v t    )     =α=-Term (pat-lam _ _)       = false
  (pi t₁ t₂   )     =α=-Term (pat-lam _ _)       = false
  (sort _     )     =α=-Term (pat-lam _ _)       = false
  (lit _      )     =α=-Term (pat-lam _ _)       = false
  (meta _ _   )     =α=-Term (pat-lam _ _)       = false
  (unknown    )     =α=-Term (pat-lam _ _)       = false

  _=α=-Sort_ : Sort → Sort → Bool
  (set t    ) =α=-Sort (set t′    ) = t =α=-Term t′
  (lit n    ) =α=-Sort (lit n′    ) = n ℕ.≡ᵇ n′
  (prop t   ) =α=-Sort (prop t′   ) = t =α=-Term t′
  (propLit n) =α=-Sort (propLit n′) = n ℕ.≡ᵇ n′
  (inf n    ) =α=-Sort (inf n′    ) = n ℕ.≡ᵇ n′
  (unknown  ) =α=-Sort (unknown   ) = true

  (set _    ) =α=-Sort (lit _    ) = false
  (set _    ) =α=-Sort (prop _   ) = false
  (set _    ) =α=-Sort (propLit _) = false
  (set _    ) =α=-Sort (inf _    ) = false
  (set _    ) =α=-Sort (unknown  ) = false
  (lit _    ) =α=-Sort (set _    ) = false
  (lit _    ) =α=-Sort (prop _   ) = false
  (lit _    ) =α=-Sort (propLit _) = false
  (lit _    ) =α=-Sort (inf _    ) = false
  (lit _    ) =α=-Sort (unknown  ) = false
  (prop _   ) =α=-Sort (set _    ) = false
  (prop _   ) =α=-Sort (lit _    ) = false
  (prop _   ) =α=-Sort (propLit _) = false
  (prop _   ) =α=-Sort (inf _    ) = false
  (prop _   ) =α=-Sort (unknown  ) = false
  (propLit _) =α=-Sort (set _    ) = false
  (propLit _) =α=-Sort (lit _    ) = false
  (propLit _) =α=-Sort (prop _   ) = false
  (propLit _) =α=-Sort (inf _    ) = false
  (propLit _) =α=-Sort (unknown  ) = false
  (inf _    ) =α=-Sort (set _    ) = false
  (inf _    ) =α=-Sort (lit _    ) = false
  (inf _    ) =α=-Sort (prop _   ) = false
  (inf _    ) =α=-Sort (propLit _) = false
  (inf _    ) =α=-Sort (unknown  ) = false
  (unknown  ) =α=-Sort (set _    ) = false
  (unknown  ) =α=-Sort (lit _    ) = false
  (unknown  ) =α=-Sort (prop _   ) = false
  (unknown  ) =α=-Sort (propLit _) = false
  (unknown  ) =α=-Sort (inf _    ) = false

  _=α=-Clause_ : Clause → Clause → Bool
  (clause tel ps b)      =α=-Clause (clause tel′ ps′ b′)     = (tel =α=-Telescope tel′) ∧ (ps =α=-ArgsPattern ps′) ∧ (b =α=-Term b′)
  (absurd-clause tel ps) =α=-Clause (absurd-clause tel′ ps′) = (tel =α=-Telescope tel′) ∧ (ps =α=-ArgsPattern ps′)
  (clause _ _ _)         =α=-Clause (absurd-clause _ _)      = false
  (absurd-clause _ _)    =α=-Clause (clause _ _ _)           = false

  _=α=-Clauses_ : Clauses → Clauses → Bool
  []       =α=-Clauses []         = true
  (x ∷ xs) =α=-Clauses (x′ ∷ xs′) = (x =α=-Clause x′) ∧ (xs =α=-Clauses xs′)
  []       =α=-Clauses (_ ∷ _)    = false
  (_ ∷ _)  =α=-Clauses []         = false

  _=α=-ArgsTerm_ : Args Term → Args Term → Bool
  []       =α=-ArgsTerm []         = true
  (x ∷ xs) =α=-ArgsTerm (x′ ∷ xs′) = (x =α=-ArgTerm x′) ∧ (xs =α=-ArgsTerm xs′)
  []       =α=-ArgsTerm (_ ∷ _)    = false
  (_ ∷ _)  =α=-ArgsTerm []         = false

  _=α=-Pattern_ : Pattern → Pattern → Bool
  (con c ps) =α=-Pattern (con c′ ps′) = (c =α= c′) ∧ (ps =α=-ArgsPattern ps′)
  (var x   ) =α=-Pattern (var x′    ) = x ℕ.≡ᵇ x′
  (lit l   ) =α=-Pattern (lit l′    ) = l =α= l′
  (proj a  ) =α=-Pattern (proj a′   ) = a =α= a′
  (dot t   ) =α=-Pattern (dot t′    ) = t =α=-Term t′
  (absurd x) =α=-Pattern (absurd x′ ) = x ℕ.≡ᵇ x′

  (con x x₁) =α=-Pattern (dot x₂    ) = false
  (con x x₁) =α=-Pattern (var x₂    ) = false
  (con x x₁) =α=-Pattern (lit x₂    ) = false
  (con x x₁) =α=-Pattern (proj x₂   ) = false
  (con x x₁) =α=-Pattern (absurd x₂ ) = false
  (dot x   ) =α=-Pattern (con x₁ x₂ ) = false
  (dot x   ) =α=-Pattern (var x₁    ) = false
  (dot x   ) =α=-Pattern (lit x₁    ) = false
  (dot x   ) =α=-Pattern (proj x₁   ) = false
  (dot x   ) =α=-Pattern (absurd x₁ ) = false
  (var s   ) =α=-Pattern (con x x₁  ) = false
  (var s   ) =α=-Pattern (dot x     ) = false
  (var s   ) =α=-Pattern (lit x     ) = false
  (var s   ) =α=-Pattern (proj x    ) = false
  (var s   ) =α=-Pattern (absurd x  ) = false
  (lit x   ) =α=-Pattern (con x₁ x₂ ) = false
  (lit x   ) =α=-Pattern (dot x₁    ) = false
  (lit x   ) =α=-Pattern (var _     ) = false
  (lit x   ) =α=-Pattern (proj x₁   ) = false
  (lit x   ) =α=-Pattern (absurd x₁ ) = false
  (proj x  ) =α=-Pattern (con x₁ x₂ ) = false
  (proj x  ) =α=-Pattern (dot x₁    ) = false
  (proj x  ) =α=-Pattern (var _     ) = false
  (proj x  ) =α=-Pattern (lit x₁    ) = false
  (proj x  ) =α=-Pattern (absurd x₁ ) = false
  (absurd x) =α=-Pattern (con x₁ x₂ ) = false
  (absurd x) =α=-Pattern (dot x₁    ) = false
  (absurd x) =α=-Pattern (var _     ) = false
  (absurd x) =α=-Pattern (lit x₁    ) = false
  (absurd x) =α=-Pattern (proj x₁   ) = false

  _=α=-ArgsPattern_ : Args Pattern → Args Pattern → Bool
  []       =α=-ArgsPattern []         = true
  (x ∷ xs) =α=-ArgsPattern (x′ ∷ xs′) = (x =α=-ArgPattern x′) ∧ (xs =α=-ArgsPattern xs′)
  []       =α=-ArgsPattern (_ ∷ _)    = false
  (_ ∷ _)  =α=-ArgsPattern []         = false

------------------------------------------------------------------------
-- Instance declarations for mutually recursive cases

instance
  α-AbsTerm : AlphaEquality (Abs Term)
  α-AbsTerm = mkAlphaEquality _=α=-AbsTerm_

  α-ArgTerm : AlphaEquality (Arg Term)
  α-ArgTerm = mkAlphaEquality _=α=-ArgTerm_

  α-ArgPattern : AlphaEquality (Arg Pattern)
  α-ArgPattern = mkAlphaEquality _=α=-ArgPattern_

  α-Telescope : AlphaEquality Telescope
  α-Telescope = mkAlphaEquality _=α=-Telescope_

  α-Term : AlphaEquality Term
  α-Term = mkAlphaEquality _=α=-Term_

  α-Sort : AlphaEquality Sort
  α-Sort = mkAlphaEquality _=α=-Sort_

  α-Clause : AlphaEquality Clause
  α-Clause = mkAlphaEquality _=α=-Clause_

  α-Clauses : AlphaEquality Clauses
  α-Clauses = mkAlphaEquality _=α=-Clauses_

  α-ArgsTerm : AlphaEquality (Args Term)
  α-ArgsTerm = mkAlphaEquality _=α=-ArgsTerm_

  α-Pattern : AlphaEquality Pattern
  α-Pattern = mkAlphaEquality _=α=-Pattern_

  α-ArgsPattern : AlphaEquality (Args Pattern)
  α-ArgsPattern = mkAlphaEquality _=α=-ArgsPattern_
