------------------------------------------------------------------------
-- The Agda standard library
--
-- Function application of reflected terms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat hiding (_⊔_)

module Reflection.Apply (limit : ℕ) where

open import Category.Monad
open import Data.Bool.Base
open import Data.List
open import Data.Maybe.Base hiding (_>>=_)
open import Data.Product
open import Data.Sum.Base
open import Function.Base
open import Level hiding (suc)
open import Reflection hiding (map-Args ; returnTC ; _≟_ ; _>>=_) renaming (return to returnTC)
open import Reflection.Argument
open import Reflection.Argument.Visibility using () renaming (_≟_ to _≟ᵥ_)
open import Reflection.Pattern hiding (_≟_)
open import Reflection.Term
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (does)
open import Relation.Unary using (Decidable ; _⊢_)

Result : Set → Set
Result A = List ErrorPart ⊎ A

pattern ok v = inj₂ v
pattern err e = inj₁ e

module _ where
  import Data.Sum.Categorical.Left (List ErrorPart) 0ℓ as S
  open RawMonad S.monad

  failed-app : Term → Arg Term → Result Term
  failed-app t (arg _ a) = err (strErr "attempted to apply" ∷ termErr a ∷ strErr "to" ∷ termErr t ∷ [])

  data Fuel : Set 0ℓ where
    fuel : ℕ → Fuel

  {- These functions take a term that needs to be embedded within another term
     and corrects all de-Bruijn indices to existing variables to still refer to
     the same variables after being embedded.

     The first argument is the embedding depth to shift by.

     The second is used during recursion to track the depth within the whole
     term that is being transformed. Non-recursive calls to shift-index should
     pass 0 for this argument.
  -}
  shift-index : ℕ → ℕ → Term → Term
  shift-index-args : ℕ → ℕ → Args Term → Args Term
  shift-index-clauses : ℕ → ℕ → List Clause → List Clause

  shift-index i j (var k args) with does (j ≤? k)
  ...                             | true  = var (i + k) $ shift-index-args i j args
  ...                             | false = var k $ shift-index-args i j args
  shift-index i j (con c args)            = con c $ shift-index-args i j args
  shift-index i j (def f args)            = def f $ shift-index-args i j args
  shift-index i j (meta x args)           = meta x $ shift-index-args i j args
  shift-index i j (lam v (abs s t))       = lam v $ abs s $ shift-index i (suc j) t
  shift-index i j (pat-lam cs args)       = let
    cs = shift-index-clauses i j cs
    args = shift-index-args i j args
    in pat-lam cs args
  shift-index i j (Π[ s ∶ arg v A ] t)    = let
    A = shift-index i j A
    t = shift-index i (suc j) t
    in Π[ s ∶ arg v A ] t
  shift-index i j (sort s)                = sort s
  shift-index i j (lit l)                 = lit l
  shift-index i j unknown                 = unknown

  shift-index-args i j []                 = []
  shift-index-args i j (arg info a ∷ as)  = let
    a = shift-index i j a
    as = shift-index-args i j as
    in arg info a ∷ as

  shift-index-clauses i j []              = []
  shift-index-clauses i j (clause ps t ∷ cs) = let
    t = shift-index i (j + pattern-args-size ps) t
    cs = shift-index-clauses i j cs
    in clause ps t ∷ cs
  shift-index-clauses i j (absurd-clause ps ∷ cs) =
    absurd-clause ps ∷ shift-index-clauses i j cs

  app : ⦃ Fuel ⦄ → Arg Term → Term → Result Term
  app-many : ⦃ Fuel ⦄ → Args Term → Term → Result Term
  subst : ⦃ Fuel ⦄ → ℕ → Term → Term → Result Term
  subst-args : ⦃ Fuel ⦄ → ℕ → Term → Args Term → Result (Args Term)
  subst-clauses : ⦃ Fuel ⦄ → ℕ → Term → List (Clause) → Result (List Clause)

  app a (var x args)      = return $ var x (args ∷ʳ a)
  app a (con c args)      = return $ con c (args ∷ʳ a)
  app a (def f args)      = return $ def f (args ∷ʳ a)
  app a (meta x args)     = return $ meta x (args ∷ʳ a)
  app a (pat-lam cs args) = return $ pat-lam cs (args ∷ʳ a)
  app a @ (arg (arg-info v₁ _) x)
      b @ (lam v₂ (abs _ t))
      with does (v₁ ≟ᵥ v₂)
  ...    | true = subst 0 x t
  ...    | false = failed-app b a
  app a @ (arg (arg-info v₁ _) x)
      b @ (Π[ _ ∶ arg (arg-info v₂ _) _ ] t)
      with does (v₁ ≟ᵥ v₂)
  ...    | true = subst 0 x t
  ...    | false = failed-app b a
  -- catch all
  app a t = failed-app t a

  app-many [] t = return t
  app-many (a ∷ as) t = do
    ta ← app a t
    app-many as ta

  subst i x (var j args) with compare i j
  ...                       | less m k = do
                              args ← subst-args i x args
                              -- decrement j by one since λ was eliminated
                              return $ var (m + k) args -- j ≡ suc (m + k)
  ...                       | greater _ _ = do
                              args ← subst-args i x args
                              -- j refers to variable named inside eliminated λ
                              return $ var j args
  subst ⦃ fuel (suc n) ⦄
        i x (var j args)    | equal _ = do
                              args ← subst-args ⦃ fuel (suc n) ⦄ i x args
                              app-many ⦃ fuel n ⦄ args (shift-index i 0 x)
  subst ⦃ fuel zero ⦄
        i x (var j [])      | equal _ = return x
  subst ⦃ fuel zero ⦄
        _ _ (var j (_ ∷ _)) | equal _ = err (strErr "evaluation limit reached" ∷ [])
  subst i x (con c args) = do
    args ← subst-args i x args
    return $ con c args
  subst i x (def f args) = do
    args ← subst-args i x args
    return $ def f args
  subst i x (lam v (abs s t)) = do
    t ← subst (suc i) x t
    return $ lam v (abs s t)
  subst i x (meta m args) = do
    args ← subst-args i x args
    return $ meta m args
  subst i x (sort s) = return $ sort s
  subst i x (lit l) = return $ lit l
  subst i x unknown = return unknown
  subst i x (pat-lam cs args) = do
    cs ← subst-clauses i x cs
    args ← subst-args i x args
    return $ pat-lam cs args
  subst i x (Π[ s ∶ arg v A ] t) = do
    A ← subst i x A
    t ← subst (suc i) x t
    return $ Π[ s ∶ arg v A ] t

  subst-args i x [] = return []
  subst-args i x (arg v a ∷ as) = do
    a ← subst i x a
    as ← subst-args i x as
    return $ arg v a ∷ as

  subst-clauses i x [] = return []
  subst-clauses i x (clause ps t ∷ cs) = do
    t ← subst (i + pattern-args-size ps) x t
    cs ← subst-clauses i x cs
    return $ clause ps t ∷ cs
  subst-clauses i x (absurd-clause ps ∷ cs) = do
    cs ← subst-clauses i x cs
    return $ absurd-clause ps ∷ cs

{- Apply an argument to a term. Fails if the recusion limit is reached or an
   attempt is made to apply an argument to non-function-like term.
-}
apply : Term → Arg Term → Result Term
apply f x = app ⦃ fuel limit ⦄ x f

{- Retrieve any trailing arguments in a term -}
term-args : Term → Maybe (Args Term)
term-args (var _ args)     = just args
term-args (con _ args)     = just args
term-args (def _ args)     = just args
term-args (pat-lam _ args) = just args
term-args (meta _ args)    = just args
-- catch all
term-args other            = nothing

{- Like term-args, but contains only the visible arguments -}
term-vis-args : Term → Maybe (List Term)
term-vis-args t = do
  args ← term-args t
  just $ Data.List.map (λ {(arg _ t) → t}) $ filter is-vis args
  where
  open Data.Maybe.Base using (_>>=_)
  args = term-args t
  is-vis : Decidable ((λ {(arg (arg-info v _) _) → v}) ⊢ (_≡ visible))
  is-vis (arg (arg-info v r) x) = v ≟ᵥ visible

{- Conveniently convert a Result into a TC -}
Result→TC : {A : Set} → Result A → TC A
Result→TC (err e) = typeError e
Result→TC (ok v)  = returnTC v
