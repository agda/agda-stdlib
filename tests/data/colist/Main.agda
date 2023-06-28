{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Level using (0ℓ)
open import Size
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin
import Data.Fin.Show as Fin
open import Data.String.Base using (String; _++_; parens)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Codata.Sized.Thunk
open import Function.Base using (_$_; _∘_; id)
open import Relation.Nullary

open import Codata.Musical.Notation
open import Codata.Sized.Colist using (Colist; _∷_; [])
open import Codata.Musical.Colist renaming (Colist to Colist♩) using (_∷_; [])
open import Codata.Musical.Conversion

variable
  i : Size
  m n : ℕ
  A : Set

data Lam (n : ℕ) : Set where
  var : Fin n → Lam n
  app : Lam n → Lam n → Lam n
  lam : Lam (suc n) → Lam n

data Loc : Set where appL appR lam : Loc

appParens : Loc → String → String
appParens appR str = parens str
appParens _ str = str

lamParens : Loc → String → String
lamParens lam str = str
lamParens _ str = parens str

show : Loc → Lam n → String
show i (var v)   = Fin.show v
show i (app f t) = appParens i $ show appL f ++ " " ++ show appR t
show i (lam b)   = lamParens i $ "λ " ++ show lam b

variable
  b f t : Lam n

_∙_ : (Fin m → A) → A → Fin (suc m) → A
(ρ ∙ v) zero    = v
(ρ ∙ v) (suc k) = ρ k

rename : (Fin m → Fin n) → Lam m → Lam n
rename ρ (var v)   = var (ρ v)
rename ρ (app f t) = app (rename ρ f) (rename ρ t)
rename ρ (lam b)   = lam (rename ((suc ∘ ρ) ∙ zero) b)

subst : (Fin m → Lam n) → Lam m → Lam n
subst ρ (var v)   = ρ v
subst ρ (app f t) = app (subst ρ f) (subst ρ t)
subst ρ (lam b)   = lam (subst ((rename suc ∘ ρ) ∙ var zero) b)

data Redex {n} : Lam n → Set where
  here : ∀ b t → Redex (app (lam b) t)
  lam  : Redex b → Redex (lam b)
  appL : Redex f → ∀ t → Redex (app f t)
  appR : ∀ f → Redex t → Redex (app f t)

redex : ∀ {n} (t : Lam n) → Dec (Redex t)
redex (var v)             = no (λ ())
redex (app (lam b) t)     = yes (here b t)
redex (app f@(var _) t)   with redex t
... | yes rt = yes (appR f rt)
... | no nrt = no λ where (appR _ rt) → nrt rt
redex (app f@(app _ _) t) with redex f | redex t
... | yes rf | _ = yes (appL rf t)
... | _ | yes rt = yes (appR f rt)
... | no nrf | no nrt = no λ where
  (appL rf _) → nrf rf
  (appR _ rt) → nrt rt
redex (lam b) with redex b
... | yes rb = yes (lam rb)
... | no nrb = no λ where (lam rb) → nrb rb

fire : Redex {n} t → Lam n
fire (here b t)  = subst (var ∙ t) b
fire (lam rt)    = lam (fire rt)
fire (appL rf t) = app (fire rf) t
fire (appR f rt) = app f (fire rt)

eval : Lam n → Colist (Lam n) i
eval t with redex t
... | yes rt = t ∷ λ where .force → eval (fire rt)
... | no nrt = t ∷ λ where .force → []

open import IO.Base
open import IO.Finite

trace : Colist♩ (Lam n) → IO {0ℓ} ⊤
trace []       = pure _
trace (t ∷ ts) = seq (♯ putStrLn (show lam t))
                     (♯ trace (♭ ts))

`id : Lam 0
`id = lam (var (# 0))

main : Main
main = run $ do
  trace (Colist.toMusical $ eval `id)
  trace (Colist.toMusical $ eval (app `id (app (app `id `id) (app `id `id))))
