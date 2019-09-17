{-# OPTIONS --without-K --safe #-}

module Reflection.Helpers where

open import Agda.Builtin.Reflection
open import Function
open import Data.List as List using (List; _∷_; [])
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.GeneralisedArithmetic using (fold)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)
open import Data.Nat.Table as Table using (Table)
open import Data.String using (String)
open import Data.Maybe as Maybe using (Maybe; just; nothing)

module _ {a} {A : Set a} where
  pure : A → TC A
  pure = returnTC
  {-# INLINE pure #-}

  infixl 3 _<|>_
  _<|>_ : TC A → TC A → TC A
  _<|>_ = catchTC
  {-# INLINE _<|>_ #-}

module _ {a b} {A : Set a} {B : Set b} where
  infixl 1 _>>=_ _>>_ _<&>_
  _>>=_ : TC A → (A → TC B) → TC B
  _>>=_ = bindTC
  {-# INLINE _>>=_ #-}

  _>>_ : TC A → TC B → TC B
  xs >> ys = bindTC xs (λ _ → ys)
  {-# INLINE _>>_ #-}

  infixl 4 _<$>_ _<*>_ _<$_
  _<*>_ : TC (A → B) → TC A → TC B
  fs <*> xs = bindTC fs (λ f → bindTC xs (λ x → returnTC (f x)))
  {-# INLINE _<*>_ #-}

  _<$>_ : (A → B) → TC A → TC B
  f <$> xs = bindTC xs (λ x → returnTC (f x))
  {-# INLINE _<$>_ #-}

  _<$_ : A → TC B → TC A
  x <$ xs = bindTC xs (λ _ → returnTC x)
  {-# INLINE _<$_ #-}

  _<&>_ : TC A → (A → B) → TC B
  xs <&> f = bindTC xs (λ x → returnTC (f x))
  {-# INLINE _<&>_ #-}

infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs = arg (arg-info visible relevant) x ∷ xs
pattern _⟅∷⟆_ x xs = arg (arg-info hidden  relevant) x ∷ xs

infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_ : ℕ → List (Arg Term) → List (Arg Term)
zero  ⋯⟅∷⟆ xs = xs
suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆ i ⋯⟅∷⟆ xs
{-# INLINE _⋯⟅∷⟆_ #-}

ℕ′ : ℕ → Term
ℕ′ zero = quote zero ⟨ con ⟩ []
ℕ′ (suc i) = quote suc ⟨ con ⟩ ℕ′ i ⟨∷⟩ []

Fin′ : ℕ → Term
Fin′ zero = quote Fin.zero ⟨ con ⟩ 1 ⋯⟅∷⟆ []
Fin′ (suc i) = quote Fin.suc ⟨ con ⟩ 1 ⋯⟅∷⟆ Fin′ i ⟨∷⟩ []

curriedTerm : Table → Term
curriedTerm = List.foldr go (quote Vec.[] ⟨ con ⟩ 2 ⋯⟅∷⟆ []) ∘ Table.toList
  where
  go : ℕ → Term → Term
  go x xs = quote Vec._∷_ ⟨ con ⟩ 3 ⋯⟅∷⟆ var x [] ⟨∷⟩ xs ⟨∷⟩ []

hlams : ∀ {n} → Vec String n → Term → Term
hlams vs xs = Vec.foldr (const Term) (λ v vs → lam hidden (abs v vs)) xs vs

vlams : ∀ {n} → Vec String n → Term → Term
vlams vs xs = Vec.foldr (const Term) (λ v vs → lam visible (abs v vs)) xs vs

getVisible : Arg Term → Maybe Term
getVisible (arg (arg-info visible relevant) x) = just x
getVisible (arg (arg-info visible irrelevant) x) = nothing
getVisible (arg (arg-info hidden r) x) = nothing
getVisible (arg (arg-info instance′ r) x) = nothing

getArgs : ∀ n → Term → Maybe (Vec Term n)
getArgs n (def _ xs) = Maybe.map Vec.reverse (List.foldl f b (List.mapMaybe getVisible xs) n)
  where
  f : (∀ n → Maybe (Vec Term n)) → Term → ∀ n → Maybe (Vec Term n)
  f xs x zero = just Vec.[]
  f xs x (suc n) = Maybe.map (x Vec.∷_) (xs n)

  b : ∀ n → Maybe (Vec Term n)
  b zero = just Vec.[]
  b (suc _ ) = nothing
getArgs _ _ = nothing

open import Data.Product

underPi : Term → ∃[ n ] (Vec String n × Term)
underPi = go (λ xs y → _ , xs , y)
  where
  go : {A : Set} → (∀ {n} → Vec String n → Term → A) → Term → A
  go k (pi a (abs s x)) = go (k ∘ (s Vec.∷_)) x
  go k t = k Vec.[] t
