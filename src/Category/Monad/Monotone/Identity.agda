open import Relation.Binary

module Category.Monad.Monotone.Identity {i}(pre : Preorder i i i) where

open Preorder pre renaming (Carrier to I)

open import Relation.Unary.PredicateTransformer using (Pt)
open import Category.Monad.Monotone pre
open RawMPMonad

Identity : Pt I i
Identity = λ P i → P i

id-monad : RawMPMonad Identity
return id-monad px = px
_≥=_ id-monad c f = f refl c
