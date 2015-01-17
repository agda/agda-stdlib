
module Data.Permutation where

open import Data.Nat
  renaming
    (ℕ to Nat ; zero to nz ; suc to ns ; _+_ to _+N_; _*_ to _*N_)
open import Data.Fin
  renaming
    (zero to fz ; suc to fs; _+_ to _+F_)

open import Data.Vec
  renaming (allFin to enumFin)

infixr 5 _∷_



-- For all n m : Nat, Inj n m is a type of injective functions from Fin n to Fin m 

data Inj : Nat → Nat → Set where
  []  : {m   : Nat} → Inj 0 m
  _∷_ : {n m : Nat}(x : Fin (ns m))(p : Inj n m) → Inj (ns n) (ns m)

-- Enumerates all injective functions of type Inj n m

size : Nat → Nat → Nat
size 0      m      = 1
size (ns n) 0      = 0
size (ns n) (ns m) = (ns m) *N (size n m)

enum : (n m : Nat) → Vec (Inj n m) (size n m)
enum nz     m  = [ [] ]
enum (ns n) nz =   []
enum (ns n) (ns m) with enum n m | enumFin (ns m)
enum (ns n) (ns m) | e0 | e1 = map _∷_ e1 ⊛* e0 

-- Injection of Fin n into Fin m

<_> : {n m : Nat} → Inj n m → Fin n → Fin m 
< [] >      ()
< (x ∷ p) > fz     = x
< (x ∷ p) > (fs y) = thin x (< p > y)

-- Identity

id : {n : Nat} → Inj n n 
id {nz}   = []
id {ns n} = fz ∷ id

-- Deletes element defined by first argument

delete : {n m : Nat} → Fin (ns n) → Inj (ns n) (ns m) → Inj n m
delete  fz           (x ∷ p)                    = p
delete (fs {nz} ())   p
delete (fs {ns n} z) (_∷_ {.(ns n)} {nz} x ())
delete (fs {ns n} z) (_∷_ {.(ns n)} {ns m} x p) = thick x (< p > z) ∷ delete z p 

-- Inserts pair (x , y) into function p 
-- that is < insert x y p > x = y  

insert : {n m : Nat} → Fin (ns n) → Fin (ns m) → Inj n m → Inj (ns n) (ns m)
insert  x     y  []     = y ∷ []
insert  fz    y (z ∷ p) = y ∷ (z ∷ p)
insert (fs x) y (z ∷ p) = (thin y z) ∷ (insert x (thick y z) p)

infixr 4 _∘_

-- Composition of injective functions

_∘_ : {n m k : Nat}(f : Inj n m)(g : Inj m k) → Inj n k
[]      ∘  g       = []
(x ∷ f) ∘ (y ∷ g) = < y ∷ g > x ∷ (f ∘ delete x (y ∷ g))

-- Permutation is an injective function from Fin n to Fin n

Permutation : Nat → Set
Permutation n = Inj n n

-- Annihilator of permutation p is an element x such that < p > x = 0 

annihilator : {n : Nat} → Permutation (ns n) → Fin (ns n)
annihilator ( fz           ∷ p) = fz
annihilator ((fs {nz} ())  ∷ p)
annihilator ((fs {ns n} x) ∷ p) = fs (annihilator p)

-- Inverse permutation
 
_⁻¹ : {n : Nat}(f : Permutation n) → Permutation n 
_⁻¹ {nz}   f = f
_⁻¹ {ns n} f = annihilator f ∷ (delete (annihilator f) f ⁻¹)
