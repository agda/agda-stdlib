------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

open import Level
open import Function
open import Relation.Nullary

------------------------------------------------------------------------
-- The type and some operations

open import Data.Maybe.Base public

------------------------------------------------------------------------
-- Maybe monad

open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity

functor : ∀ {f} → RawFunctor (Maybe {a = f})
functor = record
  { _<$>_ = map
  }

monadT : ∀ {f} {M : Set f → Set f} →
         RawMonad M → RawMonad (λ A → M (Maybe A))
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → M._>>=_ m (maybe f (M.return nothing))
  }
  where module M = RawMonad M

monad : ∀ {f} → RawMonad (Maybe {a = f})
monad = monadT IdentityMonad

monadZero : ∀ {f} → RawMonadZero (Maybe {a = f})
monadZero = record
  { monad = monad
  ; ∅     = nothing
  }

monadPlus : ∀ {f} → RawMonadPlus (Maybe {a = f})
monadPlus {f} = record
  { monadZero = monadZero
  ; _∣_       = _∣_
  }
  where
  _∣_ : {A : Set f} → Maybe A → Maybe A → Maybe A
  nothing ∣ y = y
  just x  ∣ y = just x

------------------------------------------------------------------------
-- Equality

open import Relation.Binary as B

data Eq {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) : Rel (Maybe A) (a ⊔ ℓ) where
  just    : ∀ {x y} (x≈y : x ≈ y) → Eq _≈_ (just x) (just y)
  nothing : Eq _≈_ nothing nothing

drop-just : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} {x y : A} →
            just x ⟨ Eq _≈_ ⟩ just y → x ≈ y
drop-just (just x≈y) = x≈y

refl : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
       Reflexive _≈_ → Reflexive (Eq _≈_)
refl refl {just x}  = just refl
refl refl {nothing} = nothing

sym :  ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
       Symmetric _≈_ → Symmetric (Eq _≈_)
sym sym (just x≈y) = just (sym x≈y)
sym sym nothing    = nothing

trans : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
       Transitive _≈_ → Transitive (Eq _≈_)
trans trans (just x≈y) (just y≈z) = just (trans x≈y y≈z)
trans trans nothing    nothing    = nothing

dec : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
      B.Decidable _≈_ → B.Decidable (Eq _≈_)
dec dec (just x) (just y)  with dec x y
...  | yes x≈y = yes (just x≈y)
...  | no  x≉y = no (x≉y ∘ drop-just)
dec dec (just x) nothing = no λ()
dec dec nothing (just y)  = no λ()
dec dec nothing nothing = yes nothing

isEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
                → IsEquivalence _≈_ → IsEquivalence (Eq _≈_)
isEquivalence isEq = record
    { refl  = refl (IsEquivalence.refl isEq)
    ; sym   = sym (IsEquivalence.sym isEq)
    ; trans = trans (IsEquivalence.trans isEq)
    }

setoid : ∀ {ℓ₁ ℓ₂} → Setoid ℓ₁ ℓ₂ → Setoid _ _
setoid S = record
  { Carrier       = Maybe (Setoid.Carrier S)
  ; _≈_           = Eq (Setoid._≈_ S)
  ; isEquivalence = isEquivalence (Setoid.isEquivalence S)
  }

isDecEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
                → IsDecEquivalence _≈_ → IsDecEquivalence (Eq _≈_)
isDecEquivalence isDecEq = record
    { isEquivalence = isEquivalence
                        (IsDecEquivalence.isEquivalence isDecEq)
    ; _≟_           = dec (IsDecEquivalence._≟_ isDecEq)
    }

decSetoid : ∀ {ℓ₁ ℓ₂} → DecSetoid ℓ₁ ℓ₂ → DecSetoid _ _
decSetoid D = record
  { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence D)
  }


------------------------------------------------------------------------
-- Any and All are preserving decidability

import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U

anyDec : ∀ {a p} {A : Set a} {P : A → Set p} →
         U.Decidable P → U.Decidable (Any P)
anyDec p nothing  = no λ()
anyDec p (just x) = Dec.map′ just (λ { (Any.just px) → px }) (p x)

allDec : ∀ {a p} {A : Set a} {P : A → Set p} →
         U.Decidable P → U.Decidable (All P)
allDec p nothing  = yes nothing
allDec p (just x) = Dec.map′ just (λ { (All.just px) → px }) (p x)
