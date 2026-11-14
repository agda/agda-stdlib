------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to recursive vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Recursive.Relation.Binary.Pointwise where

open import Algebra.Definitions
  using (Associative; Commutative; LeftIdentity; RightIdentity; Congruent₂)
open import Data.Nat.Base hiding (_^_)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡; ≡⇒≡×≡)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Vec.Recursive as Vec hiding (cons; head; lookup; map; splitAt; tail; uncons)
open import Level using (Level)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.Core using (REL; Rel; _⇒_)
open import Relation.Binary.Structures
  using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Definitions
  using (Trans; Decidable; Reflexive; Sym; Antisym; Irrelevant)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Decidable using (yes; no; _×?_)

private
  variable
    a b c d ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Definition

Pointwise : REL A B ℓ → ∀ n → REL (A ^ n) (B ^ n) ℓ
Pointwise R 0      _        _        = ⊤
Pointwise R 1      a        b        = R a b
Pointwise R (2+ _) (a , as) (b , bs) = R a b × Pointwise R _ as bs

------------------------------------------------------------------------
-- Operations

module _ {_~_ : REL A B ℓ} where

  cons : ∀ {x y} n {xs : A ^ n} {ys : B ^ n} →
    x ~ y → Pointwise _~_ n xs ys →
    Pointwise _~_ (suc n) (Vec.cons n x xs) (Vec.cons n y ys)
  cons 0       x~y _     = x~y
  cons (suc _) x~y xs~ys = x~y , xs~ys

  uncons : ∀ n {xs : A ^ suc n} {ys : B ^ suc n} →
    Pointwise _~_ (suc n) xs ys →
    Vec.head n xs ~ Vec.head n ys × Pointwise _~_ n (Vec.tail n xs) (Vec.tail n ys)
  uncons 0       xs~ys = xs~ys , tt
  uncons (suc _) xs~ys = xs~ys

  head : ∀ n {xs : A ^ suc n} {ys : B ^ suc n} →
    Pointwise _~_ (suc n) xs ys →
    Vec.head n xs ~ Vec.head n ys
  head n xs~ys = proj₁ (uncons n xs~ys)

  tail : ∀ n {xs : A ^ suc n} {ys : B ^ suc n} →
    (xs~ys : Pointwise _~_ (suc n) xs ys) →
    Pointwise _~_ n (Vec.tail n xs) (Vec.tail n ys)
  tail n xs~ys = proj₂ (uncons n xs~ys)

  lookup : ∀ n {xs : A ^ n} {ys : B ^ n} →
    Pointwise _~_ n xs ys →
    ∀ i → (Vec.lookup xs i) ~ (Vec.lookup ys i)
  lookup 0       xs~ys ()
  lookup (suc n) xs~ys zero    = head n xs~ys
  lookup (suc n) xs~ys (suc i) = lookup n (tail n xs~ys) i

  map : ∀ {ℓ₂} {_≈_ : REL A B ℓ₂} →
    _≈_ ⇒ _~_ → ∀ n → Pointwise _≈_ n ⇒ Pointwise _~_ n
  map ≈⇒~ 0       x≈y           = tt
  map ≈⇒~ (suc 0) x≈y           = ≈⇒~ x≈y
  map ≈⇒~ (2+ n)  (x≈y , xs≈ys) = ≈⇒~ x≈y , map ≈⇒~ (suc n) xs≈ys

------------------------------------------------------------------------
-- Relational properties

irrelevant : ∀ {_~_ : REL A B ℓ} n → Irrelevant _~_ → Irrelevant (Pointwise _~_ n)
irrelevant 0       _   _        _        = ≡.refl
irrelevant (suc 0) irr p        q        = irr p q
irrelevant (2+ n)  irr (p , ps) (q , qs) = ≡×≡⇒≡ (irr p q , irrelevant (suc n) irr ps qs)

refl : ∀ {_~_ : Rel A ℓ} n → Reflexive _~_ → Reflexive (Pointwise _~_ n)
refl 0       _      = tt
refl (suc 0) ~-refl = ~-refl
refl (2+ n)  ~-refl = ~-refl , refl (suc n) ~-refl

sym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} n →
      Sym P Q → Sym (Pointwise P n) (Pointwise Q n)
sym 0       _  _             = tt
sym (suc 0) sm x~y           = sm x~y
sym (2+ n)  sm (x~y , xs~ys) = sm x~y , sym (suc n) sm xs~ys

trans : ∀ {P : REL A B ℓ₁} {Q : REL B C ℓ₂} {R : REL A C ℓ} n →
        Trans P Q R →
        Trans (Pointwise P n) (Pointwise Q n) (Pointwise R n)
trans 0       _    _             _             = tt
trans (suc 0) trns x~y           y~z           = trns x~y y~z
trans (2+ n)  trns (x~y , xs~ys) (y~z , ys~zs) = trns x~y y~z , trans (suc n) trns xs~ys ys~zs

antisym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {R : REL A B ℓ} n →
          Antisym P Q R → Antisym (Pointwise P n) (Pointwise Q n) (Pointwise R n)
antisym 0       _    _   _ = tt
antisym (suc 0) asym x~y y~x = asym x~y y~x
antisym (2+ n)  asym (x~y , xs~ys) (y~x , ys~xs) = asym x~y y~x , antisym (suc n) asym xs~ys ys~xs

decidable : ∀ {_∼_ : REL A B ℓ} n → Decidable _∼_ → Decidable (Pointwise _∼_ n)
decidable 0       _   _ _ = yes tt
decidable (suc 0) dec x y = dec x y
decidable (2+ n)  dec (x , xs) (y , ys) = dec x y ×? decidable (suc n) dec xs ys

------------------------------------------------------------------------
-- Structures

module _ {_∼_ : Rel A ℓ} where

  isEquivalence : IsEquivalence _∼_ → ∀ n →
                  IsEquivalence (Pointwise _∼_ n)
  isEquivalence equiv n = record
    { refl  = refl  n Eq.refl
    ; sym   = sym   n Eq.sym
    ; trans = trans n Eq.trans
    } where module Eq = IsEquivalence equiv

  isDecEquivalence : IsDecEquivalence _∼_ → ∀ n →
                     IsDecEquivalence (Pointwise _∼_ n)
  isDecEquivalence decEquiv n = record
    { isEquivalence = isEquivalence Eq.isEquivalence n
    ; _≈?_          = decidable n Eq._≈?_
    } where module Eq = IsDecEquivalence decEquiv

------------------------------------------------------------------------
-- Bundles

setoid : Setoid a ℓ → ℕ → Setoid a ℓ
setoid S n = record
   { isEquivalence = isEquivalence Eq.isEquivalence n
   } where module Eq = Setoid S

decSetoid : DecSetoid a ℓ → ℕ → DecSetoid a ℓ
decSetoid S n = record
   { isDecEquivalence = isDecEquivalence Eq.isDecEquivalence n
   } where module Eq = DecSetoid S

------------------------------------------------------------------------
-- map

module _ {_∼₁_ : REL A B ℓ₁} {_∼₂_ : REL C D ℓ₂}
         {f : A → C} {g : B → D}
         where

  map⁺ : (∀ {x y} → x ∼₁ y → f x ∼₂ g y) →
         ∀ n {xs ys} → Pointwise _∼₁_ n xs ys →
         Pointwise _∼₂_ n (Vec.map f n xs) (Vec.map g n ys)
  map⁺ ~₁⇒~₂ 0       _             = tt
  map⁺ ~₁⇒~₂ (suc 0) x~y           = ~₁⇒~₂ x~y
  map⁺ ~₁⇒~₂ (2+ n)  (x~y , xs~ys) = ~₁⇒~₂ x~y , map⁺ ~₁⇒~₂ (suc n) xs~ys

------------------------------------------------------------------------
-- splitAt

splitAt : ∀ {_∼_ : REL A B ℓ} m n {xs : A ^ (m + n)} {ys : B ^ (m + n)} →
          Pointwise _∼_ (m + n) xs ys →
          (let (xs₁ , xs₂) = Vec.splitAt m n xs)
          (let (ys₁ , ys₂) = Vec.splitAt m n ys) →
          Pointwise _∼_ m xs₁ ys₁ × Pointwise _∼_ n xs₂ ys₂
splitAt zero    n x~y           = tt , x~y
splitAt (suc 0) n x~y           = uncons n x~y
splitAt (2+ m)  n (x~y , xs~ys) =
  let (r , rs) = splitAt (suc m) n xs~ys
  in (x~y , r) , rs

------------------------------------------------------------------------
-- tabulate

module _ {_∼_ : REL A B ℓ} where

  tabulate⁺ : ∀ n {f : Fin n → A} {g : Fin n → B} →
              (∀ i → f i ∼ g i) →
              Pointwise _∼_ n (tabulate n f) (tabulate n g)
  tabulate⁺ 0       f~g = tt
  tabulate⁺ (suc 0) f~g = f~g zero
  tabulate⁺ (2+ n)  f~g = f~g zero , tabulate⁺ (suc n) (f~g ∘ suc)

  tabulate⁻ : ∀ n {f : Fin n → A} {g : Fin n → B} →
              Pointwise _∼_ n (tabulate n f) (tabulate n g) →
              (∀ i → f i ∼ g i)
  tabulate⁻ (suc 0)        f~g           zero    = f~g
  tabulate⁻ (2+ n)         (f₀~g₀ , _)   zero    = f₀~g₀
  tabulate⁻ (2+ n) {f} {g} (_     , f~g) (suc i) = tabulate⁻ (suc n) {f = f ∘ suc} {g = g ∘ suc} f~g i

------------------------------------------------------------------------
-- zipWith

module _ {_∼_ : Rel A ℓ} where
  module _ {f : A → A → A} where
    zipWith-assoc : ∀ n → Associative _∼_ f →
                    Associative (Pointwise _∼_ n) (zipWith f n)
    zipWith-assoc 0       assoc _        _        _        = tt
    zipWith-assoc (suc 0) assoc                            = assoc
    zipWith-assoc (2+ n)  assoc (x , xs) (y , ys) (z , zs) =
      assoc x y z , zipWith-assoc (suc n) assoc xs ys zs

  module _ {f : A → A → A} {e : A} where
    zipWith-identityˡ : ∀ n → LeftIdentity _∼_ e f →
                        LeftIdentity (Pointwise _∼_ n) (replicate n e) (zipWith f n)
    zipWith-identityˡ zero    _   _        = tt
    zipWith-identityˡ (suc 0) idˡ x        = idˡ x
    zipWith-identityˡ (2+ n)  idˡ (x , xs) = idˡ x , zipWith-identityˡ (suc n) idˡ xs

    zipWith-identityʳ : ∀ n → RightIdentity _∼_ e f →
                        RightIdentity (Pointwise _∼_ n) (replicate n e) (zipWith f n)
    zipWith-identityʳ zero    _   _        = tt
    zipWith-identityʳ (suc 0) idʳ x        = idʳ x
    zipWith-identityʳ (2+ n)  idʳ (x , xs) = idʳ x , zipWith-identityʳ (suc n) idʳ xs


  module _ {f : A → A → A} where
    zipWith-comm : ∀ n → Commutative _∼_ f →
                   Commutative (Pointwise _∼_ n) (zipWith f n)
    zipWith-comm 0       _    _        _        = tt
    zipWith-comm (suc 0) comm                   = comm
    zipWith-comm (2+ n)  comm (x , xs) (y , ys) = comm x y , zipWith-comm (suc n) comm xs ys

  module _ {f : A → A → A} where
    zipWith-cong : ∀ n
          {ws : A ^ n} {xs : A ^ n} {ys : A ^ n} {zs : A ^ n} →
          Congruent₂ _∼_ f →
          Pointwise _∼_ n ws xs → Pointwise _∼_ n ys zs →
          Pointwise _∼_ n (zipWith f n ws ys) (zipWith f n xs zs)
    zipWith-cong 0       cong w~x           y~z           = tt
    zipWith-cong (suc 0) cong w~x           y~z           = cong w~x y~z
    zipWith-cong (2+ n)  cong (w~x , ws~xs) (y~z , ys~zs) =
      cong w~x y~z , zipWith-cong (suc n) cong ws~xs ys~zs

------------------------------------------------------------------------
-- Pointwise _≡_ is equivalent to _≡_

Pointwise-≡⇒≡ : ∀ n {xs ys : A ^ n} → Pointwise _≡_ n xs ys → xs ≡ ys
Pointwise-≡⇒≡ 0       _     = ≡.refl
Pointwise-≡⇒≡ (suc 0) xs≡ys = xs≡ys
Pointwise-≡⇒≡ (2+ n)  (x≡y , xs≡ys) = ≡×≡⇒≡ (x≡y , Pointwise-≡⇒≡ (suc n) xs≡ys)

≡⇒Pointwise-≡ : ∀ n {xs ys : A ^ n} → xs ≡ ys → Pointwise _≡_ n xs ys
≡⇒Pointwise-≡ 0       _     = tt
≡⇒Pointwise-≡ (suc 0) xs≡ys = xs≡ys
≡⇒Pointwise-≡ (2+ n) ≡.refl = ≡.refl , ≡⇒Pointwise-≡ (suc n) ≡.refl

Pointwise-≡↔≡ : ∀ n {xs ys : A ^ n} → Pointwise _≡_ n xs ys ⇔ xs ≡ ys
Pointwise-≡↔≡ n = mk⇔ (Pointwise-≡⇒≡ n) (≡⇒Pointwise-≡ n)
