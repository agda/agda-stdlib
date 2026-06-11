------------------------------------------------------------------------
-- The Agda standard library
--
-- Inductive pointwise lifting of relations to vectors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Binary.Pointwise.Inductive where

open import Algebra.Definitions
  using (Associative; Commutative; LeftIdentity; RightIdentity; Congruent₂)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; uncurry; <_,_>)
open import Data.Vec.Base as Vec hiding ([_]; head; tail; map; lookup; uncons)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Level using (Level; _⊔_)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.Core using (REL; Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.Structures
  using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Definitions
  using (Trans; Decidable; Reflexive; Sym; Antisym; Irrelevant)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Decidable using (yes; no; _×?_; map′)
open import Relation.Unary using (Pred)

private
  variable
    a b c d ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    n : ℕ

------------------------------------------------------------------------
-- Definition

infixr 5 _∷_

data Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ) :
               ∀ {m n} (xs : Vec A m) (ys : Vec B n) → Set (a ⊔ b ⊔ ℓ)
               where
  []  : Pointwise _∼_ [] []
  _∷_ : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n}
        (x∼y : x ∼ y) (xs∼ys : Pointwise _∼_ xs ys) →
        Pointwise _∼_ (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Properties

length-equal : ∀ {m n} {_∼_ : REL A B ℓ} {xs : Vec A m} {ys : Vec B n} →
               Pointwise _∼_ xs ys → m ≡ n
length-equal []          = ≡.refl
length-equal (_ ∷ xs∼ys) = ≡.cong suc (length-equal xs∼ys)

------------------------------------------------------------------------
-- Operations

module _ {_∼_ : REL A B ℓ} where

  head : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
         Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
  head (x∼y ∷ xs∼ys) = x∼y

  tail : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
         Pointwise _∼_ (x ∷ xs) (y ∷ ys) → Pointwise _∼_ xs ys
  tail (x∼y ∷ xs∼ys) = xs∼ys

  uncons : ∀ {m n x y} {xs : Vec A m} {ys : Vec B n} →
           Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y × Pointwise _∼_ xs ys
  uncons = < head , tail >

  lookup : ∀ {n} {xs : Vec A n} {ys : Vec B n} → Pointwise _∼_ xs ys →
           ∀ i → (Vec.lookup xs i) ∼ (Vec.lookup ys i)
  lookup (x∼y ∷ _)     zero    = x∼y
  lookup (_   ∷ xs∼ys) (suc i) = lookup xs∼ys i

  map : ∀ {ℓ₂} {_≈_ : REL A B ℓ₂} →
        _≈_ ⇒ _∼_ → ∀ {m n} → Pointwise _≈_ ⇒ Pointwise _∼_ {m} {n}
  map ∼₁⇒∼₂ []             = []
  map ∼₁⇒∼₂ (x∼y ∷ xs∼ys) = ∼₁⇒∼₂ x∼y ∷ map ∼₁⇒∼₂ xs∼ys

------------------------------------------------------------------------
-- Relational properties

irrelevant : ∀ {_∼_ : REL A B ℓ} {n m} → Irrelevant _∼_ → Irrelevant (Pointwise _∼_ {n} {m})
irrelevant irr []      []      = ≡.refl
irrelevant irr (p ∷ r) (q ∷ s) = ≡.cong₂ _∷_ (irr p q) (irrelevant irr r s)

refl : ∀ {_∼_ : Rel A ℓ} {n} →
       Reflexive _∼_ → Reflexive (Pointwise _∼_ {n})
refl ∼-refl {[]}     = []
refl ∼-refl {x ∷ xs} = ∼-refl ∷ refl ∼-refl

sym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {m n} →
      Sym P Q → Sym (Pointwise P) (Pointwise Q {m} {n})
sym sm []            = []
sym sm (x∼y ∷ xs∼ys) = sm x∼y ∷ sym sm xs∼ys

trans : ∀ {P : REL A B ℓ₁} {Q : REL B C ℓ₂} {R : REL A C ℓ} {m n o} →
        Trans P Q R →
        Trans (Pointwise P {m}) (Pointwise Q {n} {o}) (Pointwise R)
trans trns []            []            = []
trans trns (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
  trns x∼y y∼z ∷ trans trns xs∼ys ys∼zs

antisym : ∀ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} {R : REL A B ℓ} {m n} →
          Antisym P Q R → Antisym (Pointwise P {m}) (Pointwise Q {n}) (Pointwise R)
antisym asym []            []            = []
antisym asym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) = asym x∼y y∼x ∷ antisym asym xs∼ys ys∼xs

decidable : ∀ {_∼_ : REL A B ℓ} →
            Decidable _∼_ → ∀ {m n} → Decidable (Pointwise _∼_ {m} {n})
decidable dec []       []       = yes []
decidable dec []       (y ∷ ys) = no λ()
decidable dec (x ∷ xs) []       = no λ()
decidable dec (x ∷ xs) (y ∷ ys) =
  map′ (uncurry _∷_) uncons (dec x y ×? decidable dec xs ys)

------------------------------------------------------------------------
-- Structures

module _ {_∼_ : Rel A ℓ} where

  isEquivalence : IsEquivalence _∼_ → ∀ n →
                  IsEquivalence (Pointwise _∼_ {n})
  isEquivalence equiv n = record
    { refl  = refl  Eq.refl
    ; sym   = sym   Eq.sym
    ; trans = trans Eq.trans
    } where module Eq = IsEquivalence equiv

  isDecEquivalence : IsDecEquivalence _∼_ → ∀ n →
                     IsDecEquivalence (Pointwise _∼_ {n})
  isDecEquivalence decEquiv n = record
    { isEquivalence = isEquivalence Eq.isEquivalence n
    ; _≟_           = decidable Eq._≈?_
    } where module Eq = IsDecEquivalence decEquiv

------------------------------------------------------------------------
-- Bundles

setoid : Setoid a ℓ → ℕ → Setoid a (a ⊔ ℓ)
setoid S n = record
   { isEquivalence = isEquivalence Eq.isEquivalence n
   } where module Eq = Setoid S

decSetoid : DecSetoid a ℓ → ℕ → DecSetoid a (a ⊔ ℓ)
decSetoid S n = record
   { isDecEquivalence = isDecEquivalence Eq.isDecEquivalence n
   } where module Eq = DecSetoid S

------------------------------------------------------------------------
-- map

module _ {_∼₁_ : REL A B ℓ₁} {_∼₂_ : REL C D ℓ₂}
         {f : A → C} {g : B → D}
         where

  map⁺ : (∀ {x y} → x ∼₁ y → f x ∼₂ g y) →
         ∀ {m n xs ys} → Pointwise _∼₁_ {m} {n} xs ys →
         Pointwise _∼₂_ (Vec.map f xs) (Vec.map g ys)
  map⁺ ∼₁⇒∼₂ []             = []
  map⁺ ∼₁⇒∼₂ (x∼y ∷ xs∼ys) = ∼₁⇒∼₂ x∼y ∷ map⁺ ∼₁⇒∼₂ xs∼ys

------------------------------------------------------------------------
-- _++_

module _ {_∼_ : REL A B ℓ} where

  ++⁺ : ∀ {m n p q}
        {ws : Vec A m} {xs : Vec B p} {ys : Vec A n} {zs : Vec B q} →
        Pointwise _∼_ ws xs → Pointwise _∼_ ys zs →
        Pointwise _∼_ (ws ++ ys) (xs ++ zs)
  ++⁺ []            ys∼zs = ys∼zs
  ++⁺ (w∼x ∷ ws∼xs) ys∼zs = w∼x ∷ (++⁺ ws∼xs ys∼zs)

  ++ˡ⁻ : ∀ {m n}
         (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs : Vec B n} →
         Pointwise _∼_ (ws ++ ys) (xs ++ zs) → Pointwise _∼_ ws xs
  ++ˡ⁻ []       []        _                    = []
  ++ˡ⁻ (w ∷ ws) (x ∷ xs) (w∼x ∷ ps) = w∼x ∷ ++ˡ⁻ ws xs ps

  ++ʳ⁻ : ∀ {m n}
         (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs : Vec B n} →
         Pointwise _∼_ (ws ++ ys) (xs ++ zs) → Pointwise _∼_ ys zs
  ++ʳ⁻ [] [] ys∼zs = ys∼zs
  ++ʳ⁻ (w ∷ ws) (x ∷ xs) (_ ∷ ps) = ++ʳ⁻ ws xs ps

  ++⁻ : ∀ {m n}
        (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs : Vec B n} →
        Pointwise _∼_ (ws ++ ys) (xs ++ zs) →
        Pointwise _∼_ ws xs × Pointwise _∼_ ys zs
  ++⁻ ws xs ps = ++ˡ⁻ ws xs ps , ++ʳ⁻ ws xs ps

------------------------------------------------------------------------
-- concat

module _ {_∼_ : REL A B ℓ} where

  concat⁺ : ∀ {m n p q}
            {xss : Vec (Vec A m) n} {yss : Vec (Vec B p) q} →
            Pointwise (Pointwise _∼_) xss yss →
            Pointwise _∼_ (concat xss) (concat yss)
  concat⁺ []           = []
  concat⁺ (xs∼ys ∷ ps) = ++⁺ xs∼ys (concat⁺ ps)

  concat⁻ : ∀ {m n} (xss : Vec (Vec A m) n) (yss : Vec (Vec B m) n) →
            Pointwise _∼_ (concat xss) (concat yss) →
            Pointwise (Pointwise _∼_) xss yss
  concat⁻ []         []         [] = []
  concat⁻ (xs ∷ xss) (ys ∷ yss) ps =
    ++ˡ⁻ xs ys ps ∷ concat⁻ xss yss (++ʳ⁻ xs ys ps)

------------------------------------------------------------------------
-- tabulate

module _ {_∼_ : REL A B ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
              (∀ i → f i ∼ g i) →
              Pointwise _∼_ (tabulate f) (tabulate g)
  tabulate⁺ {zero}  f∼g = []
  tabulate⁺ {suc n} f∼g = f∼g zero ∷ tabulate⁺ (f∼g ∘ suc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
              Pointwise _∼_ (tabulate f) (tabulate g) →
              (∀ i → f i ∼ g i)
  tabulate⁻ (f₀∼g₀ ∷ _)   zero    = f₀∼g₀
  tabulate⁻ (_     ∷ f∼g) (suc i) = tabulate⁻ f∼g i

------------------------------------------------------------------------
-- cong

module _ {_∼_ : Rel A ℓ} (refl : Reflexive _∼_) where
  cong-[_]≔ : ∀ {n} i p {xs} {ys} →
              Pointwise _∼_ {n} xs ys →
              Pointwise _∼_ (xs [ i ]≔ p) (ys [ i ]≔ p)
  cong-[ zero ]≔  p (_   ∷ eqn) = refl ∷ eqn
  cong-[ suc i ]≔ p (x∼y ∷ eqn) = x∼y  ∷ cong-[ i ]≔ p eqn

------------------------------------------------------------------------
-- zipWith

module _ {_∼_ : Rel A ℓ} where
  module _ {f : A → A → A} where
    zipWith-assoc : Associative _∼_ f →
                    Associative (Pointwise _∼_) (zipWith {n = n} f)
    zipWith-assoc assoc [] [] [] = []
    zipWith-assoc assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = assoc x y z ∷ zipWith-assoc assoc xs ys zs

  module _ {f : A → A → A} {e : A} where
    zipWith-identityˡ : LeftIdentity _∼_ e f →
                        LeftIdentity (Pointwise _∼_) (replicate n e) (zipWith f)
    zipWith-identityˡ idˡ []       = []
    zipWith-identityˡ idˡ (x ∷ xs) = idˡ x ∷ zipWith-identityˡ idˡ xs

    zipWith-identityʳ : RightIdentity _∼_ e f →
                        RightIdentity (Pointwise _∼_) (replicate n e) (zipWith f)
    zipWith-identityʳ idʳ []       = []
    zipWith-identityʳ idʳ (x ∷ xs) = idʳ x ∷ zipWith-identityʳ idʳ xs

  module _ {f : A → A → A} where
    zipWith-comm : Commutative _∼_ f →
                   Commutative (Pointwise _∼_) (zipWith {n = n} f)
    zipWith-comm comm []       []       = []
    zipWith-comm comm (x ∷ xs) (y ∷ ys) = comm x y ∷ zipWith-comm comm xs ys

  module _ {f : A → A → A} where
    zipWith-cong : ∀ {m n}
          {ws : Vec A m} {xs : Vec A n} {ys : Vec A m} {zs : Vec A n} →
          Congruent₂ _∼_ f →
          Pointwise _∼_ ws xs → Pointwise _∼_ ys zs →
          Pointwise _∼_ (zipWith f ws ys) (zipWith f xs zs)
    zipWith-cong cong [] [] = []
    zipWith-cong cong (x∼y ∷ xs) (a∼b ∷ ys) = cong x∼y a∼b ∷ zipWith-cong cong xs ys

------------------------------------------------------------------------
-- Degenerate pointwise relations

module _ {P : Pred A ℓ} where

  Pointwiseˡ⇒All : ∀ {m n} {xs : Vec A m} {ys : Vec B n} →
                   Pointwise (λ x y → P x) xs ys → All P xs
  Pointwiseˡ⇒All []       = []
  Pointwiseˡ⇒All (p ∷ ps) = p ∷ Pointwiseˡ⇒All ps

  Pointwiseʳ⇒All : ∀ {n} {xs : Vec B n} {ys : Vec A n} →
                   Pointwise (λ x y → P y) xs ys → All P ys
  Pointwiseʳ⇒All []       = []
  Pointwiseʳ⇒All (p ∷ ps) = p ∷ Pointwiseʳ⇒All ps

  All⇒Pointwiseˡ : ∀ {n} {xs : Vec A n} {ys : Vec B n} →
                   All P xs → Pointwise (λ x y → P x) xs ys
  All⇒Pointwiseˡ {ys = []}    []       = []
  All⇒Pointwiseˡ {ys = _ ∷ _} (p ∷ ps) = p ∷ All⇒Pointwiseˡ ps

  All⇒Pointwiseʳ : ∀ {n} {xs : Vec B n} {ys : Vec A n} →
                   All P ys → Pointwise (λ x y → P y) xs ys
  All⇒Pointwiseʳ {xs = []}    []       = []
  All⇒Pointwiseʳ {xs = _ ∷ _} (p ∷ ps) = p ∷ All⇒Pointwiseʳ ps

------------------------------------------------------------------------
-- Pointwise _≡_ is equivalent to _≡_

Pointwise-≡⇒≡ : ∀ {n} {xs ys : Vec A n} → Pointwise _≡_ xs ys → xs ≡ ys
Pointwise-≡⇒≡ []               = ≡.refl
Pointwise-≡⇒≡ (≡.refl ∷ xs∼ys) = ≡.cong (_ ∷_) (Pointwise-≡⇒≡ xs∼ys)

≡⇒Pointwise-≡ : ∀ {n} {xs ys : Vec A n} → xs ≡ ys → Pointwise _≡_ xs ys
≡⇒Pointwise-≡ ≡.refl = refl ≡.refl

Pointwise-≡↔≡ : ∀ {n} {xs ys : Vec A n} → Pointwise _≡_ xs ys ⇔ xs ≡ ys
Pointwise-≡↔≡ = mk⇔ Pointwise-≡⇒≡ ≡⇒Pointwise-≡
