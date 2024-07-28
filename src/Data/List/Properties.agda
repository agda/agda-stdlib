------------------------------------------------------------------------
-- The Agda standard library
--
-- List-related properties
------------------------------------------------------------------------

-- Note that the lemmas below could be generalised to work with other
-- equalities than _≡_.

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-} -- for deprecated scans

module Data.List.Properties where

open import Algebra.Bundles
open import Algebra.Consequences.Propositional
 using (selfInverse⇒involutive; selfInverse⇒injective)
open import Algebra.Definitions as AlgebraicDefinitions using (SelfInverse; Involutive)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism; IsMonoidHomomorphism)
import Algebra.Structures as AlgebraicStructures
open import Data.Bool.Base using (Bool; false; true; not; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; cast; toℕ)
open import Data.List.Base as List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.Any using (just) renaming (Any to MAny)
open import Data.Nat.Base
open import Data.Nat.Divisibility using (_∣_; divides; ∣n⇒∣m*n)
open import Data.Nat.Properties
open import Data.Product.Base as Product
  using (_×_; _,_; uncurry; uncurry′; proj₁; proj₂; <_,_>)
import Data.Product.Relation.Unary.All as Product using (All)
open import Data.Sum using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Fin.Properties using (toℕ-cast)
open import Function.Base using (id; _∘_; _∘′_; _∋_; _-⟨_∣; ∣_⟩-_; _$_; const; flip)
open import Function.Definitions using (Injective)
open import Level using (Level)
open import Relation.Binary.Definitions as B using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary using (¬_; Dec; does; _because_; yes; no; contradiction)
open import Relation.Nullary.Decidable as Decidable using (isYes; map′; ⌊_⌋; ¬?; _×-dec_)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Relation.Unary.Properties using (∁?)
import Data.Nat.GeneralisedArithmetic as ℕ

open ≡-Reasoning

private
  variable
    a b c d e p ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    x y z w : A
    xs ys zs ws : List A

------------------------------------------------------------------------
-- _∷_

∷-injective : x ∷ xs ≡ y List.∷ ys → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

∷-injectiveˡ : x ∷ xs ≡ y List.∷ ys → x ≡ y
∷-injectiveˡ refl = refl

∷-injectiveʳ : x ∷ xs ≡ y List.∷ ys → xs ≡ ys
∷-injectiveʳ refl = refl

∷-dec : Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y List.∷ ys)
∷-dec x≟y xs≟ys = Decidable.map′ (uncurry (cong₂ _∷_)) ∷-injective (x≟y ×-dec xs≟ys)

≡-dec : DecidableEquality A → DecidableEquality (List A)
≡-dec _≟_ []       []       = yes refl
≡-dec _≟_ (x ∷ xs) []       = no λ()
≡-dec _≟_ []       (y ∷ ys) = no λ()
≡-dec _≟_ (x ∷ xs) (y ∷ ys) = ∷-dec (x ≟ y) (≡-dec _≟_ xs ys)

------------------------------------------------------------------------
-- map

map-id : map id ≗ id {A = List A}
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-id-local : ∀ {f : A → A} {xs} → All (λ x → f x ≡ x) xs → map f xs ≡ xs
map-id-local []           = refl
map-id-local (fx≡x ∷ pxs) = cong₂ _∷_ fx≡x (map-id-local pxs)

map-++ : ∀ (f : A → B) xs ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

map-cong-local : ∀ {f g : A → B} {xs} →
            All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
map-cong-local []                = refl
map-cong-local (fx≡gx ∷ fxs≡gxs) = cong₂ _∷_ fx≡gx (map-cong-local fxs≡gxs)

length-map : ∀ (f : A → B) xs → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

map-∘ : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
map-∘ []       = refl
map-∘ (x ∷ xs) = cong (_ ∷_) (map-∘ xs)

map-injective : ∀ {f : A → B} → Injective _≡_ _≡_ f → Injective _≡_ _≡_ (map f)
map-injective finj {[]} {[]} eq = refl
map-injective finj {x ∷ xs} {y ∷ ys} eq =
  let fx≡fy , fxs≡fys = ∷-injective eq in
  cong₂ _∷_ (finj fx≡fy) (map-injective finj fxs≡fys)

------------------------------------------------------------------------
-- _++_

length-++ : ∀ (xs : List A) {ys} →
            length (xs ++ ys) ≡ length xs + length ys
length-++ []       = refl
length-++ (x ∷ xs) = cong suc (length-++ xs)

module _ {A : Set a} where

  open AlgebraicDefinitions {A = List A} _≡_
  open AlgebraicStructures  {A = List A} _≡_

  ++-assoc : Associative _++_
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  ++-identityˡ : LeftIdentity [] _++_
  ++-identityˡ xs = refl

  ++-identityʳ : RightIdentity [] _++_
  ++-identityʳ []       = refl
  ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

  ++-identity : Identity [] _++_
  ++-identity = ++-identityˡ , ++-identityʳ

  ++-identityʳ-unique : ∀ (xs : List A) {ys} → xs ≡ xs ++ ys → ys ≡ []
  ++-identityʳ-unique []       refl = refl
  ++-identityʳ-unique (x ∷ xs) eq   =
    ++-identityʳ-unique xs (∷-injectiveʳ eq)

  ++-identityˡ-unique : ∀ {xs} (ys : List A) → xs ≡ ys ++ xs → ys ≡ []
  ++-identityˡ-unique               []       _  = refl
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ ys) eq
    with ++-identityˡ-unique (ys ++ [ x ]) (begin
         xs                  ≡⟨ ∷-injectiveʳ eq ⟩
         ys ++ x ∷ xs        ≡⟨ ++-assoc ys [ x ] xs ⟨
         (ys ++ [ x ]) ++ xs ∎)
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ []   ) eq | ()
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ _ ∷ _) eq | ()

  ++-cancelˡ : LeftCancellative _++_
  ++-cancelˡ []       _ _ ys≡zs             = ys≡zs
  ++-cancelˡ (x ∷ xs) _ _ x∷xs++ys≡x∷xs++zs = ++-cancelˡ xs _ _ (∷-injectiveʳ x∷xs++ys≡x∷xs++zs)

  ++-cancelʳ : RightCancellative _++_
  ++-cancelʳ _  []       []       _             = refl
  ++-cancelʳ xs []       (z ∷ zs) eq =
    contradiction (trans (cong length eq) (length-++ (z ∷ zs))) (m≢1+n+m (length xs))
  ++-cancelʳ xs (y ∷ ys) []       eq =
    contradiction (trans (sym (length-++ (y ∷ ys))) (cong length eq)) (m≢1+n+m (length xs) ∘ sym)
  ++-cancelʳ _  (y ∷ ys) (z ∷ zs) eq =
    cong₂ _∷_ (∷-injectiveˡ eq) (++-cancelʳ _ ys zs (∷-injectiveʳ eq))

  ++-cancel : Cancellative _++_
  ++-cancel = ++-cancelˡ , ++-cancelʳ

  ++-conicalˡ : ∀ (xs ys : List A) → xs ++ ys ≡ [] → xs ≡ []
  ++-conicalˡ []       _ refl = refl

  ++-conicalʳ : ∀ (xs ys : List A) → xs ++ ys ≡ [] → ys ≡ []
  ++-conicalʳ []       _ refl = refl

  ++-conical : Conical [] _++_
  ++-conical = ++-conicalˡ , ++-conicalʳ

  ++-isMagma : IsMagma _++_
  ++-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = cong₂ _++_
    }

  ++-isSemigroup : IsSemigroup _++_
  ++-isSemigroup = record
    { isMagma = ++-isMagma
    ; assoc   = ++-assoc
    }

  ++-isMonoid : IsMonoid _++_ []
  ++-isMonoid = record
    { isSemigroup = ++-isSemigroup
    ; identity    = ++-identity
    }

module _ (A : Set a) where

  ++-semigroup : Semigroup a a
  ++-semigroup = record
    { Carrier     = List A
    ; isSemigroup = ++-isSemigroup
    }

  ++-monoid : Monoid a a
  ++-monoid = record
    { Carrier  = List A
    ; isMonoid = ++-isMonoid
    }

module _ (A : Set a) where

  length-isMagmaHomomorphism : IsMagmaHomomorphism (++-rawMagma A) +-rawMagma length
  length-isMagmaHomomorphism = record
    { isRelHomomorphism = record
      { cong = cong length
      }
    ; homo = λ xs ys → length-++ xs {ys}
    }

  length-isMonoidHomomorphism : IsMonoidHomomorphism (++-[]-rawMonoid A) +-0-rawMonoid length
  length-isMonoidHomomorphism = record
    { isMagmaHomomorphism = length-isMagmaHomomorphism
    ; ε-homo = refl
    }

------------------------------------------------------------------------
-- cartesianProductWith

module _ (f : A → B → C) where

  private
    prod = cartesianProductWith f

  cartesianProductWith-zeroˡ : ∀ ys → prod [] ys ≡ []
  cartesianProductWith-zeroˡ _ = refl

  cartesianProductWith-zeroʳ : ∀ xs → prod xs [] ≡ []
  cartesianProductWith-zeroʳ []       = refl
  cartesianProductWith-zeroʳ (x ∷ xs) = cartesianProductWith-zeroʳ xs

  cartesianProductWith-distribʳ-++ : ∀ xs ys zs → prod (xs ++ ys) zs ≡ prod xs zs ++ prod ys zs
  cartesianProductWith-distribʳ-++ []       ys zs = refl
  cartesianProductWith-distribʳ-++ (x ∷ xs) ys zs = begin
    prod (x ∷ xs ++ ys) zs ≡⟨⟩
    map (f x) zs ++ prod (xs ++ ys) zs ≡⟨ cong (map (f x) zs ++_) (cartesianProductWith-distribʳ-++ xs ys zs) ⟩
    map (f x) zs ++ prod xs zs ++ prod ys zs ≡⟨ ++-assoc (map (f x) zs) (prod xs zs) (prod ys zs) ⟨
    (map (f x) zs ++ prod xs zs) ++ prod ys zs ≡⟨⟩
    prod (x ∷ xs) zs ++ prod ys zs ∎

------------------------------------------------------------------------
-- alignWith

module _ {f g : These A B → C} where

  alignWith-cong : f ≗ g → ∀ as → alignWith f as ≗ alignWith g as
  alignWith-cong f≗g []         bs       = map-cong (f≗g ∘ that) bs
  alignWith-cong f≗g as@(_ ∷ _) []       = map-cong (f≗g ∘ this) as
  alignWith-cong f≗g (a ∷ as)   (b ∷ bs) =
    cong₂ _∷_ (f≗g (these a b)) (alignWith-cong f≗g as bs)

module _ {f : These A B → C} where

  length-alignWith : ∀ xs ys →
                   length (alignWith f xs ys) ≡ length xs ⊔ length ys
  length-alignWith []         ys       = length-map (f ∘′ that) ys
  length-alignWith xs@(_ ∷ _) []       = length-map (f ∘′ this) xs
  length-alignWith (x ∷ xs)   (y ∷ ys) = cong suc (length-alignWith xs ys)

  alignWith-map : (g : D → A) (h : E → B) →
                  ∀ xs ys → alignWith f (map g xs) (map h ys) ≡
                            alignWith (f ∘′ These.map g h) xs ys
  alignWith-map g h []         ys     = sym (map-∘ ys)
  alignWith-map g h xs@(_ ∷ _) []     = sym (map-∘ xs)
  alignWith-map g h (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (alignWith-map g h xs ys)

  map-alignWith : ∀ (g : C → D) → ∀ xs ys →
                  map g (alignWith f xs ys) ≡
                  alignWith (g ∘′ f) xs ys
  map-alignWith g []         ys     = sym (map-∘ ys)
  map-alignWith g xs@(_ ∷ _) []     = sym (map-∘ xs)
  map-alignWith g (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (map-alignWith g xs ys)

  alignWith-flip : ∀ xs ys →
                 alignWith f xs ys ≡ alignWith (f ∘ These.swap) ys xs
  alignWith-flip []       []       = refl
  alignWith-flip []       (y ∷ ys) = refl
  alignWith-flip (x ∷ xs) []       = refl
  alignWith-flip (x ∷ xs) (y ∷ ys) = cong (_ ∷_) (alignWith-flip xs ys)

module _ {f : These A A → B} where

  alignWith-comm : f ∘ These.swap ≗ f →
                 ∀ xs ys → alignWith f xs ys ≡ alignWith f ys xs
  alignWith-comm f-comm xs ys = begin
    alignWith f xs ys                ≡⟨ alignWith-flip xs ys ⟩
    alignWith (f ∘ These.swap) ys xs ≡⟨ alignWith-cong f-comm ys xs ⟩
    alignWith f ys xs                ∎

------------------------------------------------------------------------
-- align

align-map : ∀ (f : A → B) (g : C → D) →
            ∀ xs ys → align (map f xs) (map g ys) ≡
                      map (These.map f g) (align xs ys)
align-map f g xs ys = begin
  align (map f xs) (map g ys)       ≡⟨ alignWith-map f g xs ys ⟩
  alignWith (These.map f g) xs ys   ≡⟨ sym (map-alignWith (These.map f g) xs ys) ⟩
  map (These.map f g) (align xs ys) ∎

align-flip : ∀ (xs : List A) (ys : List B) →
             align xs ys ≡ map These.swap (align ys xs)
align-flip xs ys = begin
  align xs ys                  ≡⟨ alignWith-flip xs ys ⟩
  alignWith These.swap ys xs   ≡⟨ sym (map-alignWith These.swap ys xs) ⟩
  map These.swap (align ys xs) ∎

------------------------------------------------------------------------
-- zipWith

module _ {f g : A → B → C} where

  zipWith-cong : (∀ a b → f a b ≡ g a b) → ∀ as → zipWith f as ≗ zipWith g as
  zipWith-cong f≗g []         bs       = refl
  zipWith-cong f≗g as@(_ ∷ _) []       = refl
  zipWith-cong f≗g (a ∷ as)   (b ∷ bs) =
    cong₂ _∷_ (f≗g a b) (zipWith-cong f≗g as bs)

module _ (f : A → B → C) where

  zipWith-zeroˡ : ∀ xs → zipWith f [] xs ≡ []
  zipWith-zeroˡ []       = refl
  zipWith-zeroˡ (x ∷ xs) = refl

  zipWith-zeroʳ : ∀ xs → zipWith f xs [] ≡ []
  zipWith-zeroʳ []       = refl
  zipWith-zeroʳ (x ∷ xs) = refl

  length-zipWith : ∀ xs ys →
                   length (zipWith f xs ys) ≡ length xs ⊓ length ys
  length-zipWith []       []       = refl
  length-zipWith []       (y ∷ ys) = refl
  length-zipWith (x ∷ xs) []       = refl
  length-zipWith (x ∷ xs) (y ∷ ys) = cong suc (length-zipWith xs ys)

  zipWith-map : ∀ (g : D → A) (h : E → B) →
                ∀ xs ys → zipWith f (map g xs) (map h ys) ≡
                          zipWith (λ x y → f (g x) (h y)) xs ys
  zipWith-map g h []       []       = refl
  zipWith-map g h []       (y ∷ ys) = refl
  zipWith-map g h (x ∷ xs) []       = refl
  zipWith-map g h (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (zipWith-map g h xs ys)

  map-zipWith : ∀ (g : C → D) → ∀ xs ys →
                map g (zipWith f xs ys) ≡
                zipWith (λ x y → g (f x y)) xs ys
  map-zipWith g []       []       = refl
  map-zipWith g []       (y ∷ ys) = refl
  map-zipWith g (x ∷ xs) []       = refl
  map-zipWith g (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (map-zipWith g xs ys)

  zipWith-flip : ∀ xs ys → zipWith f xs ys ≡ zipWith (flip f) ys xs
  zipWith-flip []       []       = refl
  zipWith-flip []       (x ∷ ys) = refl
  zipWith-flip (x ∷ xs) []       = refl
  zipWith-flip (x ∷ xs) (y ∷ ys) = cong (f x y ∷_) (zipWith-flip xs ys)

module _ (f : A → A → B) where

  zipWith-comm : (∀ x y → f x y ≡ f y x) →
                 ∀ xs ys → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-comm f-comm xs ys = begin
    zipWith f xs ys        ≡⟨ zipWith-flip f xs ys ⟩
    zipWith (flip f) ys xs ≡⟨ zipWith-cong (flip f-comm) ys xs ⟩
    zipWith f ys xs        ∎

------------------------------------------------------------------------
-- zip

zip-map : ∀ (f : A → B) (g : C → D) →
          ∀ xs ys → zip (map f xs) (map g ys) ≡
                    map (Product.map f g) (zip xs ys)
zip-map f g xs ys = begin
  zip (map f xs) (map g ys)         ≡⟨ zipWith-map _,_ f g xs ys ⟩
  zipWith (λ x y → f x , g y) xs ys ≡⟨ sym (map-zipWith _,_ (Product.map f g) xs ys) ⟩
  map (Product.map f g) (zip xs ys) ∎

zip-flip : ∀ (xs : List A) (ys : List B) →
           zip xs ys ≡ map Product.swap (zip ys xs)
zip-flip xs ys = begin
  zip xs ys                    ≡⟨ zipWith-flip _,_ xs ys ⟩
  zipWith (flip _,_) ys xs     ≡⟨ sym (map-zipWith _,_ Product.swap ys xs) ⟩
  map Product.swap (zip ys xs) ∎

------------------------------------------------------------------------
-- unalignWith

unalignWith-this : unalignWith ((A → These A B) ∋ this) ≗ (_, [])
unalignWith-this []       = refl
unalignWith-this (a ∷ as) = cong (Product.map₁ (a ∷_)) (unalignWith-this as)

unalignWith-that : unalignWith ((B → These A B) ∋ that) ≗ ([] ,_)
unalignWith-that []       = refl
unalignWith-that (b ∷ bs) = cong (Product.map₂ (b ∷_)) (unalignWith-that bs)

module _ {f g : C → These A B} where

  unalignWith-cong : f ≗ g → unalignWith f ≗ unalignWith g
  unalignWith-cong f≗g []       = refl
  unalignWith-cong f≗g (c ∷ cs) with f c | g c | f≗g c
  ... | this a    | ._ | refl = cong (Product.map₁ (a ∷_)) (unalignWith-cong f≗g cs)
  ... | that b    | ._ | refl = cong (Product.map₂ (b ∷_)) (unalignWith-cong f≗g cs)
  ... | these a b | ._ | refl = cong (Product.map (a ∷_) (b ∷_)) (unalignWith-cong f≗g cs)

module _ (f : C → These A B) where

  unalignWith-map : (g : D → C) → ∀ ds →
                    unalignWith f (map g ds) ≡ unalignWith (f ∘′ g) ds
  unalignWith-map g []       = refl
  unalignWith-map g (d ∷ ds) with f (g d)
  ... | this a    = cong (Product.map₁ (a ∷_)) (unalignWith-map g ds)
  ... | that b    = cong (Product.map₂ (b ∷_)) (unalignWith-map g ds)
  ... | these a b = cong (Product.map (a ∷_) (b ∷_)) (unalignWith-map g ds)

  map-unalignWith : (g : A → D) (h : B → E) →
    Product.map (map g) (map h) ∘′ unalignWith f ≗ unalignWith (These.map g h ∘′ f)
  map-unalignWith g h []       = refl
  map-unalignWith g h (c ∷ cs) with f c
  ... | this a    = cong (Product.map₁ (g a ∷_)) (map-unalignWith g h cs)
  ... | that b    = cong (Product.map₂ (h b ∷_)) (map-unalignWith g h cs)
  ... | these a b = cong (Product.map (g a ∷_) (h b ∷_)) (map-unalignWith g h cs)

  unalignWith-alignWith : (g : These A B → C) → f ∘′ g ≗ id → ∀ as bs →
                          unalignWith f (alignWith g as bs) ≡ (as , bs)
  unalignWith-alignWith g g∘f≗id []         bs = begin
    unalignWith f (map (g ∘′ that) bs) ≡⟨ unalignWith-map (g ∘′ that) bs ⟩
    unalignWith (f ∘′ g ∘′ that) bs    ≡⟨ unalignWith-cong (g∘f≗id ∘ that) bs ⟩
    unalignWith that bs                ≡⟨ unalignWith-that bs ⟩
    [] , bs                            ∎
  unalignWith-alignWith g g∘f≗id as@(_ ∷ _) [] = begin
    unalignWith f (map (g ∘′ this) as) ≡⟨ unalignWith-map (g ∘′ this) as ⟩
    unalignWith (f ∘′ g ∘′ this) as    ≡⟨ unalignWith-cong (g∘f≗id ∘ this) as ⟩
    unalignWith this as                ≡⟨ unalignWith-this as ⟩
    as , []                            ∎
  unalignWith-alignWith g g∘f≗id (a ∷ as)   (b ∷ bs)
    rewrite g∘f≗id (these a b) =
    cong (Product.map (a ∷_) (b ∷_)) (unalignWith-alignWith g g∘f≗id as bs)

------------------------------------------------------------------------
-- unzipWith

module _ {f g : A → B × C} where

  unzipWith-cong : f ≗ g → unzipWith f ≗ unzipWith g
  unzipWith-cong f≗g [] = refl
  unzipWith-cong f≗g (x ∷ xs) =
    cong₂ (Product.zip _∷_ _∷_) (f≗g x) (unzipWith-cong f≗g xs)

module _ (f : A → B × C) where

  length-unzipWith₁ : ∀ xys →
                     length (proj₁ (unzipWith f xys)) ≡ length xys
  length-unzipWith₁ []        = refl
  length-unzipWith₁ (x ∷ xys) = cong suc (length-unzipWith₁ xys)

  length-unzipWith₂ : ∀ xys →
                     length (proj₂ (unzipWith f xys)) ≡ length xys
  length-unzipWith₂ []        = refl
  length-unzipWith₂ (x ∷ xys) = cong suc (length-unzipWith₂ xys)

  zipWith-unzipWith : (g : B → C → A) → uncurry′ g ∘ f ≗ id →
                      uncurry′ (zipWith g) ∘ (unzipWith f)  ≗ id
  zipWith-unzipWith g g∘f≗id []       = refl
  zipWith-unzipWith g g∘f≗id (x ∷ xs) =
    cong₂ _∷_ (g∘f≗id x) (zipWith-unzipWith g g∘f≗id xs)

  unzipWith-zipWith : (g : B → C → A) → f ∘ uncurry′ g ≗ id →
                      ∀ xs ys → length xs ≡ length ys →
                      unzipWith f (zipWith g xs ys) ≡ (xs , ys)
  unzipWith-zipWith g f∘g≗id []       []       l≡l = refl
  unzipWith-zipWith g f∘g≗id (x ∷ xs) (y ∷ ys) l≡l  =
    cong₂ (Product.zip _∷_ _∷_) (f∘g≗id (x , y))
          (unzipWith-zipWith g f∘g≗id xs ys (suc-injective l≡l))

  unzipWith-map : (g : D → A) → unzipWith f ∘ map g ≗ unzipWith (f ∘ g)
  unzipWith-map g []       = refl
  unzipWith-map g (x ∷ xs) =
    cong (Product.zip _∷_ _∷_ (f (g x))) (unzipWith-map g xs)

  map-unzipWith : (g : B → D) (h : C → E) →
                  Product.map (map g) (map h) ∘ unzipWith f ≗
                  unzipWith (Product.map g h ∘ f)
  map-unzipWith g h []       = refl
  map-unzipWith g h (x ∷ xs) =
    cong (Product.zip _∷_ _∷_ _) (map-unzipWith g h xs)

  unzipWith-swap : unzipWith (Product.swap ∘ f) ≗
                   Product.swap ∘ unzipWith f
  unzipWith-swap []       = refl
  unzipWith-swap (x ∷ xs) =
    cong (Product.zip _∷_ _∷_ _) (unzipWith-swap xs)

  unzipWith-++ : ∀ xs ys →
                 unzipWith f (xs ++ ys) ≡
                 Product.zip _++_ _++_ (unzipWith f xs) (unzipWith f ys)
  unzipWith-++ []       ys = refl
  unzipWith-++ (x ∷ xs) ys =
    cong (Product.zip _∷_ _∷_ (f x)) (unzipWith-++ xs ys)

------------------------------------------------------------------------
-- unzip

unzip-map : ∀ (f : A → B) (g : C → D) →
            unzip ∘ map (Product.map f g) ≗
            Product.map (map f) (map g) ∘ unzip
unzip-map f g xs = begin
  unzip (map (Product.map f g) xs)       ≡⟨ unzipWith-map id (Product.map f g) xs ⟩
  unzipWith (Product.map f g) xs         ≡⟨ sym (map-unzipWith id f g xs) ⟩
  Product.map (map f) (map g) (unzip xs) ∎

unzip-swap : unzip ∘ map Product.swap ≗ Product.swap ∘ unzip {A = A} {B = B}
unzip-swap xs = begin
  unzip (map Product.swap xs) ≡⟨ unzipWith-map id Product.swap xs ⟩
  unzipWith Product.swap xs   ≡⟨ unzipWith-swap id xs ⟩
  Product.swap (unzip xs)     ∎

zip-unzip : uncurry′ zip ∘ unzip ≗ id {A = List (A × B)}
zip-unzip = zipWith-unzipWith id _,_ λ _ → refl

unzip-zip : ∀ (xs : List A) (ys : List B) →
            length xs ≡ length ys → unzip (zip xs ys) ≡ (xs , ys)
unzip-zip = unzipWith-zipWith id _,_ λ _ → refl

------------------------------------------------------------------------
-- foldr

foldr-universal : ∀ (h : List A → B) f e → (h [] ≡ e) →
                  (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) →
                  h ≗ foldr f e
foldr-universal h f e base step []       = base
foldr-universal h f e base step (x ∷ xs) = begin
  h (x ∷ xs)          ≡⟨ step x xs ⟩
  f x (h xs)          ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩
  f x (foldr f e xs)  ∎

foldr-cong : ∀ {f g : A → B → B} {d e : B} →
             (∀ x y → f x y ≡ g x y) → d ≡ e →
             foldr f d ≗ foldr g e
foldr-cong f≗g refl []      = refl
foldr-cong f≗g d≡e (x ∷ xs) rewrite foldr-cong f≗g d≡e xs = f≗g x _

foldr-fusion : ∀ (h : B → C) {f : A → B → B} {g : A → C → C} (e : B) →
               (∀ x y → h (f x y) ≡ g x (h y)) →
               h ∘ foldr f e ≗ foldr g (h e)
foldr-fusion h {f} {g} e fuse =
  foldr-universal (h ∘ foldr f e) g (h e) refl
                  (λ x xs → fuse x (foldr f e xs))

id-is-foldr : id {A = List A} ≗ foldr _∷_ []
id-is-foldr = foldr-universal id _∷_ [] refl (λ _ _ → refl)

++-is-foldr : (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
++-is-foldr xs ys = begin
  xs ++ ys                ≡⟨ cong (_++ ys) (id-is-foldr xs) ⟩
  foldr _∷_ [] xs ++ ys   ≡⟨ foldr-fusion (_++ ys) [] (λ _ _ → refl) xs ⟩
  foldr _∷_ ([] ++ ys) xs ≡⟨⟩
  foldr _∷_ ys xs         ∎

foldr-++ : ∀ (f : A → B → B) x ys zs →
           foldr f x (ys ++ zs) ≡ foldr f (foldr f x zs) ys
foldr-++ f x []       zs = refl
foldr-++ f x (y ∷ ys) zs = cong (f y) (foldr-++ f x ys zs)

map-is-foldr : {f : A → B} → map f ≗ foldr (λ x ys → f x ∷ ys) []
map-is-foldr {f = f} xs = begin
  map f xs                        ≡⟨ cong (map f) (id-is-foldr xs) ⟩
  map f (foldr _∷_ [] xs)         ≡⟨ foldr-fusion (map f) [] (λ _ _ → refl) xs ⟩
  foldr (λ x ys → f x ∷ ys) [] xs ∎

foldr-∷ʳ : ∀ (f : A → B → B) x y ys →
           foldr f x (ys ∷ʳ y) ≡ foldr f (f y x) ys
foldr-∷ʳ f x y []       = refl
foldr-∷ʳ f x y (z ∷ ys) = cong (f z) (foldr-∷ʳ f x y ys)

foldr-map : ∀ (f : A → B → B) (g : C → A) x xs → foldr f x (map g xs) ≡ foldr (g -⟨ f ∣) x xs
foldr-map f g x []       = refl
foldr-map f g x (y ∷ xs) = cong (f (g y)) (foldr-map f g x xs)

-- Interaction with predicates

module _ {P : Pred A p} {f : A → A → A} where

  foldr-forcesᵇ : (∀ x y → P (f x y) → P x × P y) →
                  ∀ e xs → P (foldr f e xs) → All P xs
  foldr-forcesᵇ _      _ []       _     = []
  foldr-forcesᵇ forces _ (x ∷ xs) Pfold =
    let px , pfxs = forces _ _ Pfold in px ∷ foldr-forcesᵇ forces _ xs pfxs

  foldr-preservesᵇ : (∀ {x y} → P x → P y → P (f x y)) →
                     ∀ {e xs} → P e → All P xs → P (foldr f e xs)
  foldr-preservesᵇ _    Pe []         = Pe
  foldr-preservesᵇ pres Pe (px ∷ pxs) = pres px (foldr-preservesᵇ pres Pe pxs)

  foldr-preservesʳ : (∀ x {y} → P y → P (f x y)) →
                     ∀ {e} → P e → ∀ xs → P (foldr f e xs)
  foldr-preservesʳ pres Pe []       = Pe
  foldr-preservesʳ pres Pe (_ ∷ xs) = pres _ (foldr-preservesʳ pres Pe xs)

  foldr-preservesᵒ : (∀ x y → P x ⊎ P y → P (f x y)) →
                     ∀ e xs → P e ⊎ Any P xs → P (foldr f e xs)
  foldr-preservesᵒ pres e []       (inj₁ Pe)          = Pe
  foldr-preservesᵒ pres e (x ∷ xs) (inj₁ Pe)          =
    pres _ _ (inj₂ (foldr-preservesᵒ pres e xs (inj₁ Pe)))
  foldr-preservesᵒ pres e (x ∷ xs) (inj₂ (here px))   = pres _ _ (inj₁ px)
  foldr-preservesᵒ pres e (x ∷ xs) (inj₂ (there pxs)) =
    pres _ _ (inj₂ (foldr-preservesᵒ pres e xs (inj₂ pxs)))

------------------------------------------------------------------------
-- foldl

foldl-cong : ∀ {f g : B → A → B} → (∀ x y → f x y ≡ g x y) →
             ∀ x → foldl f x ≗ foldl g x
foldl-cong f≗g x []       = refl
foldl-cong f≗g x (y ∷ xs) rewrite f≗g x y = foldl-cong f≗g _ xs

foldl-++ : ∀ (f : A → B → A) x ys zs →
           foldl f x (ys ++ zs) ≡ foldl f (foldl f x ys) zs
foldl-++ f x []       zs = refl
foldl-++ f x (y ∷ ys) zs = foldl-++ f (f x y) ys zs

foldl-∷ʳ : ∀ (f : A → B → A) x y ys →
           foldl f x (ys ∷ʳ y) ≡ f (foldl f x ys) y
foldl-∷ʳ f x y []       = refl
foldl-∷ʳ f x y (z ∷ ys) = foldl-∷ʳ f (f x z) y ys

foldl-map : ∀ (f : A → B → A) (g : C → B) x xs → foldl f x (map g xs) ≡ foldl (∣ f ⟩- g) x xs
foldl-map f g x []       = refl
foldl-map f g x (y ∷ xs) = foldl-map f g (f x (g y)) xs

------------------------------------------------------------------------
-- concat

concat-map : ∀ {f : A → B} → concat ∘ map (map f) ≗ map f ∘ concat
concat-map {f = f} xss = begin
  concat (map (map f) xss)                   ≡⟨ cong concat (map-is-foldr xss) ⟩
  concat (foldr (λ xs → map f xs ∷_) [] xss) ≡⟨ foldr-fusion concat [] (λ _ _ → refl) xss ⟩
  foldr (λ ys → map f ys ++_) [] xss         ≡⟨ sym (foldr-fusion (map f) [] (map-++ f) xss) ⟩
  map f (concat xss)                         ∎

concat-++ : (xss yss : List (List A)) → concat xss ++ concat yss ≡ concat (xss ++ yss)
concat-++ [] yss = refl
concat-++ ([] ∷ xss) yss = concat-++ xss yss
concat-++ ((x ∷ xs) ∷ xss) yss = cong (x ∷_) (concat-++ (xs ∷ xss) yss)

concat-concat : concat {A = A} ∘ map concat ≗ concat ∘ concat
concat-concat [] = refl
concat-concat (xss ∷ xsss) = begin
  concat (map concat (xss ∷ xsss))   ≡⟨ cong (concat xss ++_) (concat-concat xsss) ⟩
  concat xss ++ concat (concat xsss) ≡⟨ concat-++ xss (concat xsss) ⟩
  concat (concat (xss ∷ xsss))       ∎

concat-[-] : concat {A = A} ∘ map [_] ≗ id
concat-[-] [] = refl
concat-[-] (x ∷ xs) = cong (x ∷_) (concat-[-] xs)

------------------------------------------------------------------------
-- concatMap

concatMap-cong : ∀ {f g : A → List B} → f ≗ g → concatMap f ≗ concatMap g
concatMap-cong eq xs = cong concat (map-cong eq xs)

concatMap-pure : concatMap {A = A} [_] ≗ id
concatMap-pure = concat-[-]

concatMap-map : (g : B → List C) → (f : A → B) → (xs : List A) →
                concatMap g (map f xs) ≡ concatMap (g ∘′ f) xs
concatMap-map g f xs
  = cong concat
      {x = map g (map f xs)}
      {y = map (g ∘′ f) xs}
      (sym $ map-∘ xs)

map-concatMap : (f : B → C) (g : A → List B) →
                map f ∘′ concatMap g ≗ concatMap (map f ∘′ g)
map-concatMap f g xs = begin
  map f (concatMap g xs)
    ≡⟨⟩
  map f (concat (map g xs))
    ≡⟨ concat-map (map g xs) ⟨
  concat (map (map f) (map g xs))
    ≡⟨ cong concat
         {x = map (map f) (map g xs)}
         {y = map (map f ∘′ g) xs}
         (sym $ map-∘ xs) ⟩
  concat (map (map f ∘′ g) xs)
    ≡⟨⟩
  concatMap (map f ∘′ g) xs
    ∎

------------------------------------------------------------------------
-- catMaybes

catMaybes-concatMap : catMaybes {A = A} ≗ concatMap fromMaybe
catMaybes-concatMap []             = refl
catMaybes-concatMap (just x  ∷ xs) = cong (x ∷_) $ catMaybes-concatMap xs
catMaybes-concatMap (nothing ∷ xs) = catMaybes-concatMap xs

length-catMaybes : ∀ xs → length (catMaybes {A = A} xs) ≤ length xs
length-catMaybes []             = ≤-refl
length-catMaybes (just _  ∷ xs) = s≤s $ length-catMaybes xs
length-catMaybes (nothing ∷ xs) = m≤n⇒m≤1+n $ length-catMaybes xs

catMaybes-++ : (xs ys : List (Maybe A)) →
               catMaybes (xs ++ ys) ≡ catMaybes xs ++ catMaybes ys
catMaybes-++ []             _  = refl
catMaybes-++ (just x  ∷ xs) ys = cong (x ∷_) $ catMaybes-++ xs ys
catMaybes-++ (nothing ∷ xs) ys = catMaybes-++ xs ys

map-catMaybes : (f : A → B) → map f ∘ catMaybes ≗ catMaybes ∘ map (Maybe.map f)
map-catMaybes _ []             = refl
map-catMaybes f (just x  ∷ xs) = cong (f x ∷_) $ map-catMaybes f xs
map-catMaybes f (nothing ∷ xs) = map-catMaybes f xs

Any-catMaybes⁺ : ∀ {P : Pred A ℓ} {xs : List (Maybe A)} →
                 Any (MAny P) xs → Any P (catMaybes xs)
Any-catMaybes⁺ {xs = nothing ∷ xs} (there x∈)       = Any-catMaybes⁺ x∈
Any-catMaybes⁺ {xs = just x  ∷ xs} (here (just px)) = here px
Any-catMaybes⁺ {xs = just x  ∷ xs} (there x∈)       = there $ Any-catMaybes⁺ x∈

------------------------------------------------------------------------
-- mapMaybe

mapMaybe-cong : {f g : A → Maybe B} → f ≗ g → mapMaybe f ≗ mapMaybe g
mapMaybe-cong f≗g = cong catMaybes ∘ map-cong f≗g

mapMaybe-just : (xs : List A) → mapMaybe just xs ≡ xs
mapMaybe-just []       = refl
mapMaybe-just (x ∷ xs) = cong (x ∷_) (mapMaybe-just xs)

mapMaybe-nothing : (xs : List A) →
                   mapMaybe {B = B} (λ _ → nothing) xs ≡ []
mapMaybe-nothing []       = refl
mapMaybe-nothing (x ∷ xs) = mapMaybe-nothing xs

module _ (f : A → Maybe B) where

  mapMaybe-concatMap : mapMaybe f ≗ concatMap (fromMaybe ∘ f)
  mapMaybe-concatMap xs = begin
    catMaybes (map f xs)            ≡⟨ catMaybes-concatMap (map f xs) ⟩
    concatMap fromMaybe (map f xs)  ≡⟨ concatMap-map fromMaybe f xs ⟩
    concatMap (fromMaybe ∘ f) xs    ∎

  length-mapMaybe : ∀ xs → length (mapMaybe f xs) ≤ length xs
  length-mapMaybe xs = ≤-begin
    length (mapMaybe f xs)      ≤⟨ length-catMaybes (map f xs) ⟩
    length (map f xs)           ≤⟨ ≤-reflexive (length-map f xs) ⟩
    length xs                   ≤-∎
    where open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎)

  mapMaybe-++ : ∀ xs ys →
                mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
  mapMaybe-++ xs ys = begin
    catMaybes (map f (xs ++ ys))     ≡⟨ cong catMaybes (map-++ f xs ys) ⟩
    catMaybes (map f xs ++ map f ys) ≡⟨ catMaybes-++ (map f xs) (map f ys) ⟩
    mapMaybe f xs ++ mapMaybe f ys   ∎

module _ (f : B → Maybe C) (g : A → B) where

  mapMaybe-map : mapMaybe f ∘ map g ≗ mapMaybe (f ∘ g)
  mapMaybe-map = cong catMaybes ∘ sym ∘ map-∘

module _ (g : B → C) (f : A → Maybe B) where

  map-mapMaybe : map g ∘ mapMaybe f ≗ mapMaybe (Maybe.map g ∘ f)
  map-mapMaybe xs = begin
    map g (catMaybes (map f xs))       ≡⟨ map-catMaybes g (map f xs) ⟩
    mapMaybe (Maybe.map g) (map f xs)  ≡⟨ mapMaybe-map _ f xs ⟩
    mapMaybe (Maybe.map g ∘ f) xs      ∎

-- embedding-projection pairs
module _ {proj : B → Maybe A} {emb : A → B} where
  mapMaybe-map-retract : proj ∘ emb ≗ just → mapMaybe proj ∘ map emb ≗ id
  mapMaybe-map-retract retract xs = begin
    mapMaybe proj (map emb xs) ≡⟨ mapMaybe-map _ _ xs ⟩
    mapMaybe (proj ∘ emb) xs   ≡⟨ mapMaybe-cong retract xs ⟩
    mapMaybe just xs           ≡⟨ mapMaybe-just _ ⟩
    xs                         ∎

module _ {proj : C → Maybe B} {emb : A → C} where
  mapMaybe-map-none : proj ∘ emb ≗ const nothing → mapMaybe proj ∘ map emb ≗ const []
  mapMaybe-map-none retract xs = begin
    mapMaybe proj (map emb xs)  ≡⟨ mapMaybe-map _ _ xs ⟩
    mapMaybe (proj ∘ emb) xs    ≡⟨ mapMaybe-cong retract xs ⟩
    mapMaybe (const nothing) xs ≡⟨ mapMaybe-nothing xs ⟩
    []                          ∎

-- embedding-projection pairs on sums
mapMaybeIsInj₁∘mapInj₁ : (xs : List A) → mapMaybe (isInj₁ {B = B}) (map inj₁ xs) ≡ xs
mapMaybeIsInj₁∘mapInj₁ = mapMaybe-map-retract λ _ → refl

mapMaybeIsInj₁∘mapInj₂ : (xs : List B) → mapMaybe (isInj₁ {A = A}) (map inj₂ xs) ≡ []
mapMaybeIsInj₁∘mapInj₂ = mapMaybe-map-none λ _ → refl

mapMaybeIsInj₂∘mapInj₂ : (xs : List B) → mapMaybe (isInj₂ {A = A}) (map inj₂ xs) ≡ xs
mapMaybeIsInj₂∘mapInj₂ = mapMaybe-map-retract λ _ → refl

mapMaybeIsInj₂∘mapInj₁ : (xs : List A) → mapMaybe (isInj₂ {B = B}) (map inj₁ xs) ≡ []
mapMaybeIsInj₂∘mapInj₁ = mapMaybe-map-none λ _ → refl

------------------------------------------------------------------------
-- sum

sum-++ : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++ []       ys = refl
sum-++ (x ∷ xs) ys = begin
  x + sum (xs ++ ys)     ≡⟨ cong (x +_) (sum-++ xs ys) ⟩
  x + (sum xs + sum ys)  ≡⟨ sym (+-assoc x _ _) ⟩
  (x + sum xs) + sum ys  ∎

------------------------------------------------------------------------
-- product

∈⇒∣product : ∀ {n ns} → n ∈ ns → n ∣ product ns
∈⇒∣product {n} {n ∷ ns} (here  refl) = divides (product ns) (*-comm n (product ns))
∈⇒∣product {n} {m ∷ ns} (there n∈ns) = ∣n⇒∣m*n m (∈⇒∣product n∈ns)

------------------------------------------------------------------------
-- applyUpTo

length-applyUpTo : ∀ (f : ℕ → A) n → length (applyUpTo f n) ≡ n
length-applyUpTo f zero    = refl
length-applyUpTo f (suc n) = cong suc (length-applyUpTo (f ∘ suc) n)

lookup-applyUpTo : ∀ (f : ℕ → A) n i → lookup (applyUpTo f n) i ≡ f (toℕ i)
lookup-applyUpTo f (suc n) zero    = refl
lookup-applyUpTo f (suc n) (suc i) = lookup-applyUpTo (f ∘ suc) n i

applyUpTo-∷ʳ : ∀ (f : ℕ → A) n → applyUpTo f n ∷ʳ f n ≡ applyUpTo f (suc n)
applyUpTo-∷ʳ f zero = refl
applyUpTo-∷ʳ f (suc n) = cong (f 0 ∷_) (applyUpTo-∷ʳ (f ∘ suc) n)

------------------------------------------------------------------------
-- applyDownFrom

module _ (f : ℕ → A) where

  length-applyDownFrom : ∀ n → length (applyDownFrom f n) ≡ n
  length-applyDownFrom zero    = refl
  length-applyDownFrom (suc n) = cong suc (length-applyDownFrom n)

  lookup-applyDownFrom : ∀ n i → lookup (applyDownFrom f n) i ≡ f (n ∸ (suc (toℕ i)))
  lookup-applyDownFrom (suc n) zero    = refl
  lookup-applyDownFrom (suc n) (suc i) = lookup-applyDownFrom n i

  applyDownFrom-∷ʳ : ∀ n → applyDownFrom (f ∘ suc) n ∷ʳ f 0 ≡ applyDownFrom f (suc n)
  applyDownFrom-∷ʳ zero = refl
  applyDownFrom-∷ʳ (suc n) = cong (f (suc n) ∷_) (applyDownFrom-∷ʳ n)

------------------------------------------------------------------------
-- upTo

length-upTo : ∀ n → length (upTo n) ≡ n
length-upTo = length-applyUpTo id

lookup-upTo : ∀ n i → lookup (upTo n) i ≡ toℕ i
lookup-upTo = lookup-applyUpTo id

upTo-∷ʳ : ∀ n → upTo n ∷ʳ n ≡ upTo (suc n)
upTo-∷ʳ = applyUpTo-∷ʳ id

------------------------------------------------------------------------
-- downFrom

length-downFrom : ∀ n → length (downFrom n) ≡ n
length-downFrom = length-applyDownFrom id

lookup-downFrom : ∀ n i → lookup (downFrom n) i ≡ n ∸ (suc (toℕ i))
lookup-downFrom = lookup-applyDownFrom id

downFrom-∷ʳ : ∀ n → applyDownFrom suc n ∷ʳ 0 ≡ downFrom (suc n)
downFrom-∷ʳ = applyDownFrom-∷ʳ id

------------------------------------------------------------------------
-- tabulate

tabulate-cong : ∀ {n} {f g : Fin n → A} →
                f ≗ g → tabulate f ≡ tabulate g
tabulate-cong {n = zero}  p = refl
tabulate-cong {n = suc n} p = cong₂ _∷_ (p zero) (tabulate-cong (p ∘ suc))

tabulate-lookup : ∀ (xs : List A) → tabulate (lookup xs) ≡ xs
tabulate-lookup []       = refl
tabulate-lookup (x ∷ xs) = cong (_ ∷_) (tabulate-lookup xs)

length-tabulate : ∀ {n} → (f : Fin n → A) →
                  length (tabulate f) ≡ n
length-tabulate {n = zero} f = refl
length-tabulate {n = suc n} f = cong suc (length-tabulate (λ z → f (suc z)))

lookup-tabulate : ∀ {n} → (f : Fin n → A) →
                  ∀ i → let i′ = cast (sym (length-tabulate f)) i
                        in lookup (tabulate f) i′ ≡ f i
lookup-tabulate f zero    = refl
lookup-tabulate f (suc i) = lookup-tabulate (f ∘ suc) i

map-tabulate : ∀ {n} (g : Fin n → A) (f : A → B) →
               map f (tabulate g) ≡ tabulate (f ∘ g)
map-tabulate {n = zero}  g f = refl
map-tabulate {n = suc n} g f = cong (_ ∷_) (map-tabulate (g ∘ suc) f)

------------------------------------------------------------------------
-- _[_]%=_

length-%= : ∀ xs k (f : A → A) → length (xs [ k ]%= f) ≡ length xs
length-%= (x ∷ xs) zero    f = refl
length-%= (x ∷ xs) (suc k) f = cong suc (length-%= xs k f)

------------------------------------------------------------------------
-- _[_]∷=_

length-∷= : ∀ xs k (v : A) → length (xs [ k ]∷= v) ≡ length xs
length-∷= xs k v = length-%= xs k (const v)

map-∷= : ∀ xs k (v : A) (f : A → B) →
         let eq = sym (length-map f xs) in
         map f (xs [ k ]∷= v) ≡ map f xs [ cast eq k ]∷= f v
map-∷= (x ∷ xs) zero    v f = refl
map-∷= (x ∷ xs) (suc k) v f = cong (f x ∷_) (map-∷= xs k v f)

------------------------------------------------------------------------
-- insertAt

length-insertAt : ∀ (xs : List A) (i : Fin (suc (length xs))) v →
                  length (insertAt xs i v) ≡ suc (length xs)
length-insertAt xs       zero    v = refl
length-insertAt (x ∷ xs) (suc i) v = cong suc (length-insertAt xs i v)

------------------------------------------------------------------------
-- removeAt

length-removeAt : ∀ (xs : List A) k → length (removeAt xs k) ≡ pred (length xs)
length-removeAt (x ∷ xs) zero            = refl
length-removeAt (x ∷ xs@(_ ∷ _)) (suc k) = cong suc (length-removeAt xs k)

length-removeAt′ : ∀ (xs : List A) k → length xs ≡ suc (length (removeAt xs k))
length-removeAt′ xs@(_ ∷ _) k rewrite length-removeAt xs k = refl

map-removeAt : ∀ xs k (f : A → B) →
            let eq = sym (length-map f xs) in
            map f (removeAt xs k) ≡ removeAt (map f xs) (cast eq k)
map-removeAt (x ∷ xs) zero    f = refl
map-removeAt (x ∷ xs) (suc k) f = cong (f x ∷_) (map-removeAt xs k f)

------------------------------------------------------------------------
 -- insertAt and removeAt

removeAt-insertAt : ∀ (xs : List A) (i : Fin (suc (length xs))) v →
  removeAt (insertAt xs i v) ((cast (sym (length-insertAt xs i v)) i)) ≡ xs
removeAt-insertAt xs       zero    v = refl
removeAt-insertAt (x ∷ xs) (suc i) v = cong (_ ∷_) (removeAt-insertAt xs i v)

insertAt-removeAt : (xs : List A) (i : Fin (length xs)) →
  insertAt (removeAt xs i) (cast (length-removeAt′ xs i) i) (lookup xs i) ≡ xs
insertAt-removeAt (x ∷ xs) zero    = refl
insertAt-removeAt (x ∷ xs) (suc i) = cong (x ∷_) (insertAt-removeAt xs i)

------------------------------------------------------------------------
-- take

length-take : ∀ n (xs : List A) → length (take n xs) ≡ n ⊓ (length xs)
length-take zero    xs       = refl
length-take (suc n) []       = refl
length-take (suc n) (x ∷ xs) = cong suc (length-take n xs)

-- Take commutes with map.
take-map : ∀ {f : A → B} (n : ℕ) xs → take n (map f xs) ≡ map f (take n xs)
take-map zero xs = refl
take-map (suc s) [] = refl
take-map (suc s) (a ∷ xs) = cong (_ ∷_) (take-map s xs)

take-suc : (xs : List A) (i : Fin (length xs)) → let m = toℕ i in
           take (suc m) xs ≡ take m xs ∷ʳ lookup xs i
take-suc (x ∷ xs) zero    = refl
take-suc (x ∷ xs) (suc i) = cong (x ∷_) (take-suc xs i)

take-suc-tabulate : ∀ {n} (f : Fin n → A) (i : Fin n) → let m = toℕ i in
                    take (suc m) (tabulate f) ≡ take m (tabulate f) ∷ʳ f i
take-suc-tabulate f i rewrite sym (toℕ-cast (sym (length-tabulate f)) i) | sym (lookup-tabulate f i)
  = take-suc (tabulate f) (cast _ i)

-- If you take at least as many elements from a list as it has, you get
-- the whole list.
take-all : (n : ℕ) (xs : List A) → n ≥ length xs → take n xs ≡ xs
take-all zero [] _ = refl
take-all (suc _) [] _ = refl
take-all (suc n) (x ∷ xs) (s≤s pf) = cong (x ∷_) (take-all n xs pf)

-- Taking from an empty list does nothing.
take-[] : ∀ m → take {A = A} m [] ≡ []
take-[] zero = refl
take-[] (suc m) = refl

-- Taking twice takes the minimum of both counts.
take-take : ∀ n m (xs : List A) → take n (take m xs) ≡ take (n ⊓ m) xs
take-take zero    m       xs       = refl
take-take (suc n) zero    xs       = refl
take-take (suc n) (suc m) []       = refl
take-take (suc n) (suc m) (x ∷ xs) = cong (x ∷_) (take-take n m xs)

-- Dropping m elements and then taking n is the same as
-- taking n + m elements and then dropping m.
take-drop : ∀ n m (xs : List A) →
            take n (drop m xs) ≡ drop m (take (m + n) xs)
take-drop n zero    xs       = refl
take-drop n (suc m) []       = take-[] n
take-drop n (suc m) (x ∷ xs) = take-drop n m xs

------------------------------------------------------------------------
-- drop

length-drop : ∀ n (xs : List A) → length (drop n xs) ≡ length xs ∸ n
length-drop zero    xs       = refl
length-drop (suc n) []       = refl
length-drop (suc n) (x ∷ xs) = length-drop n xs

-- Drop commutes with map.
drop-map : ∀ {f : A → B} (n : ℕ) xs → drop n (map f xs) ≡ map f (drop n xs)
drop-map zero xs = refl
drop-map (suc n) [] = refl
drop-map (suc n) (a ∷ xs) = drop-map n xs

-- Dropping from an empty list does nothing.
drop-[] : ∀ m → drop {A = A} m [] ≡ []
drop-[] zero = refl
drop-[] (suc m) = refl

take++drop≡id : ∀ n (xs : List A) → take n xs ++ drop n xs ≡ xs
take++drop≡id zero    xs       = refl
take++drop≡id (suc n) []       = refl
take++drop≡id (suc n) (x ∷ xs) = cong (x ∷_) (take++drop≡id n xs)

drop-take-suc : (xs : List A) (i : Fin (length xs)) → let m = toℕ i in
           drop m (take (suc m) xs) ≡ [ lookup xs i ]
drop-take-suc (x ∷ xs) zero    = refl
drop-take-suc (x ∷ xs) (suc i) = drop-take-suc xs i

drop-take-suc-tabulate : ∀ {n} (f : Fin n → A) (i : Fin n) → let m = toℕ i in
                  drop m (take (suc m) (tabulate f)) ≡ [ f i ]
drop-take-suc-tabulate f i rewrite sym (toℕ-cast (sym (length-tabulate f)) i) | sym (lookup-tabulate f i)
  = drop-take-suc (tabulate f) (cast _ i)

-- Dropping m elements and then n elements is same as dropping m+n elements
drop-drop : (m n : ℕ) → (xs : List A) → drop n (drop m xs) ≡ drop (m + n) xs
drop-drop zero n xs = refl
drop-drop (suc m) n [] = drop-[] n
drop-drop (suc m) n (x ∷ xs) = drop-drop m n xs

drop-all : (n : ℕ) (xs : List A) → n ≥ length xs → drop n xs ≡ []
drop-all n       []       _ = drop-[] n
drop-all (suc n) (x ∷ xs) p = drop-all n xs (s≤s⁻¹ p)

------------------------------------------------------------------------
-- replicate

length-replicate : ∀ n {x : A} → length (replicate n x) ≡ n
length-replicate zero    = refl
length-replicate (suc n) = cong suc (length-replicate n)

lookup-replicate : ∀ n (x : A) (i : Fin n) →
                   lookup (replicate n x) (cast (sym (length-replicate n)) i) ≡ x
lookup-replicate (suc n) x zero    = refl
lookup-replicate (suc n) x (suc i) = lookup-replicate n x i

map-replicate :  ∀ (f : A → B) n (x : A) →
                 map f (replicate n x) ≡ replicate n (f x)
map-replicate f zero    x = refl
map-replicate f (suc n) x = cong (_ ∷_) (map-replicate f n x)

zipWith-replicate : ∀ n (_⊕_ : A → B → C) (x : A) (y : B) →
                    zipWith _⊕_ (replicate n x) (replicate n y) ≡ replicate n (x ⊕ y)
zipWith-replicate zero    _⊕_ x y = refl
zipWith-replicate (suc n) _⊕_ x y = cong (x ⊕ y ∷_) (zipWith-replicate n _⊕_ x y)

------------------------------------------------------------------------
-- iterate

length-iterate : ∀ f (x : A) n → length (iterate f x n) ≡ n
length-iterate f x zero    = refl
length-iterate f x (suc n) = cong suc (length-iterate f (f x) n)

iterate-id : ∀ (x : A) n → iterate id x n ≡ replicate n x
iterate-id x zero    = refl
iterate-id x (suc n) = cong (_ ∷_) (iterate-id x n)

lookup-iterate : ∀ f (x : A) n (i : Fin n) →
  lookup (iterate f x n) (cast (sym (length-iterate f x n)) i) ≡ ℕ.iterate f x (toℕ i)
lookup-iterate f x (suc n) zero    = refl
lookup-iterate f x (suc n) (suc i) = lookup-iterate f (f x) n i

------------------------------------------------------------------------
-- splitAt

splitAt-defn : ∀ n → splitAt {A = A} n ≗ < take n , drop n >
splitAt-defn zero    xs       = refl
splitAt-defn (suc n) []       = refl
splitAt-defn (suc n) (x ∷ xs) = cong (Product.map (x ∷_) id) (splitAt-defn n xs)

module _ (f : A → B) where

  splitAt-map : ∀ n → splitAt n ∘ map f ≗
                      Product.map (map f) (map f) ∘ splitAt n
  splitAt-map zero    xs       = refl
  splitAt-map (suc n) []       = refl
  splitAt-map (suc n) (x ∷ xs) =
    cong (Product.map₁ (f x ∷_)) (splitAt-map n xs)

------------------------------------------------------------------------
-- takeWhile, dropWhile, and span

module _ {P : Pred A p} (P? : Decidable P) where

  takeWhile++dropWhile : ∀ xs → takeWhile P? xs ++ dropWhile P? xs ≡ xs
  takeWhile++dropWhile []       = refl
  takeWhile++dropWhile (x ∷ xs) with does (P? x)
  ... | true  = cong (x ∷_) (takeWhile++dropWhile xs)
  ... | false = refl

  span-defn : span P? ≗ < takeWhile P? , dropWhile P? >
  span-defn []       = refl
  span-defn (x ∷ xs) with does (P? x)
  ... | true  = cong (Product.map (x ∷_) id) (span-defn xs)
  ... | false = refl

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : Decidable P) where

  length-filter : ∀ xs → length (filter P? xs) ≤ length xs
  length-filter []       = z≤n
  length-filter (x ∷ xs) with ih ← length-filter xs | does (P? x)
  ... | false = m≤n⇒m≤1+n ih
  ... | true  = s≤s ih

  filter-all : ∀ {xs} → All P xs → filter P? xs ≡ xs
  filter-all {[]}     []         = refl
  filter-all {x ∷ xs} (px ∷ pxs) with P? x
  ... | no          ¬px = contradiction px ¬px
  ... | true  because _ = cong (x ∷_) (filter-all pxs)

  filter-notAll : ∀ xs → Any (∁ P) xs → length (filter P? xs) < length xs
  filter-notAll (x ∷ xs) (here ¬px) with P? x
  ... | false because _ = s≤s (length-filter xs)
  ... | yes          px = contradiction px ¬px
  filter-notAll (x ∷ xs) (there any) with ih ← filter-notAll xs any | does (P? x)
  ... | false = m≤n⇒m≤1+n ih
  ... | true  = s≤s ih

  filter-some : ∀ {xs} → Any P xs → 0 < length (filter P? xs)
  filter-some {x ∷ xs} (here px)   with P? x
  ... | true because _ = z<s
  ... | no         ¬px = contradiction px ¬px
  filter-some {x ∷ xs} (there pxs) with does (P? x)
  ... | true  = m≤n⇒m≤1+n (filter-some pxs)
  ... | false = filter-some pxs

  filter-none : ∀ {xs} → All (∁ P) xs → filter P? xs ≡ []
  filter-none {[]}     []           = refl
  filter-none {x ∷ xs} (¬px ∷ ¬pxs) with P? x
  ... | false because _ = filter-none ¬pxs
  ... | yes          px = contradiction px ¬px

  filter-complete : ∀ {xs} → length (filter P? xs) ≡ length xs →
                    filter P? xs ≡ xs
  filter-complete {[]}     eq = refl
  filter-complete {x ∷ xs} eq with does (P? x)
  ... | false = contradiction eq (<⇒≢ (s≤s (length-filter xs)))
  ... | true  = cong (x ∷_) (filter-complete (suc-injective eq))

  filter-accept : ∀ {x xs} → P x → filter P? (x ∷ xs) ≡ x ∷ (filter P? xs)
  filter-accept {x} Px with P? x
  ... | true because _ = refl
  ... | no         ¬Px = contradiction Px ¬Px

  filter-reject : ∀ {x xs} → ¬ P x → filter P? (x ∷ xs) ≡ filter P? xs
  filter-reject {x} ¬Px with P? x
  ... | yes          Px = contradiction Px ¬Px
  ... | false because _ = refl

  filter-idem : filter P? ∘ filter P? ≗ filter P?
  filter-idem []       = refl
  filter-idem (x ∷ xs) with does (P? x) in eq
  ... | false            = filter-idem xs
  ... | true  rewrite eq = cong (x ∷_) (filter-idem xs)

  filter-++ : ∀ xs ys → filter P? (xs ++ ys) ≡ filter P? xs ++ filter P? ys
  filter-++ []       ys = refl
  filter-++ (x ∷ xs) ys with ih ← filter-++ xs ys | does (P? x)
  ... | true  = cong (x ∷_) ih
  ... | false = ih

------------------------------------------------------------------------
-- derun and deduplicate

module _ {R : Rel A p} (R? : B.Decidable R) where

  length-derun : ∀ xs → length (derun R? xs) ≤ length xs
  length-derun [] = ≤-refl
  length-derun (x ∷ []) = ≤-refl
  length-derun (x ∷ y ∷ xs) with ih ← length-derun (y ∷ xs) | does (R? x y)
  ... | true  = m≤n⇒m≤1+n ih
  ... | false = s≤s ih

  length-deduplicate : ∀ xs → length (deduplicate R? xs) ≤ length xs
  length-deduplicate [] = z≤n
  length-deduplicate (x ∷ xs) = ≤-begin
    1 + length (filter (¬? ∘ R? x) r) ≤⟨ s≤s (length-filter (¬? ∘ R? x) r) ⟩
    1 + length r                      ≤⟨ s≤s (length-deduplicate xs) ⟩
    1 + length xs                     ≤-∎
    where
    open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎)
    r = deduplicate R? xs

  derun-reject : ∀ {x y} xs → R x y → derun R? (x ∷ y ∷ xs) ≡ derun R? (y ∷ xs)
  derun-reject {x} {y} xs Rxy with R? x y
  ... | yes _    = refl
  ... | no  ¬Rxy = contradiction Rxy ¬Rxy

  derun-accept : ∀ {x y} xs → ¬ R x y → derun R? (x ∷ y ∷ xs) ≡ x ∷ derun R? (y ∷ xs)
  derun-accept {x} {y} xs ¬Rxy with R? x y
  ... | yes Rxy = contradiction Rxy ¬Rxy
  ... | no  _   = refl

------------------------------------------------------------------------
-- partition

module _ {P : Pred A p} (P? : Decidable P) where

  partition-defn : partition P? ≗ < filter P? , filter (∁? P?) >
  partition-defn []       = refl
  partition-defn (x ∷ xs) with ih ← partition-defn xs | does (P? x)
  ...  | true  = cong (Product.map (x ∷_) id) ih
  ...  | false = cong (Product.map id (x ∷_)) ih

  length-partition : ∀ xs → (let (ys , zs) = partition P? xs) →
                     length ys ≤ length xs × length zs ≤ length xs
  length-partition []       = z≤n , z≤n
  length-partition (x ∷ xs) with ih ← length-partition xs | does (P? x)
  ...  | true  = Product.map s≤s m≤n⇒m≤1+n ih
  ...  | false = Product.map m≤n⇒m≤1+n s≤s ih

------------------------------------------------------------------------
-- _ʳ++_

ʳ++-defn : ∀ (xs : List A) {ys} → xs ʳ++ ys ≡ reverse xs ++ ys
ʳ++-defn [] = refl
ʳ++-defn (x ∷ xs) {ys} = begin
  (x ∷ xs)             ʳ++ ys   ≡⟨⟩
  xs         ʳ++   x     ∷ ys   ≡⟨⟩
  xs         ʳ++ [ x ]  ++ ys   ≡⟨ ʳ++-defn xs  ⟩
  reverse xs  ++ [ x ]  ++ ys   ≡⟨ sym (++-assoc (reverse xs) _ _) ⟩
  (reverse xs ++ [ x ]) ++ ys   ≡⟨ cong (_++ ys) (sym (ʳ++-defn xs)) ⟩
  (xs ʳ++ [ x ])        ++ ys   ≡⟨⟩
  reverse (x ∷ xs)      ++ ys   ∎

-- Reverse-append of append is reverse-append after reverse-append.

++-ʳ++ : ∀ (xs {ys zs} : List A) → (xs ++ ys) ʳ++ zs ≡ ys ʳ++ xs ʳ++ zs
++-ʳ++ [] = refl
++-ʳ++ (x ∷ xs) {ys} {zs} = begin
  (x ∷ xs ++ ys) ʳ++ zs   ≡⟨⟩
  (xs ++ ys) ʳ++ x ∷ zs   ≡⟨ ++-ʳ++ xs ⟩
  ys ʳ++ xs ʳ++ x ∷ zs    ≡⟨⟩
  ys ʳ++ (x ∷ xs) ʳ++ zs  ∎

-- Reverse-append of reverse-append is commuted reverse-append after append.

ʳ++-ʳ++ : ∀ (xs {ys zs} : List A) → (xs ʳ++ ys) ʳ++ zs ≡ ys ʳ++ xs ++ zs
ʳ++-ʳ++ [] = refl
ʳ++-ʳ++ (x ∷ xs) {ys} {zs} = begin
  ((x ∷ xs) ʳ++ ys) ʳ++ zs   ≡⟨⟩
  (xs ʳ++ x ∷ ys) ʳ++ zs     ≡⟨ ʳ++-ʳ++ xs ⟩
  (x ∷ ys) ʳ++ xs ++ zs      ≡⟨⟩
  ys ʳ++ (x ∷ xs) ++ zs      ∎

-- Length of reverse-append

length-ʳ++ : ∀ (xs {ys} : List A) →
             length (xs ʳ++ ys) ≡ length xs + length ys
length-ʳ++ [] = refl
length-ʳ++ (x ∷ xs) {ys} = begin
  length ((x ∷ xs) ʳ++ ys)      ≡⟨⟩
  length (xs ʳ++ x ∷ ys)        ≡⟨ length-ʳ++ xs ⟩
  length xs + length (x ∷ ys)   ≡⟨ +-suc _ _ ⟩
  length (x ∷ xs) + length ys   ∎

-- map distributes over reverse-append.

map-ʳ++ : (f : A → B) (xs {ys} : List A) →
          map f (xs ʳ++ ys) ≡ map f xs ʳ++ map f ys
map-ʳ++ f []            = refl
map-ʳ++ f (x ∷ xs) {ys} = begin
  map f ((x ∷ xs) ʳ++ ys)         ≡⟨⟩
  map f (xs ʳ++ x ∷ ys)           ≡⟨ map-ʳ++ f xs ⟩
  map f xs ʳ++ map f (x ∷ ys)     ≡⟨⟩
  map f xs ʳ++ f x ∷ map f ys     ≡⟨⟩
  (f x ∷ map f xs) ʳ++ map f ys   ≡⟨⟩
  map f (x ∷ xs)   ʳ++ map f ys   ∎

-- A foldr after a reverse is a foldl.

foldr-ʳ++ : ∀ (f : A → B → B) b xs {ys} →
            foldr f b (xs ʳ++ ys) ≡ foldl (flip f) (foldr f b ys) xs
foldr-ʳ++ f b []       {_}  = refl
foldr-ʳ++ f b (x ∷ xs) {ys} = begin
  foldr f b ((x ∷ xs) ʳ++ ys)              ≡⟨⟩
  foldr f b (xs ʳ++ x ∷ ys)                ≡⟨ foldr-ʳ++ f b xs ⟩
  foldl (flip f) (foldr f b (x ∷ ys)) xs   ≡⟨⟩
  foldl (flip f) (f x (foldr f b ys)) xs   ≡⟨⟩
  foldl (flip f) (foldr f b ys) (x ∷ xs)   ∎

-- A foldl after a reverse is a foldr.

foldl-ʳ++ : ∀ (f : B → A → B) b xs {ys} →
            foldl f b (xs ʳ++ ys) ≡ foldl f (foldr (flip f) b xs) ys
foldl-ʳ++ f b []       {_}  = refl
foldl-ʳ++ f b (x ∷ xs) {ys} = begin
  foldl f b ((x ∷ xs) ʳ++ ys)              ≡⟨⟩
  foldl f b (xs ʳ++ x ∷ ys)                ≡⟨ foldl-ʳ++ f b xs ⟩
  foldl f (foldr (flip f) b xs) (x ∷ ys)   ≡⟨⟩
  foldl f (f (foldr (flip f) b xs) x) ys   ≡⟨⟩
  foldl f (foldr (flip f) b (x ∷ xs)) ys   ∎

------------------------------------------------------------------------
-- reverse

-- reverse of cons is snoc of reverse.

unfold-reverse : ∀ (x : A) xs → reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
unfold-reverse x xs = ʳ++-defn xs

-- reverse is an anti-homomorphism with respect to append.

reverse-++ : (xs ys : List A) →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ xs ys = begin
  reverse (xs ++ ys)         ≡⟨⟩
  (xs ++ ys) ʳ++ []          ≡⟨ ++-ʳ++ xs ⟩
  ys ʳ++ xs ʳ++ []           ≡⟨⟩
  ys ʳ++ reverse xs          ≡⟨ ʳ++-defn ys ⟩
  reverse ys ++ reverse xs   ∎

-- reverse is self-inverse.

reverse-selfInverse : SelfInverse {A = List A} _≡_ reverse
reverse-selfInverse {x = xs} {y = ys} xs⁻¹≈ys = begin
  reverse ys         ≡⟨⟩
  ys ʳ++ []          ≡⟨ cong (_ʳ++ []) xs⁻¹≈ys ⟨
  reverse xs ʳ++ []  ≡⟨⟩
  (xs ʳ++ []) ʳ++ [] ≡⟨ ʳ++-ʳ++ xs ⟩
  [] ʳ++ xs ++ []    ≡⟨⟩
  xs ++ []           ≡⟨ ++-identityʳ xs ⟩
  xs                 ∎

-- reverse is involutive.

reverse-involutive : Involutive {A = List A} _≡_ reverse
reverse-involutive = selfInverse⇒involutive reverse-selfInverse

-- reverse is injective.

reverse-injective : Injective {A = List A} _≡_ _≡_ reverse
reverse-injective = selfInverse⇒injective reverse-selfInverse

-- reverse preserves length.

length-reverse : ∀ (xs : List A) → length (reverse xs) ≡ length xs
length-reverse xs = begin
  length (reverse xs)   ≡⟨⟩
  length (xs ʳ++ [])    ≡⟨ length-ʳ++ xs ⟩
  length xs + 0         ≡⟨ +-identityʳ _ ⟩
  length xs             ∎

reverse-map : (f : A → B) → map f ∘ reverse ≗ reverse ∘ map f
reverse-map f xs = begin
  map f (reverse xs) ≡⟨⟩
  map f (xs ʳ++ [])  ≡⟨ map-ʳ++ f xs ⟩
  map f xs ʳ++ []    ≡⟨⟩
  reverse (map f xs) ∎

reverse-foldr : ∀ (f : A → B → B) b →
                foldr f b ∘ reverse ≗ foldl (flip f) b
reverse-foldr f b xs = foldr-ʳ++ f b xs

reverse-foldl : ∀ (f : B → A → B) b xs →
                foldl f b (reverse xs) ≡ foldr (flip f) b xs
reverse-foldl f b xs = foldl-ʳ++ f b xs

------------------------------------------------------------------------
-- reverse, applyUpTo, and applyDownFrom

reverse-applyUpTo : ∀ (f : ℕ → A) n → reverse (applyUpTo f n) ≡ applyDownFrom f n
reverse-applyUpTo f zero = refl
reverse-applyUpTo f (suc n) = begin
  reverse (f 0 ∷ applyUpTo (f ∘ suc) n)  ≡⟨ reverse-++ [ f 0 ] (applyUpTo (f ∘ suc) n) ⟩
  reverse (applyUpTo (f ∘ suc) n) ∷ʳ f 0 ≡⟨ cong (_∷ʳ f 0) (reverse-applyUpTo (f ∘ suc) n) ⟩
  applyDownFrom (f ∘ suc) n ∷ʳ f 0       ≡⟨ applyDownFrom-∷ʳ f n ⟩
  applyDownFrom f (suc n)                ∎

reverse-upTo : ∀ n → reverse (upTo n) ≡ downFrom n
reverse-upTo = reverse-applyUpTo id

reverse-applyDownFrom : ∀ (f : ℕ → A) n → reverse (applyDownFrom f n) ≡ applyUpTo f n
reverse-applyDownFrom f zero = refl
reverse-applyDownFrom f (suc n) = begin
  reverse (f n ∷ applyDownFrom f n)  ≡⟨ reverse-++ [ f n ] (applyDownFrom f n) ⟩
  reverse (applyDownFrom f n) ∷ʳ f n ≡⟨ cong (_∷ʳ f n) (reverse-applyDownFrom f n) ⟩
  applyUpTo f n ∷ʳ f n               ≡⟨ applyUpTo-∷ʳ f n ⟩
  applyUpTo f (suc n)                ∎

reverse-downFrom : ∀ n → reverse (downFrom n) ≡ upTo n
reverse-downFrom = reverse-applyDownFrom id

------------------------------------------------------------------------
-- _∷ʳ_

∷ʳ-injective : ∀ xs ys → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
∷ʳ-injective []          []          refl = refl , refl
∷ʳ-injective (x ∷ xs)    (y  ∷ ys)   eq   with refl , eq′  ← ∷-injective eq
  = Product.map (cong (x ∷_)) id (∷ʳ-injective xs ys eq′)
∷ʳ-injective []          (_ ∷ _ ∷ _) ()
∷ʳ-injective (_ ∷ _ ∷ _) []          ()

∷ʳ-injectiveˡ : ∀ xs ys → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
∷ʳ-injectiveˡ xs ys eq = proj₁ (∷ʳ-injective xs ys eq)

∷ʳ-injectiveʳ : ∀ xs ys → xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y
∷ʳ-injectiveʳ xs ys eq = proj₂ (∷ʳ-injective xs ys eq)

∷ʳ-++ : ∀ xs (a : A) ys → xs ∷ʳ a ++ ys ≡ xs ++ a ∷ ys
∷ʳ-++ xs a ys = ++-assoc xs [ a ] ys

------------------------------------------------------------------------
-- uncons

module _ (f : A → B) where

  -- 'commute' List.uncons and List.map to obtain a Maybe.map and List.uncons.
  uncons-map : uncons ∘ map f ≗ Maybe.map (Product.map f (map f)) ∘ uncons
  uncons-map []       = refl
  uncons-map (x ∷ xs) = refl

------------------------------------------------------------------------
-- head

module _ {f : A → B} where

  -- 'commute' List.head and List.map to obtain a Maybe.map and List.head.
  head-map : head ∘ map f ≗ Maybe.map f ∘ head
  head-map []      = refl
  head-map (_ ∷ _) = refl

------------------------------------------------------------------------
-- last

module _ (f : A → B) where

  -- 'commute' List.last and List.map to obtain a Maybe.map and List.last.
  last-map : last ∘ map f ≗ Maybe.map f ∘ last
  last-map []               = refl
  last-map (x ∷ [])         = refl
  last-map (x ∷ xs@(_ ∷ _)) = last-map xs

------------------------------------------------------------------------
-- tail

module _ (f : A → B) where

  -- 'commute' List.tail and List.map to obtain a Maybe.map and List.tail.
  tail-map : tail ∘ map f ≗ Maybe.map (map f) ∘ tail
  tail-map []       = refl
  tail-map (x ∷ xs) = refl




------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-id₂ = map-id-local
{-# WARNING_ON_USAGE map-id₂
"Warning: map-id₂ was deprecated in v2.0.
Please use map-id-local instead."
#-}

map-cong₂ = map-cong-local
{-# WARNING_ON_USAGE map-id₂
"Warning: map-cong₂ was deprecated in v2.0.
Please use map-cong-local instead."
#-}

map-compose = map-∘
{-# WARNING_ON_USAGE map-compose
"Warning: map-compose was deprecated in v2.0.
Please use map-∘ instead."
#-}

map-++-commute = map-++
{-# WARNING_ON_USAGE map-++-commute
"Warning: map-++-commute was deprecated in v2.0.
Please use map-++ instead."
#-}

sum-++-commute = sum-++
{-# WARNING_ON_USAGE sum-++-commute
"Warning: map-++-commute was deprecated in v2.0.
Please use map-++ instead."
#-}

reverse-map-commute = reverse-map
{-# WARNING_ON_USAGE reverse-map-commute
"Warning: reverse-map-commute was deprecated in v2.0.
Please use reverse-map instead."
#-}

reverse-++-commute = reverse-++
{-# WARNING_ON_USAGE reverse-++-commute
"Warning: reverse-++-commute was deprecated in v2.0.
Please use reverse-++ instead."
#-}

zipWith-identityˡ = zipWith-zeroˡ
{-# WARNING_ON_USAGE zipWith-identityˡ
"Warning: zipWith-identityˡ was deprecated in v2.0.
Please use zipWith-zeroˡ instead."
#-}

zipWith-identityʳ = zipWith-zeroʳ
{-# WARNING_ON_USAGE zipWith-identityʳ
"Warning: zipWith-identityʳ was deprecated in v2.0.
Please use zipWith-zeroʳ instead."
#-}

ʳ++-++ = ++-ʳ++
{-# WARNING_ON_USAGE ʳ++-++
"Warning: ʳ++-++ was deprecated in v2.0.
Please use ++-ʳ++ instead."
#-}

take++drop = take++drop≡id
{-# WARNING_ON_USAGE take++drop
"Warning: take++drop was deprecated in v2.0.
Please use take++drop≡id instead."
#-}

length-─ = length-removeAt
{-# WARNING_ON_USAGE length-─
"Warning: length-─ was deprecated in v2.0.
Please use length-removeAt instead."
#-}

map-─ = map-removeAt
{-# WARNING_ON_USAGE map-─
"Warning: map-─ was deprecated in v2.0.
Please use map-removeAt instead."
#-}

-- Version 2.1

scanr-defn : ∀ (f : A → B → B) (e : B) →
             scanr f e ≗ map (foldr f e) ∘ tails
scanr-defn f e []             = refl
scanr-defn f e (x ∷ [])       = refl
scanr-defn f e (x ∷ xs@(_ ∷ _))
  with eq ← scanr-defn f e xs
  with ys@(_ ∷ _) ← scanr f e xs
  = cong₂ (λ z → f x z ∷_) (∷-injectiveˡ eq) eq
{-# WARNING_ON_USAGE scanr-defn
"Warning: scanr-defn was deprecated in v2.1.
Please use Data.List.Scans.Properties.scanr-defn instead."
#-}

scanl-defn : ∀ (f : A → B → A) (e : A) →
             scanl f e ≗ map (foldl f e) ∘ inits
scanl-defn f e []       = refl
scanl-defn f e (x ∷ xs) = cong (e ∷_) (begin
   scanl f (f e x) xs
 ≡⟨ scanl-defn f (f e x) xs ⟩
   map (foldl f (f e x)) (inits xs)
 ≡⟨ refl ⟩
   map (foldl f e ∘ (x ∷_)) (inits xs)
 ≡⟨ map-∘ (inits xs) ⟩
   map (foldl f e) (map (x ∷_) (inits xs))
 ∎)
{-# WARNING_ON_USAGE scanl-defn
"Warning: scanl-defn was deprecated in v2.1.
Please use Data.List.Scans.Properties.scanl-defn instead."
#-}
