------------------------------------------------------------------------
-- The Agda standard library
--
-- List-related properties
------------------------------------------------------------------------

-- Note that the lemmas below could be generalised to work with other
-- equalities than _≡_.

{-# OPTIONS --without-K --safe #-}

module Data.List.Properties where

open import Algebra.Bundles
open import Algebra.Definitions as AlgebraicDefinitions using (Involutive)
import Algebra.Structures as AlgebraicStructures
open import Data.Bool.Base using (Bool; false; true; not; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; cast; toℕ; inject₁)
open import Data.List.Base as List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product as Prod hiding (map; zip)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Function
open import Level using (Level)
open import Relation.Binary as B using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Binary as B using (Rel)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary using (¬_; Dec; does; _because_; yes; no)
open import Relation.Nullary.Negation using (contradiction; ¬?)
open import Relation.Nullary.Decidable as Decidable using (isYes; map′; ⌊_⌋)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Relation.Unary.Properties using (∁?)

open ≡-Reasoning

private
  variable
    a b c d e p : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

-----------------------------------------------------------------------
-- _∷_

module _ {x y : A} {xs ys : List A} where

  ∷-injective : x ∷ xs ≡ y List.∷ ys → x ≡ y × xs ≡ ys
  ∷-injective refl = (refl , refl)

  ∷-injectiveˡ : x ∷ xs ≡ y List.∷ ys → x ≡ y
  ∷-injectiveˡ refl = refl

  ∷-injectiveʳ : x ∷ xs ≡ y List.∷ ys → xs ≡ ys
  ∷-injectiveʳ refl = refl

  ∷-dec : Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x List.∷ xs ≡ y ∷ ys)
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

map-id₂ : ∀ {f : A → A} {xs} → All (λ x → f x ≡ x) xs → map f xs ≡ xs
map-id₂ []           = refl
map-id₂ (fx≡x ∷ pxs) = cong₂ _∷_ fx≡x (map-id₂ pxs)

map-++-commute : ∀ (f : A → B) xs ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = refl
map-++-commute f (x ∷ xs) ys = cong (f x ∷_) (map-++-commute f xs ys)

map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

map-cong₂ : ∀ {f g : A → B} {xs} →
            All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
map-cong₂ []                = refl
map-cong₂ (fx≡gx ∷ fxs≡gxs) = cong₂ _∷_ fx≡gx (map-cong₂ fxs≡gxs)

length-map : ∀ (f : A → B) xs → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

map-compose : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
map-compose []       = refl
map-compose (x ∷ xs) = cong (_ ∷_) (map-compose xs)

------------------------------------------------------------------------
-- mapMaybe

mapMaybe-just : (xs : List A) → mapMaybe just xs ≡ xs
mapMaybe-just []       = refl
mapMaybe-just (x ∷ xs) = cong (x ∷_) (mapMaybe-just xs)

mapMaybe-nothing : (xs : List A) →
                   mapMaybe {B = A} (λ _ → nothing) xs ≡ []
mapMaybe-nothing []       = refl
mapMaybe-nothing (x ∷ xs) = mapMaybe-nothing xs

module _ (f : A → Maybe B) where

  mapMaybe-concatMap : mapMaybe f ≗ concatMap (fromMaybe ∘ f)
  mapMaybe-concatMap [] = refl
  mapMaybe-concatMap (x ∷ xs) with f x
  ... | just y  = cong (y ∷_) (mapMaybe-concatMap xs)
  ... | nothing = mapMaybe-concatMap xs

  length-mapMaybe : ∀ xs → length (mapMaybe f xs) ≤ length xs
  length-mapMaybe []       = z≤n
  length-mapMaybe (x ∷ xs) with f x
  ... | just y  = s≤s (length-mapMaybe xs)
  ... | nothing = ≤-step (length-mapMaybe xs)

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
    ++-identityʳ-unique xs (proj₂ (∷-injective eq))

  ++-identityˡ-unique : ∀ {xs} (ys : List A) → xs ≡ ys ++ xs → ys ≡ []
  ++-identityˡ-unique               []       _  = refl
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ ys) eq
    with ++-identityˡ-unique (ys ++ [ x ]) (begin
         xs                  ≡⟨ proj₂ (∷-injective eq) ⟩
         ys ++ x ∷ xs        ≡⟨ sym (++-assoc ys [ x ] xs) ⟩
         (ys ++ [ x ]) ++ xs ∎)
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ []   ) eq | ()
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ _ ∷ _) eq | ()

  ++-cancelˡ : ∀ xs {ys zs : List A} → xs ++ ys ≡ xs ++ zs → ys ≡ zs
  ++-cancelˡ []       ys≡zs             = ys≡zs
  ++-cancelˡ (x ∷ xs) x∷xs++ys≡x∷xs++zs = ++-cancelˡ xs (∷-injectiveʳ x∷xs++ys≡x∷xs++zs)

  ++-cancelʳ : ∀ {xs : List A} ys zs → ys ++ xs ≡ zs ++ xs → ys ≡ zs
  ++-cancelʳ {_}  []       []       _             = refl
  ++-cancelʳ {xs} []       (z ∷ zs) eq =
    contradiction (trans (cong length eq) (length-++ (z ∷ zs))) (m≢1+n+m (length xs))
  ++-cancelʳ {xs} (y ∷ ys) []       eq =
    contradiction (trans (sym (length-++ (y ∷ ys))) (cong length eq)) (m≢1+n+m (length xs) ∘ sym)
  ++-cancelʳ {_}  (y ∷ ys) (z ∷ zs) eq =
    cong₂ _∷_ (∷-injectiveˡ eq) (++-cancelʳ ys zs (∷-injectiveʳ eq))

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

------------------------------------------------------------------------
-- alignWith

module _ {f g : These A B → C} where

  alignWith-cong : f ≗ g → ∀ as → alignWith f as ≗ alignWith g as
  alignWith-cong f≗g []         bs       = map-cong (f≗g ∘ that) bs
  alignWith-cong f≗g as@(_ ∷ _) []       = map-cong (f≗g ∘ this) as
  alignWith-cong f≗g (a ∷ as)   (b ∷ bs) =
    cong₂ _∷_ (f≗g (these a b)) (alignWith-cong f≗g as bs)

  length-alignWith : ∀ xs ys →
                   length (alignWith f xs ys) ≡ length xs ⊔ length ys
  length-alignWith []         ys       = length-map (f ∘′ that) ys
  length-alignWith xs@(_ ∷ _) []       = length-map (f ∘′ this) xs
  length-alignWith (x ∷ xs)   (y ∷ ys) = cong suc (length-alignWith xs ys)

  alignWith-map : (g : D → A) (h : E → B) →
                  ∀ xs ys → alignWith f (map g xs) (map h ys) ≡
                            alignWith (f ∘′ These.map g h) xs ys
  alignWith-map g h []         ys     = sym (map-compose ys)
  alignWith-map g h xs@(_ ∷ _) []     = sym (map-compose xs)
  alignWith-map g h (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (alignWith-map g h xs ys)

  map-alignWith : ∀ (g : C → D) → ∀ xs ys →
                  map g (alignWith f xs ys) ≡
                  alignWith (g ∘′ f) xs ys
  map-alignWith g []         ys     = sym (map-compose ys)
  map-alignWith g xs@(_ ∷ _) []     = sym (map-compose xs)
  map-alignWith g (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (map-alignWith g xs ys)

------------------------------------------------------------------------
-- zipWith

module _ (f : A → A → B) where

  zipWith-comm : (∀ x y → f x y ≡ f y x) →
                 ∀ xs ys → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-comm f-comm []       []       = refl
  zipWith-comm f-comm []       (x ∷ ys) = refl
  zipWith-comm f-comm (x ∷ xs) []       = refl
  zipWith-comm f-comm (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ (f-comm x y) (zipWith-comm f-comm xs ys)

module _ (f : A → B → C) where

  zipWith-identityˡ : ∀ xs → zipWith f [] xs ≡ []
  zipWith-identityˡ []       = refl
  zipWith-identityˡ (x ∷ xs) = refl

  zipWith-identityʳ : ∀ xs → zipWith f xs [] ≡ []
  zipWith-identityʳ []       = refl
  zipWith-identityʳ (x ∷ xs) = refl

  length-zipWith : ∀ xs ys →
                   length (zipWith f xs ys) ≡ length xs ⊓ length ys
  length-zipWith []       []       = refl
  length-zipWith []       (y ∷ ys) = refl
  length-zipWith (x ∷ xs) []       = refl
  length-zipWith (x ∷ xs) (y ∷ ys) = cong suc (length-zipWith xs ys)

  zipWith-map : ∀ {d e} {D : Set d} {E : Set e} (g : D → A) (h : E → B) →
                ∀ xs ys → zipWith f (map g xs) (map h ys) ≡
                          zipWith (λ x y → f (g x) (h y)) xs ys
  zipWith-map g h []       []       = refl
  zipWith-map g h []       (y ∷ ys) = refl
  zipWith-map g h (x ∷ xs) []       = refl
  zipWith-map g h (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (zipWith-map g h xs ys)

  map-zipWith : ∀ {d} {D : Set d} (g : C → D) → ∀ xs ys →
                map g (zipWith f xs ys) ≡
                zipWith (λ x y → g (f x y)) xs ys
  map-zipWith g []       []       = refl
  map-zipWith g []       (y ∷ ys) = refl
  map-zipWith g (x ∷ xs) []       = refl
  map-zipWith g (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ refl (map-zipWith g xs ys)

------------------------------------------------------------------------
-- unalignWith

unalignWith-this : unalignWith ((A → These A B) ∋ this) ≗ (_, [])
unalignWith-this []       = refl
unalignWith-this (a ∷ as) = cong (Prod.map₁ (a ∷_)) (unalignWith-this as)

unalignWith-that : unalignWith ((B → These A B) ∋ that) ≗ ([] ,_)
unalignWith-that []       = refl
unalignWith-that (b ∷ bs) = cong (Prod.map₂ (b ∷_)) (unalignWith-that bs)

module _ {f g : C → These A B} where

  unalignWith-cong : f ≗ g → unalignWith f ≗ unalignWith g
  unalignWith-cong f≗g []       = refl
  unalignWith-cong f≗g (c ∷ cs) with f c | g c | f≗g c
  ... | this a    | ._ | refl = cong (Prod.map₁ (a ∷_)) (unalignWith-cong f≗g cs)
  ... | that b    | ._ | refl = cong (Prod.map₂ (b ∷_)) (unalignWith-cong f≗g cs)
  ... | these a b | ._ | refl = cong (Prod.map (a ∷_) (b ∷_)) (unalignWith-cong f≗g cs)

module _ (f : C → These A B) where

  unalignWith-map : (g : D → C) → ∀ ds →
                    unalignWith f (map g ds) ≡ unalignWith (f ∘′ g) ds
  unalignWith-map g []       = refl
  unalignWith-map g (d ∷ ds) with f (g d)
  ... | this a    = cong (Prod.map₁ (a ∷_)) (unalignWith-map g ds)
  ... | that b    = cong (Prod.map₂ (b ∷_)) (unalignWith-map g ds)
  ... | these a b = cong (Prod.map (a ∷_) (b ∷_)) (unalignWith-map g ds)

  map-unalignWith : (g : A → D) (h : B → E) →
    Prod.map (map g) (map h) ∘′ unalignWith f ≗ unalignWith (These.map g h ∘′ f)
  map-unalignWith g h []       = refl
  map-unalignWith g h (c ∷ cs) with f c
  ... | this a    = cong (Prod.map₁ (g a ∷_)) (map-unalignWith g h cs)
  ... | that b    = cong (Prod.map₂ (h b ∷_)) (map-unalignWith g h cs)
  ... | these a b = cong (Prod.map (g a ∷_) (h b ∷_)) (map-unalignWith g h cs)

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
    cong (Prod.map (a ∷_) (b ∷_)) (unalignWith-alignWith g g∘f≗id as bs)

------------------------------------------------------------------------
-- unzipWith

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
  zipWith-unzipWith g f∘g≗id []       = refl
  zipWith-unzipWith g f∘g≗id (x ∷ xs) =
    cong₂ _∷_ (f∘g≗id x) (zipWith-unzipWith g f∘g≗id xs)

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

-- Interaction with predicates

module _ {P : Pred A p} {f : A → A → A} where

  foldr-forcesᵇ : (∀ x y → P (f x y) → P x × P y) →
                  ∀ e xs → P (foldr f e xs) → All P xs
  foldr-forcesᵇ _      _ []       _     = []
  foldr-forcesᵇ forces _ (x ∷ xs) Pfold with forces _ _ Pfold
  ... | (px , pfxs) = px ∷ foldr-forcesᵇ forces _ xs pfxs

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

foldl-++ : ∀ (f : A → B → A) x ys zs →
           foldl f x (ys ++ zs) ≡ foldl f (foldl f x ys) zs
foldl-++ f x []       zs = refl
foldl-++ f x (y ∷ ys) zs = foldl-++ f (f x y) ys zs

foldl-∷ʳ : ∀ (f : A → B → A) x y ys →
           foldl f x (ys ∷ʳ y) ≡ f (foldl f x ys) y
foldl-∷ʳ f x y []       = refl
foldl-∷ʳ f x y (z ∷ ys) = foldl-∷ʳ f (f x z) y ys

------------------------------------------------------------------------
-- concat

concat-map : ∀ {f : A → B} → concat ∘ map (map f) ≗ map f ∘ concat
concat-map {f = f} xss = begin
  concat (map (map f) xss)                   ≡⟨ cong concat (map-is-foldr xss) ⟩
  concat (foldr (λ xs → map f xs ∷_) [] xss) ≡⟨ foldr-fusion concat [] (λ _ _ → refl) xss ⟩
  foldr (λ ys → map f ys ++_) [] xss         ≡⟨ sym (foldr-fusion (map f) [] (map-++-commute f) xss) ⟩
  map f (concat xss)                         ∎

------------------------------------------------------------------------
-- sum

sum-++-commute : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)     ≡⟨ cong (x +_) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)  ≡⟨ sym (+-assoc x _ _) ⟩
  (x + sum xs) + sum ys  ∎

------------------------------------------------------------------------
-- replicate

length-replicate : ∀ n {x : A} → length (replicate n x) ≡ n
length-replicate zero    = refl
length-replicate (suc n) = cong suc (length-replicate n)

------------------------------------------------------------------------
-- scanr

scanr-defn : ∀ (f : A → B → B) (e : B) →
             scanr f e ≗ map (foldr f e) ∘ tails
scanr-defn f e []             = refl
scanr-defn f e (x ∷ [])       = refl
scanr-defn f e (x ∷ y ∷ xs)
  with scanr f e (y ∷ xs) | scanr-defn f e (y ∷ xs)
... | []     | ()
... | z ∷ zs | eq with ∷-injective eq
...   | z≡fy⦇f⦈xs , _ = cong₂ (λ z → f x z ∷_) z≡fy⦇f⦈xs eq

------------------------------------------------------------------------
-- scanl

scanl-defn : ∀ (f : A → B → A) (e : A) →
             scanl f e ≗ map (foldl f e) ∘ inits
scanl-defn f e []       = refl
scanl-defn f e (x ∷ xs) = cong (e ∷_) (begin
   scanl f (f e x) xs
 ≡⟨ scanl-defn f (f e x) xs ⟩
   map (foldl f (f e x)) (inits xs)
 ≡⟨ refl ⟩
   map (foldl f e ∘ (x ∷_)) (inits xs)
 ≡⟨ map-compose (inits xs) ⟩
   map (foldl f e) (map (x ∷_) (inits xs))
 ∎)

------------------------------------------------------------------------
-- applyUpTo

length-applyUpTo : ∀ (f : ℕ → A) n → length (applyUpTo f n) ≡ n
length-applyUpTo f zero    = refl
length-applyUpTo f (suc n) = cong suc (length-applyUpTo (f ∘ suc) n)

lookup-applyUpTo : ∀ (f : ℕ → A) n i → lookup (applyUpTo f n) i ≡ f (toℕ i)
lookup-applyUpTo f (suc n) zero    = refl
lookup-applyUpTo f (suc n) (suc i) = lookup-applyUpTo (f ∘ suc) n i

------------------------------------------------------------------------
-- applyUpTo

module _ (f : ℕ → A) where

  length-applyDownFrom : ∀ n → length (applyDownFrom f n) ≡ n
  length-applyDownFrom zero    = refl
  length-applyDownFrom (suc n) = cong suc (length-applyDownFrom n)

  lookup-applyDownFrom : ∀ n i → lookup (applyDownFrom f n) i ≡ f (n ∸ (suc (toℕ i)))
  lookup-applyDownFrom (suc n) zero    = refl
  lookup-applyDownFrom (suc n) (suc i) = lookup-applyDownFrom n i

------------------------------------------------------------------------
-- upTo

length-upTo : ∀ n → length (upTo n) ≡ n
length-upTo = length-applyUpTo id

lookup-upTo : ∀ n i → lookup (upTo n) i ≡ toℕ i
lookup-upTo = lookup-applyUpTo id

------------------------------------------------------------------------
-- downFrom

length-downFrom : ∀ n → length (downFrom n) ≡ n
length-downFrom = length-applyDownFrom id

lookup-downFrom : ∀ n i → lookup (downFrom n) i ≡ n ∸ (suc (toℕ i))
lookup-downFrom = lookup-applyDownFrom id

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
-- _─_

length-─ : ∀ (xs : List A) k → length (xs ─ k) ≡ pred (length xs)
length-─ (x ∷ xs) zero        = refl
length-─ (x ∷ y ∷ xs) (suc k) = cong suc (length-─ (y ∷ xs) k)

map-─ : ∀ xs k (f : A → B) →
        let eq = sym (length-map f xs) in
        map f (xs ─ k) ≡ map f xs ─ cast eq k
map-─ (x ∷ xs) zero    f = refl
map-─ (x ∷ xs) (suc k) f = cong (f x ∷_) (map-─ xs k f)

------------------------------------------------------------------------
-- take

length-take : ∀ n (xs : List A) → length (take n xs) ≡ n ⊓ (length xs)
length-take zero    xs       = refl
length-take (suc n) []       = refl
length-take (suc n) (x ∷ xs) = cong suc (length-take n xs)

------------------------------------------------------------------------
-- drop

length-drop : ∀ n (xs : List A) → length (drop n xs) ≡ length xs ∸ n
length-drop zero    xs       = refl
length-drop (suc n) []       = refl
length-drop (suc n) (x ∷ xs) = length-drop n xs

take++drop : ∀ n (xs : List A) → take n xs ++ drop n xs ≡ xs
take++drop zero    xs       = refl
take++drop (suc n) []       = refl
take++drop (suc n) (x ∷ xs) = cong (x ∷_) (take++drop n xs)

------------------------------------------------------------------------
-- splitAt

splitAt-defn : ∀ n → splitAt {A = A} n ≗ < take n , drop n >
splitAt-defn zero    xs       = refl
splitAt-defn (suc n) []       = refl
splitAt-defn (suc n) (x ∷ xs) with splitAt n xs | splitAt-defn n xs
... | (ys , zs) | ih = cong (Prod.map (x ∷_) id) ih

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
  ... | true  = cong (Prod.map (x ∷_) id) (span-defn xs)
  ... | false = refl

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : Decidable P) where

  length-filter : ∀ xs → length (filter P? xs) ≤ length xs
  length-filter []       = z≤n
  length-filter (x ∷ xs) with does (P? x)
  ... | false = ≤-step (length-filter xs)
  ... | true  = s≤s (length-filter xs)

  filter-all : ∀ {xs} → All P xs → filter P? xs ≡ xs
  filter-all {[]}     []         = refl
  filter-all {x ∷ xs} (px ∷ pxs) with P? x
  ... | no          ¬px = contradiction px ¬px
  ... | true  because _ = cong (x ∷_) (filter-all pxs)

  filter-notAll : ∀ xs → Any (∁ P) xs → length (filter P? xs) < length xs
  filter-notAll (x ∷ xs) (here ¬px) with P? x
  ... | false because _ = s≤s (length-filter xs)
  ... | yes          px = contradiction px ¬px
  filter-notAll (x ∷ xs) (there any) with does (P? x)
  ... | false = ≤-step (filter-notAll xs any)
  ... | true  = s≤s (filter-notAll xs any)

  filter-some : ∀ {xs} → Any P xs → 0 < length (filter P? xs)
  filter-some {x ∷ xs} (here px)   with P? x
  ... | true because _ = s≤s z≤n
  ... | no         ¬px = contradiction px ¬px
  filter-some {x ∷ xs} (there pxs) with does (P? x)
  ... | true  = ≤-step (filter-some pxs)
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
  filter-idem (x ∷ xs) with does (P? x) | inspect does (P? x)
  ... | false | _                   = filter-idem xs
  ... | true  | P.[ eq ] rewrite eq = cong (x ∷_) (filter-idem xs)

  filter-++ : ∀ xs ys → filter P? (xs ++ ys) ≡ filter P? xs ++ filter P? ys
  filter-++ []       ys = refl
  filter-++ (x ∷ xs) ys with does (P? x)
  ... | true  = cong (x ∷_) (filter-++ xs ys)
  ... | false = filter-++ xs ys

------------------------------------------------------------------------
-- derun and deduplicate

module _ {R : Rel A p} (R? : B.Decidable R) where

  length-derun : ∀ xs → length (derun R? xs) ≤ length xs
  length-derun [] = ≤-refl
  length-derun (x ∷ []) = ≤-refl
  length-derun (x ∷ y ∷ xs) with does (R? x y) | length-derun (y ∷ xs)
  ... | true  | r = ≤-step r
  ... | false | r = s≤s r

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
  partition-defn (x ∷ xs) with does (P? x)
  ...  | true  = cong (Prod.map (x ∷_) id) (partition-defn xs)
  ...  | false = cong (Prod.map id (x ∷_)) (partition-defn xs)

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

ʳ++-++ : ∀ (xs {ys zs} : List A) → (xs ++ ys) ʳ++ zs ≡ ys ʳ++ xs ʳ++ zs
ʳ++-++ [] = refl
ʳ++-++ (x ∷ xs) {ys} {zs} = begin
  (x ∷ xs ++ ys) ʳ++ zs   ≡⟨⟩
  (xs ++ ys) ʳ++ x ∷ zs   ≡⟨ ʳ++-++ xs ⟩
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

-- reverse is an involution with respect to append.

reverse-++-commute : (xs ys : List A) →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute xs ys = begin
  reverse (xs ++ ys)         ≡⟨⟩
  (xs ++ ys) ʳ++ []          ≡⟨ ʳ++-++ xs ⟩
  ys ʳ++ xs ʳ++ []           ≡⟨⟩
  ys ʳ++ reverse xs          ≡⟨ ʳ++-defn ys ⟩
  reverse ys ++ reverse xs   ∎

-- reverse is involutive.

reverse-involutive : Involutive {A = List A} _≡_ reverse
reverse-involutive xs = begin
  reverse (reverse xs)  ≡⟨⟩
  (xs ʳ++ []) ʳ++ []    ≡⟨ ʳ++-ʳ++ xs ⟩
  [] ʳ++  xs ++ []      ≡⟨⟩
  xs ++ []              ≡⟨ ++-identityʳ xs ⟩
  xs                    ∎

-- reverse preserves length.

length-reverse : ∀ (xs : List A) → length (reverse xs) ≡ length xs
length-reverse xs = begin
  length (reverse xs)   ≡⟨⟩
  length (xs ʳ++ [])    ≡⟨ length-ʳ++ xs ⟩
  length xs + 0         ≡⟨ +-identityʳ _ ⟩
  length xs             ∎

reverse-map-commute : (f : A → B) → map f ∘ reverse ≗ reverse ∘ map f
reverse-map-commute f xs = begin
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
-- _∷ʳ_

module _ {x y : A} where

  ∷ʳ-injective : ∀ xs ys → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
  ∷ʳ-injective []          []          refl = (refl , refl)
  ∷ʳ-injective (x ∷ xs)    (y  ∷ ys)   eq   with ∷-injective eq
  ... | refl , eq′ = Prod.map (cong (x ∷_)) id (∷ʳ-injective xs ys eq′)
  ∷ʳ-injective []          (_ ∷ _ ∷ _) ()
  ∷ʳ-injective (_ ∷ _ ∷ _) []          ()

  ∷ʳ-injectiveˡ : ∀ (xs ys : List A) → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
  ∷ʳ-injectiveˡ xs ys eq = proj₁ (∷ʳ-injective xs ys eq)

  ∷ʳ-injectiveʳ : ∀ (xs ys : List A) → xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y
  ∷ʳ-injectiveʳ xs ys eq = proj₂ (∷ʳ-injective xs ys eq)



------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

gfilter-just      = mapMaybe-just
{-# WARNING_ON_USAGE gfilter-just
"Warning: gfilter-just was deprecated in v0.15.
Please use mapMaybe-just instead."
#-}
gfilter-nothing   = mapMaybe-nothing
{-# WARNING_ON_USAGE gfilter-nothing
"Warning: gfilter-nothing was deprecated in v0.15.
Please use mapMaybe-nothing instead."
#-}
gfilter-concatMap = mapMaybe-concatMap
{-# WARNING_ON_USAGE gfilter-concatMap
"Warning: gfilter-concatMap was deprecated in v0.15.
Please use mapMaybe-concatMap instead."
#-}
length-gfilter    = length-mapMaybe
{-# WARNING_ON_USAGE length-gfilter
"Warning: length-gfilter was deprecated in v0.15.
Please use length-mapMaybe instead."
#-}
right-identity-unique = ++-identityʳ-unique
{-# WARNING_ON_USAGE right-identity-unique
"Warning: right-identity-unique was deprecated in v0.15.
Please use ++-identityʳ-unique instead."
#-}
left-identity-unique  = ++-identityˡ-unique
{-# WARNING_ON_USAGE left-identity-unique
"Warning: left-identity-unique was deprecated in v0.15.
Please use ++-identityˡ-unique instead."
#-}

-- Version 0.16

module _ (p : A → Bool) where

  boolTakeWhile++boolDropWhile : ∀ xs → boolTakeWhile p xs ++ boolDropWhile p xs ≡ xs
  boolTakeWhile++boolDropWhile []       = refl
  boolTakeWhile++boolDropWhile (x ∷ xs) with p x
  ... | true  = cong (x ∷_) (boolTakeWhile++boolDropWhile xs)
  ... | false = refl
  {-# WARNING_ON_USAGE boolTakeWhile++boolDropWhile
  "Warning: boolTakeWhile and boolDropWhile were deprecated in v0.16.
  Please use takeWhile and dropWhile instead."
  #-}
  boolSpan-defn : boolSpan p ≗ < boolTakeWhile p , boolDropWhile p >
  boolSpan-defn []       = refl
  boolSpan-defn (x ∷ xs) with p x
  ... | true  = cong (Prod.map (x ∷_) id) (boolSpan-defn xs)
  ... | false = refl
  {-# WARNING_ON_USAGE boolSpan-defn
  "Warning: boolSpan, boolTakeWhile and boolDropWhile were deprecated in v0.16.
  Please use span, takeWhile and dropWhile instead."
  #-}
  length-boolFilter : ∀ xs → length (boolFilter p xs) ≤ length xs
  length-boolFilter xs =
    length-mapMaybe (λ x → if p x then just x else nothing) xs
  {-# WARNING_ON_USAGE length-boolFilter
  "Warning: boolFilter was deprecated in v0.16.
  Please use filter instead."
  #-}
  boolPartition-defn : boolPartition p ≗ < boolFilter p , boolFilter (not ∘ p) >
  boolPartition-defn []       = refl
  boolPartition-defn (x ∷ xs) with p x
  ...  | true  = cong (Prod.map (x ∷_) id) (boolPartition-defn xs)
  ...  | false = cong (Prod.map id (x ∷_)) (boolPartition-defn xs)
  {-# WARNING_ON_USAGE boolPartition-defn
  "Warning: boolPartition and boolFilter were deprecated in v0.16.
  Please use partition and filter instead."
  #-}

module _ (P : A → Set p) (P? : Decidable P) where

  boolFilter-filters : ∀ xs → All P (boolFilter (isYes ∘ P?) xs)
  boolFilter-filters []       = []
  boolFilter-filters (x ∷ xs) with P? x
  ... | true  because [px] = invert [px] ∷ boolFilter-filters xs
  ... | false because  _   = boolFilter-filters xs
  {-# WARNING_ON_USAGE boolFilter-filters
  "Warning: boolFilter was deprecated in v0.16.
  Please use filter instead."
  #-}

-- Version 0.17

idIsFold  = id-is-foldr
{-# WARNING_ON_USAGE idIsFold
"Warning: idIsFold was deprecated in v0.17.
Please use id-is-foldr instead."
#-}
++IsFold  = ++-is-foldr
{-# WARNING_ON_USAGE ++IsFold
"Warning: ++IsFold was deprecated in v0.17.
Please use ++-is-foldr instead."
#-}
mapIsFold = map-is-foldr
{-# WARNING_ON_USAGE mapIsFold
"Warning: mapIsFold was deprecated in v0.17.
Please use map-is-foldr instead."
#-}
