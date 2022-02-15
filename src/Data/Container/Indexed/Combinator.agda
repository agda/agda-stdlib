------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Indexed.Combinator where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Container.Indexed
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Product as Prod hiding (Σ) renaming (_×_ to _⟨×⟩_)
open import Data.Sum renaming (_⊎_ to _⟨⊎⟩_)
open import Data.Sum.Relation.Unary.All as All using (All)
open import Function as F hiding (id; const) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse using (_↔̇_; inverse)
open import Level
open import Relation.Unary using (Pred; _⊆_; _∪_; _∩_; ⋃; ⋂)
  renaming (_⟨×⟩_ to _⟪×⟫_; _⟨⊙⟩_ to _⟪⊙⟫_; _⟨⊎⟩_ to _⟪⊎⟫_)
open import Relation.Binary.PropositionalEquality as P
  using (_≗_; refl)

private
  variable
    ℓ ℓ₁ ℓ₂ i j k o c c₁ c₂ r r₁ r₂ x z : Level
    I J K O X Z : Set _

------------------------------------------------------------------------
-- Combinators


-- Identity.

id : Container O O c r
id = F.const ⊤ ◃ F.const ⊤ / (λ {o} _ _ → o)

-- Constant.

const : Pred O c → Container I O c r
const X = X ◃ F.const ⊥ / F.const ⊥-elim

-- Composition.

infixr 9 _∘_

_∘_ : Container J K c₁ r₁ → Container I J c₂ r₂ → Container I K _ _
C₁ ∘ C₂ = C ◃ R / n
  where
  C : ∀ k → Set _
  C = ⟦ C₁ ⟧ (Command C₂)

  R : ∀ {k} → ⟦ C₁ ⟧ (Command C₂) k → Set _
  R (c , k) = ◇ C₁ {X = Command C₂} (Response C₂ ⟨∘⟩ proj₂) (_ , c , k)

  n : ∀ {k} (c : ⟦ C₁ ⟧ (Command C₂) k) → R c → _
  n (_ , f) (r₁ , r₂) = next C₂ (f r₁) r₂

-- Duality.

_^⊥ : Container I O c r → Container I O (c ⊔ r) c
(C ^⊥) .Command  o     = (c : C .Command o) → C .Response c
(C ^⊥) .Response {o} _ = C .Command o
(C ^⊥) .next     f c   = C .next c (f c)

-- Strength.

infixl 3 _⋊_

_⋊_ : Container I O c r → (Z : Set z) → Container (I ⟨×⟩ Z) (O ⟨×⟩ Z) c r
(C ⋊ Z) .Command  (o , z)     = C .Command o
(C ⋊ Z) .Response             = C .Response
(C ⋊ Z) .next     {o , z} c r = C .next c r , z

infixr 3 _⋉_

_⋉_ : (Z : Set z) → Container I O c r → Container (Z ⟨×⟩ I) (Z ⟨×⟩ O) c r
(Z ⋉ C) .Command  (z , o)     = C .Command o
(Z ⋉ C) .Response             = C .Response
(Z ⋉ C) .next     {z , o} c r = z , C .next c r



-- Product. (Note that, up to isomorphism, and ignoring universe level
-- issues, this is a special case of indexed product.)

infixr 2 _×_

_×_ : Container I O c₁ r₁ → Container I O c₂ r₂ → Container I O _ _
(C₁ ◃ R₁ / n₁) × (C₂ ◃ R₂ / n₂) = record
  { Command  = C₁ ∩ C₂
  ; Response = R₁ ⟪⊙⟫ R₂
  ; next     = λ { (c₁ , c₂) → [ n₁ c₁ , n₂ c₂ ] }
  }

-- Indexed product.

Π : (X → Container I O c r) → Container I O _ _
Π {X = X} C = record
  { Command  = ⋂ X (Command ⟨∘⟩ C)
  ; Response = ⋃[ x ∶ X ] λ c → Response (C x) (c x)
  ; next     = λ { c (x , r) → next (C x) (c x) r }
  }

-- Sum. (Note that, up to isomorphism, and ignoring universe level
-- issues, this is a special case of indexed sum.)

infixr 1  _⊎_ _⊎′_

_⊎_ : Container I O c₁ r₁ → Container I O c₂ r₂ → Container I O _ _
(C₁ ⊎ C₂) .Command  = C₁ .Command ∪ C₂ .Command
(C₁ ⊎ C₂) .Response = All (C₁ .Response) (C₂ .Response)
(C₁ ⊎ C₂) .next     = All.[ C₁ .next , C₂ .next ]

-- A simplified version for responses at the same level r:

_⊎′_ : Container I O c₁ r → Container I O c₂ r → Container I O _ r
(C₁ ◃ R₁ / n₁) ⊎′ (C₂ ◃ R₂ / n₂) = record
  { Command  = C₁ ∪ C₂
  ; Response = [ R₁ , R₂ ]
  ; next     = [ n₁ , n₂ ]
  }

-- Indexed sum.

Σ : (X → Container I O c r) → Container I O _ r
Σ {X = X} C = record
  { Command  = ⋃ X (Command ⟨∘⟩ C)
  ; Response = λ { (x , c) → Response (C x) c }
  ; next     = λ { (x , c) r → next (C x) c r }
  }

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : (X : Set ℓ) → Container I O c r → Container I O _ _
const[ X ]⟶ C = Π {X = X} (F.const C)

------------------------------------------------------------------------
-- Correctness proofs

module Identity where

  correct : {X : Pred O ℓ} → ⟦ id {c = c}{r} ⟧ X ↔̇ F.id X
  correct {X = X} = inverse to from (λ _ → refl) (λ _ → refl)
    where
    to : ∀ {x} → ⟦ id ⟧ X x → F.id X x
    to xs = proj₂ xs _

    from : ∀ {x} → F.id X x → ⟦ id ⟧ X x
    from x = (_ , λ _ → x)

module Constant (ext : ∀ {ℓ} → Extensionality ℓ ℓ) where

  correct : (X : Pred O ℓ₁) {Y : Pred O ℓ₂} → ⟦ const X ⟧ Y ↔̇ F.const X Y
  correct X {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → refl
      ; left-inverse-of  = to∘from
      }
    }
    where
    to : ⟦ const X ⟧ Y ⊆ X
    to = proj₁

    from : X ⊆ ⟦ const X ⟧ Y
    from = < F.id , F.const ⊥-elim >

    to∘from : _
    to∘from xs = P.cong (proj₁ xs ,_) (ext ⊥-elim)

module Duality where

  correct : (C : Container I O c r) (X : Pred I ℓ) →
            ⟦ C ^⊥ ⟧ X ↔̇ (λ o → (c : Command C o) → ∃ λ r → X (next C c r))
  correct C X = inverse (λ { (f , g) → < f , g > }) (λ f → proj₁ ⟨∘⟩ f , proj₂ ⟨∘⟩ f)
                        (λ _ → refl) (λ _ → refl)

module Composition where

  correct : (C₁ : Container J K c r) (C₂ : Container I J c r) →
            {X : Pred I ℓ} → ⟦ C₁ ∘ C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ ⟨∘⟩ ⟦ C₂ ⟧) X
  correct C₁ C₂ {X} = inverse to from (λ _ → refl) (λ _ → refl)
    where
    to : ⟦ C₁ ∘ C₂ ⟧ X ⊆ ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
    to ((c , f) , g) = (c , < f , curry g >)

    from : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) ⊆ ⟦ C₁ ∘ C₂ ⟧ X
    from (c , f) = ((c , proj₁ ⟨∘⟩ f) , uncurry (proj₂ ⟨∘⟩ f))

module Product (ext : ∀ {ℓ} → Extensionality ℓ ℓ) where

  correct : (C₁ C₂ : Container I O c r) {X : Pred I _} →
            ⟦ C₁ × C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ X ∩ ⟦ C₂ ⟧ X)
  correct C₁ C₂ {X} = inverse to from from∘to (λ _ → refl)
    where
    to : ⟦ C₁ × C₂ ⟧ X ⊆ ⟦ C₁ ⟧ X ∩ ⟦ C₂ ⟧ X
    to ((c₁ , c₂) , k) = ((c₁ , k ⟨∘⟩ inj₁) , (c₂ , k ⟨∘⟩ inj₂))

    from : ⟦ C₁ ⟧ X ∩ ⟦ C₂ ⟧ X ⊆ ⟦ C₁ × C₂ ⟧ X
    from ((c₁ , k₁) , (c₂ , k₂)) = ((c₁ , c₂) , [ k₁ , k₂ ])

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (c , _) =
      P.cong (c ,_) (ext [ (λ _ → refl) , (λ _ → refl) ])

module IndexedProduct where

  correct : (C : X → Container I O c r) {Y : Pred I ℓ} →
            ⟦ Π C ⟧ Y ↔̇ ⋂[ x ∶ X ] ⟦ C x ⟧ Y
  correct {X = X} C {Y} = inverse to from (λ _ → refl) (λ _ → refl)
    where
    to : ⟦ Π C ⟧ Y ⊆ ⋂[ x ∶ X ] ⟦ C x ⟧ Y
    to (c , k) = λ x → (c x , λ r → k (x , r))

    from : ⋂[ x ∶ X ] ⟦ C x ⟧ Y ⊆ ⟦ Π C ⟧ Y
    from f = (proj₁ ⟨∘⟩ f , uncurry (proj₂ ⟨∘⟩ f))

module Sum (ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

  correct : (C₁ C₂ : Container I O c r) {X : Pred I ℓ} →
            ⟦ C₁ ⊎ C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X)
  correct C₁ C₂ {X} = inverse to from from∘to to∘from
    where
    to : ⟦ C₁ ⊎ C₂ ⟧ X ⊆ ⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X
    to (inj₁ c₁ , k) = inj₁ (c₁ , λ r → k (All.inj₁ r))
    to (inj₂ c₂ , k) = inj₂ (c₂ , λ r → k (All.inj₂ r))

    from : ⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X ⊆ ⟦ C₁ ⊎ C₂ ⟧ X
    from (inj₁ (c , f)) = inj₁ c , λ{ (All.inj₁ r) → f r}
    from (inj₂ (c , f)) = inj₂ c , λ{ (All.inj₂ r) → f r}

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (inj₁ _ , _) = P.cong (inj₁ _ ,_) (ext λ{ (All.inj₁ r) → refl})
    from∘to (inj₂ _ , _) = P.cong (inj₂ _ ,_) (ext λ{ (All.inj₂ r) → refl})

    to∘from : to ⟨∘⟩ from ≗ F.id
    to∘from =  [ (λ _ → refl) , (λ _ → refl) ]

module Sum′ where

  correct : (C₁ C₂ : Container I O c r) {X : Pred I ℓ} →
            ⟦ C₁ ⊎′ C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X)
  correct C₁ C₂ {X} = inverse to from from∘to to∘from
    where
    to : ⟦ C₁ ⊎′ C₂ ⟧ X ⊆ ⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X
    to (inj₁ c₁ , k) = inj₁ (c₁ , k)
    to (inj₂ c₂ , k) = inj₂ (c₂ , k)

    from : ⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X ⊆ ⟦ C₁ ⊎′ C₂ ⟧ X
    from = [ Prod.map inj₁ F.id , Prod.map inj₂ F.id ]

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (inj₁ _ , _) = refl
    from∘to (inj₂ _ , _) = refl

    to∘from : to ⟨∘⟩ from ≗ F.id
    to∘from = [ (λ _ → refl) , (λ _ → refl) ]

module IndexedSum where

  correct : (C : X → Container I O c r) {Y : Pred I ℓ} →
            ⟦ Σ C ⟧ Y ↔̇ ⋃[ x ∶ X ] ⟦ C x ⟧ Y
  correct {X = X} C {Y} = inverse to from (λ _ → refl) (λ _ → refl)
    where
    to : ⟦ Σ C ⟧ Y ⊆ ⋃[ x ∶ X ] ⟦ C x ⟧ Y
    to ((x , c) , k) = (x , (c , k))

    from : ⋃[ x ∶ X ] ⟦ C x ⟧ Y ⊆ ⟦ Σ C ⟧ Y
    from (x , (c , k)) = ((x , c) , k)

module ConstantExponentiation where

  correct : (C : Container I O c r) {Y : Pred I ℓ} →
            ⟦ const[ X ]⟶ C ⟧ Y ↔̇ (⋂ X (F.const (⟦ C ⟧ Y)))
  correct C {Y} = IndexedProduct.correct (F.const C) {Y}
