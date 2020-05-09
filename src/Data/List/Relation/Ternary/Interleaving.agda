------------------------------------------------------------------------
-- The Agda standard library
--
-- Generalised notion of interleaving two lists into one in an
-- order-preserving manner
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Ternary.Interleaving where

open import Level
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product as Prod using (∃; ∃₂; _×_; uncurry; _,_; -,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Definition

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         (L : REL A C l) (R : REL B C r) where

  data Interleaving : List A → List B → List C → Set (a ⊔ b ⊔ c ⊔ l ⊔ r) where
    []   : Interleaving [] [] []
    _∷ˡ_ : ∀ {a c l r cs} → L a c → Interleaving l r cs → Interleaving (a ∷ l) r (c ∷ cs)
    _∷ʳ_ : ∀ {b c l r cs} → R b c → Interleaving l r cs → Interleaving l (b ∷ r) (c ∷ cs)

------------------------------------------------------------------------
-- Operations

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A C l} {R : REL B C r} where

-- injections

  left : ∀ {as cs} → Pointwise L as cs → Interleaving L R as [] cs
  left []       = []
  left (l ∷ pw) = l ∷ˡ left pw

  right : ∀ {bs cs} → Pointwise R bs cs → Interleaving L R [] bs cs
  right []       = []
  right (r ∷ pw) = r ∷ʳ right pw

-- swap

  swap : ∀ {cs l r} → Interleaving L R l r cs → Interleaving R L r l cs
  swap []        = []
  swap (l ∷ˡ sp) = l ∷ʳ swap sp
  swap (r ∷ʳ sp) = r ∷ˡ swap sp

-- extract the "proper" equality split from the pointwise relations

  break : ∀ {cs l r} → Interleaving L R l r cs → ∃ $ uncurry $ λ csl csr →
          Interleaving _≡_ _≡_ csl csr cs × Pointwise L l csl × Pointwise R r csr
  break []        = -, [] , [] , []
  break (l ∷ˡ sp) = let (_ , eq , pwl , pwr) = break sp in
                    -, P.refl ∷ˡ eq , l ∷ pwl , pwr
  break (r ∷ʳ sp) = let (_ , eq , pwl , pwr) = break sp in
                    -, P.refl ∷ʳ eq , pwl , r ∷ pwr

-- map

module _ {a b c l r p q} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A C l} {R : REL B C r} {P : REL A C p} {Q : REL B C q} where

  map : ∀ {cs l r} → L ⇒ P → R ⇒ Q → Interleaving L R l r cs → Interleaving P Q l r cs
  map L⇒P R⇒Q []        = []
  map L⇒P R⇒Q (l ∷ˡ sp) = L⇒P l ∷ˡ map L⇒P R⇒Q sp
  map L⇒P R⇒Q (r ∷ʳ sp) = R⇒Q r ∷ʳ map L⇒P R⇒Q sp

module _ {a b c l r p} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A C l} {R : REL B C r} where

  map₁ : ∀ {P : REL A C p} {as l r} → L ⇒ P →
         Interleaving L R l r as → Interleaving P R l r as
  map₁ L⇒P = map L⇒P id

  map₂ : ∀ {P : REL B C p} {as l r} → R ⇒ P →
         Interleaving L R l r as → Interleaving L P l r as
  map₂ = map id

------------------------------------------------------------------------
-- Special case: The second and third list have the same type

module _ {a b l r} {A : Set a} {B : Set b} {L : REL A B l} {R : REL A B r} where

-- converting back and forth with pointwise

  split : ∀ {as bs} → Pointwise (λ a b → L a b ⊎ R a b) as bs →
          ∃₂ λ asr asl → Interleaving L R asl asr bs
  split []            = [] , [] , []
  split (inj₁ l ∷ pw) = Prod.map _ (Prod.map _ (l ∷ˡ_)) (split pw)
  split (inj₂ r ∷ pw) = Prod.map _ (Prod.map _ (r ∷ʳ_)) (split pw)

  unsplit : ∀ {l r as} → Interleaving L R l r as →
            ∃ λ bs → Pointwise (λ a b → L a b ⊎ R a b) bs as
  unsplit []        = -, []
  unsplit (l ∷ˡ sp) = Prod.map _ (inj₁ l ∷_) (unsplit sp)
  unsplit (r ∷ʳ sp) = Prod.map _ (inj₂ r ∷_) (unsplit sp)
