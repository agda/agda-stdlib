------------------------------------------------------------------------
-- The Agda standard library
--
-- General notion of splitting a list in two in an order-preserving manner
------------------------------------------------------------------------

module Data.List.Relation.Split where

open import Level
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Permutation.Inductive as Perm using (_↭_)
open import Data.List.Relation.Permutation.Inductive.Properties using (shift)
open import Data.Product as Prod using (∃; ∃₂; _×_; uncurry; _,_; -,_; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         (L : REL A B l) (R : REL A C r) where

  data Split : List A → REL (List B) (List C) (l ⊔ r) where
    []   : Split [] [] []
    _ˡ∷_ : ∀ {a b as l r} → L a b → Split as l r → Split (a ∷ as) (b ∷ l) r
    _ʳ∷_ : ∀ {a b as l r} → R a b → Split as l r → Split (a ∷ as) l (b ∷ r)

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A B l} {R : REL A C r} where

-- injections

  left : ∀ {as bs} → Pointwise L as bs → Split L R as bs []
  left []       = []
  left (l ∷ pw) = l ˡ∷ left pw

  right : ∀ {as bs} → Pointwise R as bs → Split L R as [] bs
  right []       = []
  right (r ∷ pw) = r ʳ∷ right pw

-- swap

  swap : ∀ {as l r} → Split L R as l r → Split R L as r l
  swap []        = []
  swap (l ˡ∷ sp) = l ʳ∷ swap sp
  swap (r ʳ∷ sp) = r ˡ∷ swap sp

-- extract the "proper" equality split from the pointwise relations

  break : ∀ {as l r} → Split L R as l r → ∃ $ uncurry $ λ asl asr →
          Split _≡_ _≡_ as asl asr × Pointwise L asl l × Pointwise R asr r
  break []        = -, [] , [] , []
  break (l ˡ∷ sp) = let (_ , eq , pwl , pwr) = break sp in
                    -, P.refl ˡ∷ eq , l ∷ pwl , pwr
  break (r ʳ∷ sp) = let (_ , eq , pwl , pwr) = break sp in
                    -, P.refl ʳ∷ eq , pwl , r ∷ pwr

-- map

module _ {a b c l r p q} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A B l} {R : REL A C r} {P : REL A B p} {Q : REL A C q} where

  map : ∀ {as l r} → L ⇒ P → R ⇒ Q → Split L R as l r → Split P Q as l r
  map L⇒P R⇒Q []        = []
  map L⇒P R⇒Q (l ˡ∷ sp) = L⇒P l ˡ∷ map L⇒P R⇒Q sp
  map L⇒P R⇒Q (r ʳ∷ sp) = R⇒Q r ʳ∷ map L⇒P R⇒Q sp

module _ {a b c l r p} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A B l} {R : REL A C r} where

  map₁ : ∀ {P : REL A B p} {as l r} → L ⇒ P → Split L R as l r → Split P R as l r
  map₁ L⇒P = map L⇒P id

  map₂ : ∀ {P : REL A C p} {as l r} → R ⇒ P → Split L R as l r → Split L P as l r
  map₂ = map id


------------------------------------------------------------------------
-- Special case: The second and third list have the same type

module _ {a b l r} {A : Set a} {B : Set b} {L : REL A B l} {R : REL A B r} where

-- converting back and forth with pointwise

  split : ∀ {as bs} → Pointwise (λ a b → L a b ⊎ R a b) as bs →
          ∃ (uncurry $ Split L R as)
  split []            = -, []
  split (inj₁ l ∷ pw) = Prod.map _ (l ˡ∷_) (split pw)
  split (inj₂ r ∷ pw) = Prod.map _ (r ʳ∷_) (split pw)

  unsplit : ∀ {as l r} → Split L R as l r → ∃ (Pointwise (λ a b → L a b ⊎ R a b) as)
  unsplit []        = -, []
  unsplit (l ˡ∷ sp) = Prod.map _ (inj₁ l ∷_) (unsplit sp)
  unsplit (r ʳ∷ sp) = Prod.map _ (inj₂ r ∷_) (unsplit sp)

------------------------------------------------------------------------
-- Special case: all the lists have the same type

module _ {a} {A : Set a} where

-- An equality split induces a permutation:

  toPermutation : {as l r : List A} → Split _≡_ _≡_ as l r → as ↭ l List.++ r
  toPermutation []             = Perm.refl
  toPermutation (P.refl ˡ∷ sp) = Perm.prep _ (toPermutation sp)
  toPermutation {a ∷ as} {l} {r ∷ rs} (P.refl ʳ∷ sp) = begin
    a ∷ as           ↭⟨ Perm.prep a (toPermutation sp) ⟩
    a ∷ l List.++ rs ↭⟨ Perm.↭-sym (shift a l rs) ⟩
    l List.++ a ∷ rs ∎ where open Perm.PermutationReasoning
