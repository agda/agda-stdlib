------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Colist type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Colist.Properties where

open import Level using (Level)
open import Size
open import Codata.Thunk using (Thunk; force)
open import Codata.Conat
open import Codata.Colist
open import Codata.Colist.Bisimilarity
open import Codata.Conat.Bisimilarity as coℕᵇ using (zero; suc)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
import Data.Maybe.Properties as Maybeₚ
open import Data.Maybe.Relation.Unary.All using (All; nothing; just)
open import Data.Nat.Base using (zero; suc)
open import Data.Product as Prod using (_×_; _,_; uncurry)
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; [_])

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    i : Size

------------------------------------------------------------------------
-- Functor laws

map-identity : ∀ (as : Colist A ∞) → i ⊢ map id as ≈ as
map-identity []       = []
map-identity (a ∷ as) = Eq.refl ∷ λ where .force → map-identity (as .force)

map-map-fusion : ∀ (f : A → B) (g : B → C) as {i} →
                 i ⊢ map g (map f as) ≈ map (g ∘ f) as
map-map-fusion f g []       = []
map-map-fusion f g (a ∷ as) =
  Eq.refl ∷ λ where .force → map-map-fusion f g (as .force)

------------------------------------------------------------------------
-- Relation to Cowriter

fromCowriter∘toCowriter≗id : ∀ (as : Colist A ∞) →
  i ⊢ fromCowriter (toCowriter as) ≈ as
fromCowriter∘toCowriter≗id []       = []
fromCowriter∘toCowriter≗id (a ∷ as) =
  Eq.refl ∷ λ where .force → fromCowriter∘toCowriter≗id (as .force)

------------------------------------------------------------------------
-- Properties of length

length-replicate : ∀ n (a : A) → i coℕᵇ.⊢ length (replicate n a) ≈ n
length-replicate zero    a = zero
length-replicate (suc n) a = suc λ where .force → length-replicate (n .force) a

length-++ : (as bs : Colist A ∞) →
            i coℕᵇ.⊢ length (as ++ bs) ≈ length as + length bs
length-++ []       bs = coℕᵇ.refl
length-++ (a ∷ as) bs = suc λ where .force → length-++ (as .force) bs

------------------------------------------------------------------------
-- Properties of replicate

replicate-+ : ∀ m n (a : A) →
              i ⊢ replicate (m + n) a ≈ replicate m a ++ replicate n a
replicate-+ zero    n a = refl
replicate-+ (suc m) n a = Eq.refl ∷ λ where .force → replicate-+ (m .force) n a

map-replicate : ∀ (f : A → B) n a →
                i ⊢ map f (replicate n a) ≈ replicate n (f a)
map-replicate f zero    a = []
map-replicate f (suc n) a =
  Eq.refl ∷ λ where .force → map-replicate f (n .force) a

lookup-replicate : ∀ k n (a : A) → All (a ≡_) (lookup k (replicate n a))
lookup-replicate k zero          a = nothing
lookup-replicate zero    (suc n) a = just Eq.refl
lookup-replicate (suc k) (suc n) a = lookup-replicate k (n .force) a

------------------------------------------------------------------------
-- Properties of unfold

map-unfold : ∀ (f : B → C) (alg : A → Maybe (A × B)) a →
             i ⊢ map f (unfold alg a) ≈ unfold (Maybe.map (Prod.map₂ f) ∘ alg) a
map-unfold f alg a with alg a
... | nothing       = []
... | just (a′ , b) = Eq.refl ∷ λ where .force → map-unfold f alg a′

module _ {alg : A → Maybe (A × B)} {a} where

  unfold-nothing : alg a ≡ nothing → unfold alg a ≡ []
  unfold-nothing eq with alg a
  ... | nothing = Eq.refl

  unfold-just : ∀ {a′ b} → alg a ≡ just (a′ , b) →
                i ⊢ unfold alg a ≈ b ∷ λ where .force → unfold alg a′
  unfold-just eq with alg a
  unfold-just Eq.refl | just (a′ , b) = Eq.refl ∷ λ where .force → refl

module _ (cons : C → B → C) (alg : A → Maybe (A × B)) where

  private
    alg′ : (A × C) → Maybe ((A × C) × C)
    alg′ (a , c) = Maybe.map (uncurry step) (alg a) where
      step = λ a′ b → let b′ = cons c b in (a′ , b′) , b′

  scanl-unfold : ∀ nil a → i ⊢ scanl cons nil (unfold alg a)
                             ≈ nil ∷ (λ where .force → unfold alg′ (a , nil))
  scanl-unfold nil a with alg a | Eq.inspect alg a
  ... | nothing       | [ eq ] = Eq.refl ∷ λ { .force →
    sym (fromEq (unfold-nothing (Maybeₚ.map-nothing eq))) }
  ... | just (a′ , b) | [ eq ] = Eq.refl ∷ λ { .force → begin
    scanl cons (cons nil b) (unfold alg a′)
     ≈⟨ scanl-unfold (cons nil b) a′ ⟩
    (cons nil b ∷ _)
     ≈⟨ Eq.refl ∷ (λ where .force → refl) ⟩
    (cons nil b ∷ _)
     ≈˘⟨ unfold-just (Maybeₚ.map-just eq) ⟩
    unfold alg′ (a , nil) ∎ } where open ≈-Reasoning
