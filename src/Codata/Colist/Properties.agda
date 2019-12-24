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
open import Codata.Colist
open import Codata.Colist.Bisimilarity
open import Codata.Conat
open import Codata.Conat.Bisimilarity as coℕᵇ using (zero; suc)
import Codata.Conat.Properties as coℕₚ
open import Codata.Stream as Stream using (Stream; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
import Data.Maybe.Properties as Maybeₚ
open import Data.Maybe.Relation.Unary.All using (All; nothing; just)
open import Data.Nat.Base as ℕ using (zero; suc)
open import Data.Product as Prod using (_×_; _,_; uncurry)
open import Data.These.Base as These using (These; this; that; these)
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; [_])

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
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

length-∷ : ∀ (a : A) as → i coℕᵇ.⊢ length (a ∷ as) ≈ 1 ℕ+ length (as .force)
length-∷ a as = suc (λ where .force → coℕᵇ.refl)

length-replicate : ∀ n (a : A) → i coℕᵇ.⊢ length (replicate n a) ≈ n
length-replicate zero    a = zero
length-replicate (suc n) a = suc λ where .force → length-replicate (n .force) a

length-++ : (as bs : Colist A ∞) →
            i coℕᵇ.⊢ length (as ++ bs) ≈ length as + length bs
length-++ []       bs = coℕᵇ.refl
length-++ (a ∷ as) bs = suc λ where .force → length-++ (as .force) bs

length-map : ∀ (f : A → B) as → i coℕᵇ.⊢ length (map f as) ≈ length as
length-map f []       = zero
length-map f (a ∷ as) = suc λ where .force → length-map f (as .force)

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

------------------------------------------------------------------------
-- Properties of scanl

length-scanl : ∀ (c : B → A → B) n as →
               i coℕᵇ.⊢ length (scanl c n as) ≈ 1 ℕ+ length as
length-scanl c n []       = suc λ where .force → zero
length-scanl c n (a ∷ as) = suc λ { .force → begin
  length (scanl c (c n a) (as .force))
    ≈⟨ length-scanl c (c n a) (as .force) ⟩
  1 ℕ+ length (as .force)
    ≈˘⟨ length-∷ a as ⟩
  length (a ∷ as) ∎ } where open coℕᵇ.≈-Reasoning

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

------------------------------------------------------------------------
-- Properties of alignwith

map-alignWith : ∀ (f : C → D) (al : These A B → C) as bs →
                i ⊢ map f (alignWith al as bs) ≈ alignWith (f ∘ al) as bs
map-alignWith f al []         bs       = map-map-fusion (al ∘′ that) f bs
map-alignWith f al as@(_ ∷ _) []       = map-map-fusion (al ∘′ this) f as
map-alignWith f al (a ∷ as)   (b ∷ bs) =
  Eq.refl ∷ λ where .force → map-alignWith f al (as .force) (bs .force)

length-alignWith : ∀ (al : These A B → C) as bs →
                   i coℕᵇ.⊢ length (alignWith al as bs) ≈ length as ⊔ length bs
length-alignWith al []         bs       = length-map (al ∘ that) bs
length-alignWith al as@(_ ∷ _) []       = length-map (al ∘ this) as
length-alignWith al (a ∷ as)   (b ∷ bs) =
  suc λ where .force → length-alignWith al (as .force) (bs .force)

------------------------------------------------------------------------
-- Properties of zipwith

map-zipWith : ∀ (f : C → D) (zp : A → B → C) as bs →
              i ⊢ map f (zipWith zp as bs) ≈ zipWith (λ a → f ∘ zp a) as bs
map-zipWith f zp []       _        = []
map-zipWith f zp (_ ∷ _)  []       = []
map-zipWith f zp (a ∷ as) (b ∷ bs) =
  Eq.refl ∷ λ where .force → map-zipWith f zp (as .force) (bs .force)

length-zipWith : ∀ (zp : A → B → C) as bs →
                 i coℕᵇ.⊢ length (zipWith zp as bs) ≈ length as ⊓ length bs
length-zipWith zp []         bs       = zero
length-zipWith zp as@(_ ∷ _) []       = zero
length-zipWith zp (a ∷ as)   (b ∷ bs) =
  suc λ where .force → length-zipWith zp (as .force) (bs .force)

------------------------------------------------------------------------
-- Properties of drop

drop-nil : ∀ m → i ⊢ drop {A = A} m [] ≈ []
drop-nil zero    = []
drop-nil (suc m) = []

drop-drop-fusion : ∀ m n (as : Colist A ∞) →
                   i ⊢ drop n (drop m as) ≈ drop (m ℕ.+ n) as
drop-drop-fusion zero    n as       = refl
drop-drop-fusion (suc m) n []       = drop-nil n
drop-drop-fusion (suc m) n (a ∷ as) = drop-drop-fusion m n (as .force)

map-drop : ∀ (f : A → B) m as → i ⊢ map f (drop m as) ≈ drop m (map f as)
map-drop f zero    as       = refl
map-drop f (suc m) []       = []
map-drop f (suc m) (a ∷ as) = map-drop f m (as .force)

length-drop : ∀ m (as : Colist A ∞) → i coℕᵇ.⊢ length (drop m as) ≈ length as ∸ m
length-drop zero    as       = coℕᵇ.refl
length-drop (suc m) []       = coℕᵇ.sym (coℕₚ.0∸m≈0 m)
length-drop (suc m) (a ∷ as) = length-drop m (as .force)

------------------------------------------------------------------------
-- Properties of cotake

length-cotake : ∀ n (as : Stream A ∞) → i coℕᵇ.⊢ length (cotake n as) ≈ n
length-cotake zero    as       = zero
length-cotake (suc n) (a ∷ as) =
  suc λ where .force → length-cotake (n .force) (as .force)

map-cotake : ∀ (f : A → B) n as →
             i ⊢ map f (cotake n as) ≈ cotake n (Stream.map f as)
map-cotake f zero    as       = []
map-cotake f (suc n) (a ∷ as) =
  Eq.refl ∷ λ where .force → map-cotake f (n .force) (as .force)

