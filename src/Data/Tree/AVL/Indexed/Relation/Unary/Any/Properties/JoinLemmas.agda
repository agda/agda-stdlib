------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties constant-time join functions related to Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.JoinLemmas
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (∃; _,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p
    l u : Key⁺
    hˡ hʳ h : ℕ

  [_]ᵏ : K& V → Key⁺
  [ kv ]ᵏ = [ kv .key ]


----------------------------------------------------------------------
-- joinˡ⁺

joinˡ⁺-here⁺ : (kv : K& V) →
               (l : Tree⁺ V l [ kv ]ᵏ hˡ) →
               (r : Tree V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P kv → Any P (proj₂ (joinˡ⁺ kv l r bal))
joinˡ⁺-here⁺ _ (0# , _)                 _ _  p = here p
joinˡ⁺-here⁺ _ (1# , _)                 _ ∼0 p = here p
joinˡ⁺-here⁺ _ (1# , _)                 _ ∼+ p = here p
joinˡ⁺-here⁺ _ (1# , node _ _ _ ∼-)     _ ∼- p = right (here p)
joinˡ⁺-here⁺ _ (1# , node _ _ _ ∼0)     _ ∼- p = right (here p)
joinˡ⁺-here⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- p = right (here p)

joinˡ⁺-left⁺ : (kv : K& V) →
               (l@(_ , lt) : Tree⁺ V l [ kv ]ᵏ hˡ) →
               (r : Tree V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P lt → Any P (proj₂ (joinˡ⁺ kv l r bal))
joinˡ⁺-left⁺ _ (0# , _)                 _ _  p                 = left p
joinˡ⁺-left⁺ _ (1# , _)                 _ ∼0 p                 = left p
joinˡ⁺-left⁺ _ (1# , _)                 _ ∼+ p                 = left p
joinˡ⁺-left⁺ _ (1# , node _ _ _ ∼-)     _ ∼- (here p)          = here p
joinˡ⁺-left⁺ _ (1# , node _ _ _ ∼-)     _ ∼- (left p)          = left p
joinˡ⁺-left⁺ _ (1# , node _ _ _ ∼-)     _ ∼- (right p)         = right (left p)
joinˡ⁺-left⁺ _ (1# , node _ _ _ ∼0)     _ ∼- (here p)          = here p
joinˡ⁺-left⁺ _ (1# , node _ _ _ ∼0)     _ ∼- (left p)          = left p
joinˡ⁺-left⁺ _ (1# , node _ _ _ ∼0)     _ ∼- (right p)         = right (left p)
joinˡ⁺-left⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- (here p)          = left (here p)
joinˡ⁺-left⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- (left p)          = left (left p)
joinˡ⁺-left⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- (right (here p))  = here p
joinˡ⁺-left⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- (right (left p))  = left (right p)
joinˡ⁺-left⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- (right (right p)) = right (left p)

joinˡ⁺-right⁺ : (kv : K& V) →
                (l : Tree⁺ V l [ kv ]ᵏ hˡ) →
                (r : Tree V [ kv ]ᵏ u hʳ) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P r → Any P (proj₂ (joinˡ⁺ kv l r bal))
joinˡ⁺-right⁺ _ (0# , _)                 _ _  p = right p
joinˡ⁺-right⁺ _ (1# , _)                 _ ∼0 p = right p
joinˡ⁺-right⁺ _ (1# , _)                 _ ∼+ p = right p
joinˡ⁺-right⁺ _ (1# , node _ _ _ ∼-)     _ ∼- p = right (right p)
joinˡ⁺-right⁺ _ (1# , node _ _ _ ∼0)     _ ∼- p = right (right p)
joinˡ⁺-right⁺ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- p = right (right p)

joinˡ⁺⁻ : (kv : K& V) →
          (l@(_ , lt) : Tree⁺ V l [ kv ]ᵏ hˡ) →
          (r : Tree V [ kv ]ᵏ u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (joinˡ⁺ kv l r bal)) →
          P kv ⊎ Any P lt ⊎ Any P r
joinˡ⁺⁻ _ (0# , _)                 _ _  = Any.toSum
joinˡ⁺⁻ _ (1# , _)                 _ ∼0 = Any.toSum
joinˡ⁺⁻ _ (1# , _)                 _ ∼+ = Any.toSum
joinˡ⁺⁻ _ (1# , node _ _ _ ∼-)     _ ∼- = λ where
  (left p)          → inj₂ (inj₁ (left p))
  (here p)          → inj₂ (inj₁ (here p))
  (right (left p))  → inj₂ (inj₁ (right p))
  (right (here p))  → inj₁ p
  (right (right p)) → inj₂ (inj₂ p)
joinˡ⁺⁻ _ (1# , node _ _ _ ∼0)     _ ∼- = λ where
  (left p)          → inj₂ (inj₁ (left p))
  (here p)          → inj₂ (inj₁ (here p))
  (right (left p))  → inj₂ (inj₁ (right p))
  (right (here p))  → inj₁ p
  (right (right p)) → inj₂ (inj₂ p)
joinˡ⁺⁻ _ (1# , node⁺ _ _ _ _ _ _) _ ∼- = λ where
  (left (left p))   → inj₂ (inj₁ (left p))
  (left (here p))   → inj₂ (inj₁ (here p))
  (left (right p))  → inj₂ (inj₁ (right (left p)))
  (here p)          → inj₂ (inj₁ (right (here p)))
  (right (left p))  → inj₂ (inj₁ (right (right p)))
  (right (here p))  → inj₁ p
  (right (right p)) → inj₂ (inj₂ p)

----------------------------------------------------------------------
-- joinʳ⁺

joinʳ⁺-here⁺ : (kv : K& V) →
               (l : Tree V l [ kv ]ᵏ hˡ) →
               (r : Tree⁺ V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P kv → Any P (proj₂ (joinʳ⁺ kv l r bal))
joinʳ⁺-here⁺ _ _ (0# , _)                 _  p = here p
joinʳ⁺-here⁺ _ _ (1# , _)                 ∼0 p = here p
joinʳ⁺-here⁺ _ _ (1# , _)                 ∼- p = here p
joinʳ⁺-here⁺ _ _ (1# , node _ _ _ ∼+)     ∼+ p = left (here p)
joinʳ⁺-here⁺ _ _ (1# , node _ _ _ ∼0)     ∼+ p = left (here p)
joinʳ⁺-here⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ p = left (here p)

joinʳ⁺-left⁺ : (kv : K& V) →
               (l : Tree V l [ kv ]ᵏ hˡ) →
               (r : Tree⁺ V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P l → Any P (proj₂ (joinʳ⁺ kv l r bal))
joinʳ⁺-left⁺ _ _ (0# , _)                 _  p = left p
joinʳ⁺-left⁺ _ _ (1# , _)                 ∼0 p = left p
joinʳ⁺-left⁺ _ _ (1# , _)                 ∼- p = left p
joinʳ⁺-left⁺ _ _ (1# , node _ _ _ ∼+)     ∼+ p = left (left p)
joinʳ⁺-left⁺ _ _ (1# , node _ _ _ ∼0)     ∼+ p = left (left p)
joinʳ⁺-left⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ p = left (left p)

joinʳ⁺-right⁺ : (kv : K& V) →
                (l : Tree V l [ kv ]ᵏ hˡ) →
                (r@(_ , rt) : Tree⁺ V [ kv ]ᵏ u hʳ) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P rt → Any P (proj₂ (joinʳ⁺ kv l r bal))
joinʳ⁺-right⁺ _ _ (0# , _)                 _  p                = right p
joinʳ⁺-right⁺ _ _ (1# , _)                 ∼0 p                = right p
joinʳ⁺-right⁺ _ _ (1# , _)                 ∼- p                = right p
joinʳ⁺-right⁺ _ _ (1# , node _ _ _ ∼+)     ∼+ (here p)         = here p
joinʳ⁺-right⁺ _ _ (1# , node _ _ _ ∼+)     ∼+ (left p)         = left (right p)
joinʳ⁺-right⁺ _ _ (1# , node _ _ _ ∼+)     ∼+ (right p)        = right p
joinʳ⁺-right⁺ _ _ (1# , node _ _ _ ∼0)     ∼+ (here p)         = here p
joinʳ⁺-right⁺ _ _ (1# , node _ _ _ ∼0)     ∼+ (left p)         = left (right p)
joinʳ⁺-right⁺ _ _ (1# , node _ _ _ ∼0)     ∼+ (right p)        = right p
joinʳ⁺-right⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ (here p)         = right (here p)
joinʳ⁺-right⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ (left (here p))  = here p
joinʳ⁺-right⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ (left (left p))  = left (right p)
joinʳ⁺-right⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ (left (right p)) = right (left p)
joinʳ⁺-right⁺ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ (right p)        = right (right p)

joinʳ⁺⁻ : (kv : K& V) →
          (l : Tree V l [ kv ]ᵏ hˡ) →
          (r@(_ , rt) : Tree⁺ V [ kv ]ᵏ u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (joinʳ⁺ kv l r bal)) →
          P kv ⊎ Any P l ⊎ Any P rt
joinʳ⁺⁻ _ _ (0# , _)                 _  = Any.toSum
joinʳ⁺⁻ _ _ (1# , _)                 ∼0 = Any.toSum
joinʳ⁺⁻ _ _ (1# , _)                 ∼- = Any.toSum
joinʳ⁺⁻ _ _ (1# , node _ _ _ ∼+)     ∼+ = λ where
  (left (left p))  → inj₂ (inj₁ p)
  (left (here p))  → inj₁ p
  (left (right p)) → inj₂ (inj₂ (left p))
  (here p)         → inj₂ (inj₂ (here p))
  (right p)        → inj₂ (inj₂ (right p))
joinʳ⁺⁻ _ _ (1# , node _ _ _ ∼0)     ∼+ = λ where
  (left (left p))  → inj₂ (inj₁ p)
  (left (here p))  → inj₁ p
  (left (right p)) → inj₂ (inj₂ (left p))
  (here p)         → inj₂ (inj₂ (here p))
  (right p)        → inj₂ (inj₂ (right p))
joinʳ⁺⁻ _ _ (1# , node⁻ _ _ _ _ _ _) ∼+ = λ where
  (left (left p))   → inj₂ (inj₁ p)
  (left (here p))   → inj₁ p
  (left (right p))  → inj₂ (inj₂ (left (left p)))
  (here p)          → inj₂ (inj₂ (left (here p)))
  (right (left p))  → inj₂ (inj₂ (left (right p)))
  (right (here p))  → inj₂ (inj₂ (here p))
  (right (right p)) → inj₂ (inj₂ (right p))

----------------------------------------------------------------------
-- joinˡ⁻

joinˡ⁻-here⁺ : (kv : K& V) →
               (l : Tree⁻ V l [ kv ]ᵏ hˡ) →
               (r : Tree V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P kv → Any P (proj₂ (joinˡ⁻ hˡ kv l r bal))
joinˡ⁻-here⁺ {hˡ = zero}  _ (leaf⁻ _) _  _  p = here p
joinˡ⁻-here⁺ {hˡ = suc _} _ (0# , t₁) t₃ ∼+ p =
  joinʳ⁺-here⁺ _ t₁ (1# , t₃) ∼+ p
joinˡ⁻-here⁺ {hˡ = suc _} _ (0# , _)  _  ∼0 p = here p
joinˡ⁻-here⁺ {hˡ = suc _} _ (0# , _)  _  ∼- p = here p
joinˡ⁻-here⁺ {hˡ = suc _} _ (1# , _)  _  _  p = here p

joinˡ⁻-left⁺ : (kv : K& V) →
               (l@(_ , lt) : Tree⁻ V l [ kv ]ᵏ hˡ) →
               (r : Tree V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P lt → Any P (proj₂ (joinˡ⁻ hˡ kv l r bal))
joinˡ⁻-left⁺ {hˡ = zero}  _ (leaf⁻ _)  _  _  p = left p
joinˡ⁻-left⁺ {hˡ = suc _} _ (0# , t₁)  t₃ ∼+ p =
  joinʳ⁺-left⁺ _ t₁ (1# , t₃) ∼+ p
joinˡ⁻-left⁺ {hˡ = suc _} _ (0# , _)   _  ∼0 p = left p
joinˡ⁻-left⁺ {hˡ = suc _} _ (0# , _)   _  ∼- p = left p
joinˡ⁻-left⁺ {hˡ = suc _} _ (1# , _)   _  _  p = left p

joinˡ⁻-right⁺ : (kv : K& V) →
                (l : Tree⁻ V l [ kv ]ᵏ hˡ) →
                (r : Tree V [ kv ]ᵏ u hʳ) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P r → Any P (proj₂ (joinˡ⁻ hˡ kv l r bal))
joinˡ⁻-right⁺ {hˡ = zero}  _ (leaf⁻ _)  _  _  p = right p
joinˡ⁻-right⁺ {hˡ = suc _} _ (0# , t₁)  t₃ ∼+ p =
  joinʳ⁺-right⁺ _ t₁ (1# , t₃) ∼+ p
joinˡ⁻-right⁺ {hˡ = suc _} _ (0# , _)   _  ∼0 p = right p
joinˡ⁻-right⁺ {hˡ = suc _} _ (0# , _)   _  ∼- p = right p
joinˡ⁻-right⁺ {hˡ = suc _} _ (1# , _)   _  _  p = right p

joinˡ⁻⁻ : (kv : K& V) →
          (l@(_ , lt) : Tree⁻ V l [ kv ]ᵏ hˡ) →
          (r : Tree V [ kv ]ᵏ u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (joinˡ⁻ hˡ kv l r bal)) →
          P kv ⊎ Any P lt ⊎ Any P r
joinˡ⁻⁻ {hˡ = zero}  _ (leaf⁻ _) _  _  = Any.toSum
joinˡ⁻⁻ {hˡ = suc _} _ (0# , t₁) t₃ ∼+ = joinʳ⁺⁻ _ t₁ (1# , t₃) ∼+
joinˡ⁻⁻ {hˡ = suc _} _ (0# , _)  _  ∼0 = Any.toSum
joinˡ⁻⁻ {hˡ = suc _} _ (0# , _)  _  ∼- = Any.toSum
joinˡ⁻⁻ {hˡ = suc _} _ (1# , _)  _  _  = Any.toSum

----------------------------------------------------------------------
-- joinʳ⁻

joinʳ⁻-here⁺ : (kv : K& V) →
               (l : Tree V l [ kv ]ᵏ hˡ) →
               (r : Tree⁻ V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P kv → Any P (proj₂ (joinʳ⁻ hʳ kv l r bal))
joinʳ⁻-here⁺ {hʳ = zero}  _ _  (leaf⁻ _) _  p = here p
joinʳ⁻-here⁺ {hʳ = suc _} _ t₁ (0# , t₃) ∼- p =
  joinˡ⁺-here⁺ _ (1# , t₁) t₃ ∼- p
joinʳ⁻-here⁺ {hʳ = suc _} _ _  (0# , _)  ∼0 p = here p
joinʳ⁻-here⁺ {hʳ = suc _} _ _  (0# , _)  ∼+ p = here p
joinʳ⁻-here⁺ {hʳ = suc _} _ _  (1# , _)  _  p = here p

joinʳ⁻-left⁺ : (kv : K& V) →
               (l : Tree V l [ kv ]ᵏ hˡ) →
               (r : Tree⁻ V [ kv ]ᵏ u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P l → Any P (proj₂ (joinʳ⁻ hʳ kv l r bal))
joinʳ⁻-left⁺ {hʳ = zero}  _ _  (leaf⁻ _) _  p = left p
joinʳ⁻-left⁺ {hʳ = suc _} _ t₁ (0# , t₃) ∼- p =
  joinˡ⁺-left⁺ _ (1# , t₁) t₃ ∼- p
joinʳ⁻-left⁺ {hʳ = suc _} _ _  (0# , _)  ∼0 p = left p
joinʳ⁻-left⁺ {hʳ = suc _} _ _  (0# , _)  ∼+ p = left p
joinʳ⁻-left⁺ {hʳ = suc _} _ _  (1# , _)  _  p = left p

joinʳ⁻-right⁺ : (kv : K& V) →
                (l : Tree V l [ kv ]ᵏ hˡ) →
                (r@(_ , rt) : Tree⁻ V [ kv ]ᵏ u hʳ) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P rt → Any P (proj₂ (joinʳ⁻ hʳ kv l r bal))
joinʳ⁻-right⁺ {hʳ = zero}  _ _  (leaf⁻ _) _  p = right p
joinʳ⁻-right⁺ {hʳ = suc _} _ t₁ (0# , t₃) ∼- p =
  joinˡ⁺-right⁺ _ (1# , t₁) t₃ ∼- p
joinʳ⁻-right⁺ {hʳ = suc _} _ _  (0# , _)  ∼0 p = right p
joinʳ⁻-right⁺ {hʳ = suc _} _ _  (0# , _)  ∼+ p = right p
joinʳ⁻-right⁺ {hʳ = suc _} _ _  (1# , _)  _  p = right p

joinʳ⁻⁻ : (kv : K& V) →
          (l : Tree V l [ kv ]ᵏ hˡ) →
          (r@(_ , rt) : Tree⁻ V [ kv ]ᵏ u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (joinʳ⁻ hʳ kv l r bal)) →
          P kv ⊎ Any P l ⊎ Any P rt
joinʳ⁻⁻ {hʳ = zero}  _ _  (leaf⁻ _) _  = Any.toSum
joinʳ⁻⁻ {hʳ = suc _} _ t₁ (0# , t₃) ∼- = joinˡ⁺⁻ _ (1# , t₁) t₃ ∼-
joinʳ⁻⁻ {hʳ = suc _} _ _  (0# , _)  ∼0 = Any.toSum
joinʳ⁻⁻ {hʳ = suc _} _ _  (0# , _)  ∼+ = Any.toSum
joinʳ⁻⁻ {hʳ = suc _} _ _  (1# , _)  _  = Any.toSum
