open import Relation.Binary using (Preorder)

module Category.Monad.Monotone {ℓ}(pre : Preorder ℓ ℓ ℓ) where

open Preorder pre renaming (Carrier to I)

open import Level
open import Function

open import Data.Product hiding (map)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Closure.Preorder pre hiding (map)

open import Category.Monad.Predicate

open Closed ⦃...⦄

record RawMPMonad (M : Pt I ℓ) : Set (suc ℓ) where

  infixl 1 _≥=_
  field
    return : ∀ {P} → P ⊆ M P
    _≥=_   : ∀ {P Q} → M P ⊆ (□ (P ⇒ M Q) ⇒ M Q)

  {- predicate monad -}
  module _ {P : Pred I ℓ} where

    map : ∀ {Q} → M P ⊆ (□ (P ⇒ Q) ⇒ M Q)
    map m f = m ≥= (λ w p → return (f w p))

    _>>=_ : ∀ {Q : Pred I ℓ} → M P ⊆ (λ i → (P ⊆ M Q) → M Q i)
    c >>= f = c ≥= λ i≤j pj → f pj

    -- infix monadic strength
    infixl 10 _^_
    _^_ : ∀ {Q : Pred I ℓ}⦃ m : Closed Q ⦄ → M P ⊆ (Q ⇒ M (P ∩ Q))
    c ^ qi = c ≥= λ {j} x≤j pj → return (pj , next qi x≤j)

    -- prefix monadic strength; useful when Q cannot be inferred
    ts : ∀ Q ⦃ m : Closed Q ⦄ → M P ⊆ (Q ⇒ M (P ∩ Q))
    ts _ c qi = c ^ qi

  pmonad : RawPMonad {ℓ = ℓ} M
  pmonad = record
    { return? = return
    ; _=<?_ = λ f px → px >>= f }

  {- sequencing -}
  module _ {A : Set ℓ}{P : A → Pred I ℓ} ⦃ mp : ∀ {a} → Closed (P a) ⦄  where
    open import Data.List.All

    instance
      _ = ∼-closed

    sequence′ : ∀ {as}{i k} → i ∼ k →
                All (λ a → □ (M (P a)) i) as → M (λ j → All (λ a → P a j) as) k
    sequence′ _ [] = return []
    sequence′ le (x ∷ xs) = do
      px  , le  ← x le ^ le
      pxs , px  ← sequence′ le xs ^ px
      return (px ∷ pxs)

    sequence : ∀ {as i} → All (λ a → □ (M (P a)) i) as → M (λ j → All (λ a → P a j) as) i
    sequence = sequence′ refl
