------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation
------------------------------------------------------------------------

module Data.List.Relation.Permutation.Inductive.Properties where

open import Data.List.Base as List
open import Data.List.Relation.Permutation.Inductive
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; ∃ ; ∃₂)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; _≢_)
open import Function

open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties as Listₚ hiding (map-cong)


module _ {a} {A : Set a} where

  sym-self-inverse : ∀ {l₁ l₂ : List A} (p : l₁ ⇿ l₂) → sym (sym p) ≡ p
  sym-self-inverse refl         = refl
  sym-self-inverse (prep x p)
    rewrite sym-self-inverse p  = refl
  sym-self-inverse (swap x y p)
    rewrite sym-self-inverse p  = refl
  sym-self-inverse (trans p₁ p₂)
    rewrite sym-self-inverse p₁
          | sym-self-inverse p₂ = refl

  -------------------------------------------------------------------------------------
  -- _++_

  ++ʳ : ∀ {l₁ l₂ : List A} l → l₁ ⇿ l₂ → l₁ ++ l ⇿ l₂ ++ l
  ++ʳ l refl         = refl
  ++ʳ l (prep x p)   = prep x (++ʳ l p)
  ++ʳ l (swap x y p) = swap x y (++ʳ l p)
  ++ʳ l (trans p p₁) = trans (++ʳ l p) (++ʳ l p₁)

  ++ˡ : ∀ {l₁ l₂ : List A} l → l₁ ⇿ l₂ → l ++ l₁ ⇿ l ++ l₂
  ++ˡ [] p      = p
  ++ˡ (x ∷ l) p = prep x (++ˡ l p)

  ++-cong : ∀ {l₁ l₂ j₁ j₂ : List A} → l₁ ⇿ l₂ → j₁ ⇿ j₂ → l₁ ++ j₁ ⇿ l₂ ++ j₂
  ++-cong {l₁} {l₂} {j₁} {j₂} pl pj = begin
    l₁ ++ j₁ p⟨ ++ˡ l₁ pj ⟩
    l₁ ++ j₂ p⟨ ++ʳ _ pl ⟩
    l₂ ++ j₂ ∎
    where open PReasoning

  -- this lemma allows focusing on a small portion of the lists
  zoom : ∀ h {t l₁ l₂ : List A} → l₁ ⇿ l₂ → h ++ l₁ ++ t ⇿ h ++ l₂ ++ t
  zoom h {t} = ++ˡ h ∘ ++ʳ t

  inject : ∀ l₁ l₂ {j₁ j₂ : List A} x → l₁ ⇿ l₂ → j₁ ⇿ j₂ → l₁ ++ x ∷ j₁ ⇿ l₂ ++ x ∷ j₂
  inject l₁ _ x pl pj = trans (++ˡ l₁ (prep x pj)) (++ʳ _ pl)

  shift : ∀ (l₁ l₂ : List A) x → l₁ ++ x ∷ l₂ ⇿ x ∷ l₁ ++ l₂
  shift [] l₂ x        = refl
  shift (x₁ ∷ l₁) l₂ x = begin
    x₁ ∷ (l₁ ++ x ∷ l₂) <⟨ shift l₁ l₂ x ⟩
    x₁ ∷ x ∷ l₁ ++ l₂   <<⟨ refl ⟩
    x ∷ x₁ ∷ l₁ ++ l₂   ∎
    where open PReasoning

  ∷⇒∷ʳ : ∀ (x : A) l → x ∷ l ⇿ l ∷ʳ x
  ∷⇒∷ʳ x l with sym $ shift l [] x
  ... | res rewrite ++-identityʳ l = res

  ++-swap : ∀ (l₁ l₂ : List A) → l₁ ++ l₂ ⇿ l₂ ++ l₁
  ++-swap [] l₂ rewrite ++-identityʳ l₂ = refl
  ++-swap (x ∷ l₁) l₂ with ++ʳ l₁ $ ∷⇒∷ʳ x l₂
  ... | res rewrite ++-assoc l₂ [ x ] l₁  = trans (prep x (++-swap l₁ l₂)) res

  -------------------------------------------------------------------------------------
  -- respectful lemmas

  open import Data.List.Properties
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties

  Any-resp-⇿ : ∀ {ℓ} {P : A → Set ℓ} → (Any P) Respects _⇿_
  Any-resp-⇿ refl         wit                 = wit
  Any-resp-⇿ (prep x p)   (here px)           = here px
  Any-resp-⇿ (prep x p)   (there wit)         = there (Any-resp-⇿ p wit)
  Any-resp-⇿ (swap x y p) (here px)           = there (here px)
  Any-resp-⇿ (swap x y p) (there (here px))   = here px
  Any-resp-⇿ (swap x y p) (there (there wit)) = there (there (Any-resp-⇿ p wit))
  Any-resp-⇿ (trans p p₁) wit                 = Any-resp-⇿ p₁ (Any-resp-⇿ p wit)

  open import Data.List.All

  All-resp-⇿ : ∀ {ℓ} {P : A → Set ℓ} → (All P) Respects _⇿_
  All-resp-⇿ refl wit                     = wit
  All-resp-⇿ (prep x p) (px ∷ wit)        = px ∷ All-resp-⇿ p wit
  All-resp-⇿ (swap x y p) (px ∷ py ∷ wit) = py ∷ px ∷ All-resp-⇿ p wit
  All-resp-⇿ (trans p₁ p₂) wit            = All-resp-⇿ p₂ (All-resp-⇿ p₁ wit)

  ⇿⇒∈ : ∀ l₁ {x l₂ l} → l₁ ++ x ∷ l₂ ⇿ l → x ∈ l
  ⇿⇒∈ l₁ p = Any-resp-⇿ p (∈-witness _ l₁)

  --------------------------------------------------------------------------------------
  -- inversion lemmas

  private
    -- the helper to prove the main inversion lemmas
    -- this lemma is massive because we need to perform a dependent induction.

    drop-mid′ : ∀ l₁ l₂ {l₃ l₄ : List A} {x : A}
                     {l′ l″ : List A} →
                     l′ ⇿ l″ →
                     l₁ ++ x ∷ l₃ ≡ l′ → l₂ ++ x ∷ l₄ ≡ l″ → l₁ ++ l₃ ⇿ l₂ ++ l₄
    drop-mid′ l₁ l₂ refl eq₁ eq₂         = ++-≡-inv l₁ l₂ (≡.trans eq₁ $ ≡.sym eq₂)
      where ++-≡-inv : ∀ l₁ l₂ {l₃ l₄ : List A} {x : A} →
                         l₁ ++ x ∷ l₃ ≡ l₂ ++ x ∷ l₄ → l₁ ++ l₃ ⇿ l₂ ++ l₄
            ++-≡-inv []       []       refl = refl
            ++-≡-inv []       (x ∷ l₂) refl = shift l₂ _ _
            ++-≡-inv (x ∷ l₁) []       refl = sym $ shift l₁ _ _
            ++-≡-inv (x ∷ l₁) (x₁ ∷ l₂) eq with ∷-injective eq
            ... | refl , eq′                = prep x (++-≡-inv l₁ l₂ eq′)

    drop-mid′ l₁ l₂ (prep x p) eq₁ eq₂   = helper l₁ l₂ p eq₁ eq₂
      where helper : ∀ {x : A} {l₁ l₂ l₃ l₄ : List A}
                       {x₁ : A} (l₅ l₆ : List A) →
                       l₁ ⇿ l₂ →
                       l₅ ++ x₁ ∷ l₃ ≡ x ∷ l₁ →
                       l₆ ++ x₁ ∷ l₄ ≡ x ∷ l₂ → l₅ ++ l₃ ⇿ l₆ ++ l₄
            helper []       []        p refl refl = p
            helper []       (x ∷ l₆)  p refl refl = trans p (shift l₆ _ _)
            helper (x ∷ l₅) []        p refl refl = trans (sym $ shift l₅ _ _) p
            helper (x ∷ l₅) (.x ∷ l₆) p refl refl = prep x (drop-mid′ l₅ l₆ p refl refl)

    drop-mid′ l₁ l₂ (swap x y p) eq₁ eq₂ = helper l₁ l₂ p eq₁ eq₂
      where open PReasoning
            helper : ∀ {x y : A} {l₁ l₂ l₃ l₄ : List A}
                       {x₁ : A} (l₅ l₆ : List A) →
                       l₁ ⇿ l₂ →
                       l₅ ++ x₁ ∷ l₃ ≡ x ∷ y ∷ l₁ →
                       l₆ ++ x₁ ∷ l₄ ≡ y ∷ x ∷ l₂ → l₅ ++ l₃ ⇿ l₆ ++ l₄
            helper []            []             p refl refl  = prep _ p
            helper []            (x ∷ [])       p refl refl  = prep x p
            helper []            (x ∷ x₁ ∷ l₆)  p refl refl  = prep x (trans p $ shift l₆ _ _)
            helper (x ∷ [])      []             p refl refl  = prep x p
            helper (x ∷ x₁ ∷ l₅) []             p refl refl  = prep x (trans (sym $ shift l₅ _ _) p)
            helper (x ∷ [])      (.x ∷ [])      p refl refl  = prep x p
            helper {l₁ = l₁} {l₂} {l₃} {l₄}
                   (x ∷ [])      (y ∷ .x ∷ l₆)  p refl refl  = begin
              x ∷ l₁             <⟨ p ⟩
              x ∷ (l₆ ++ y ∷ l₄) <⟨ shift l₆ _ _ ⟩
              x ∷ y ∷ l₆ ++ l₄   <<⟨ refl ⟩
              y ∷ x ∷ l₆ ++ l₄   ∎
            helper {l₁ = l₁} {l₂} {l₃} {l₄}
                   (x ∷ y ∷ l₅)  (.y ∷ [])      p refl refl  = begin
              x ∷ y ∷ l₅ ++ l₃   <<⟨ refl ⟩
              y ∷ (x ∷ l₅ ++ l₃) <⟨ sym $ shift l₅ _ _ ⟩
              y ∷ (l₅ ++ x ∷ l₃) <⟨ p ⟩
              y ∷ l₂             ∎
            helper (x ∷ x₂ ∷ l₅) (.x₂ ∷ .x ∷ l₆) p refl refl = swap _ _ (drop-mid′ l₅ l₆ p refl refl)

    drop-mid′ l₁ l₂ {l₃} {l₄} {x}
                   (trans {l₂ = l′} p₁ p₂) eq₁ eq₂ = helper $ ∈-∃++ _ $ ⇒x∈l′ eq₁ p₁
      where ⇒x∈l′ : ∀ {l} → l₁ ++ x ∷ l₃ ≡ l → l ⇿ l′ → x ∈ l′
            ⇒x∈l′ refl p = ⇿⇒∈ l₁ p
            helper : ∃₂ (λ h t → l′ ≡ h ++ x ∷ t) → l₁ ++ l₃ ⇿ l₂ ++ l₄
            helper (h , t , eq₃) = trans (drop-mid′ l₁ h p₁ eq₁ (≡.sym eq₃))
                                         (drop-mid′ h l₂ p₂ (≡.sym eq₃) eq₂)

  -- the main inversion lemmas

  drop-mid : ∀ l₁ l₂ {l₃ l₄ x} → l₁ ++ x ∷ l₃ ⇿ l₂ ++ x ∷ l₄ → l₁ ++ l₃ ⇿ l₂ ++ l₄
  drop-mid l₁ l₂ {l₃} {l₄} {x} p
    with l₁ ++ x ∷ l₃ | l₂ ++ x ∷ l₄ | ≡.inspect (l₁ ++_) (x ∷ l₃) | ≡.inspect (l₂ ++_) (x ∷ l₄)
  ... | l′ | l″ | ≡.[ eq₁ ] | ≡.[ eq₂ ] = drop-mid′ l₁ l₂ p eq₁ eq₂

  drop-one-side : ∀ l₁ {l₂ l x} → x ∷ l ⇿ l₁ ++ x ∷ l₂ → l ⇿ l₁ ++ l₂
  drop-one-side l₁ = drop-mid [] l₁

  drop-∷ : ∀ {l₁ l₂ x} → x ∷ l₁ ⇿ x ∷ l₂ → l₁ ⇿ l₂
  drop-∷ = drop-one-side []

  -----------------------------------------------------------------------------------------------
  --- equivalence to bag equality

  open import Data.List.Relation.BagAndSetEquality

  ⇿⇒bag-equality : ∀ {l₁ l₂} → l₁ ⇿ l₂ → l₁ ∼[ bag ] l₂
  ⇿⇒bag-equality p = record
    { to         = ≡.→-to-⟶ (Any-resp-⇿ p)
    ; from       = ≡.→-to-⟶ (Any-resp-⇿ (sym p))
    ; inverse-of = record
      { left-inverse-of  = inverse p
      ; right-inverse-of = right-inv p
      }
    }
    where inverse : ∀ {l₁ l₂ : List A} (p : l₁ ⇿ l₂)
                       {z : A} (x : z ∈ l₁) →
                       Any-resp-⇿ (sym p) (Any-resp-⇿ p x) ≡ x
          inverse refl x∈l₁                         = refl
          inverse (prep _ _) (here refl)            = refl
          inverse (prep _ p) (there x∈l₁)
            rewrite inverse p x∈l₁                  = refl
          inverse (swap x y p) (here refl)          = refl
          inverse (swap x y p) (there (here refl))  = refl
          inverse (swap x y p) (there (there x∈l₁))
            rewrite inverse p x∈l₁                  = refl
          inverse (trans p₁ p₂) x∈l₁
            rewrite inverse p₂ (Any-resp-⇿ p₁ x∈l₁)
                  | inverse p₁ x∈l₁                 = refl

          right-inv : ∀ {l₁ l₂ : List A} (p : l₁ ⇿ l₂)
                        {z : A} (x : Any (_≡_ z) l₂) →
                        Any-resp-⇿ p (Any-resp-⇿ (sym p) x) ≡ x
          right-inv p with inverse $ sym p
          ... | res rewrite sym-self-inverse p = res


-------------------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} where

  map-cong : ∀ {l₁ l₂} → (f : A → B) → l₁ ⇿ l₂ → List.map f l₁ ⇿ List.map f l₂
  map-cong f refl          = refl
  map-cong f (prep x p)    = prep _ (map-cong f p)
  map-cong f (swap x y p)  = swap _ _ (map-cong f p)
  map-cong f (trans p₁ p₂) = trans (map-cong f p₁) (map-cong f p₂)
