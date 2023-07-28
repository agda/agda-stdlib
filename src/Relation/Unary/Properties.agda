------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of constructions over unary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Properties where

open import Data.Product.Base as Product using (_×_; _,_; swap; proj₁; zip′)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Level using (Level)
open import Relation.Binary.Core as Binary
open import Relation.Binary.Definitions hiding (Decidable; Universal; Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Unary
open import Relation.Nullary.Decidable using (yes; no; _⊎-dec_; _×-dec_; ¬?)
open import Function.Base using (id; _$_; _∘_)

private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b

----------------------------------------------------------------------
-- The empty set

∅? : Decidable {A = A} ∅
∅? _ = no λ()

∅-Empty : Empty {A = A} ∅
∅-Empty x ()

∁∅-Universal : Universal {A = A} (∁ ∅)
∁∅-Universal = λ x x∈∅ → x∈∅

----------------------------------------------------------------------
-- The universe

U? : Decidable {A = A} U
U? _ = yes tt

U-Universal : Universal {A = A} U
U-Universal = λ _ → _

∁U-Empty : Empty {A = A} (∁ U)
∁U-Empty = λ x x∈∁U → x∈∁U _

----------------------------------------------------------------------
-- Subset properties

∅-⊆ : (P : Pred A ℓ) → ∅ ⊆ P
∅-⊆ P ()

⊆-U : (P : Pred A ℓ) → P ⊆ U
⊆-U P _ = _

⊆-refl : Reflexive {A = Pred A ℓ} _⊆_
⊆-refl x∈P = x∈P

⊆-reflexive : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐_ _⊆_
⊆-reflexive (P⊆Q , Q⊆P) = P⊆Q

⊆-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊆_ _⊆_ _⊆_
⊆-trans P⊆Q Q⊆R x∈P = Q⊆R (P⊆Q x∈P)

⊆-antisym : Antisymmetric {A = Pred A ℓ} _≐_ _⊆_
⊆-antisym = _,_

⊆-min : Min {B = Pred A ℓ} _⊆_ ∅
⊆-min = ∅-⊆

⊆-max : Max {A = Pred A ℓ} _⊆_ U
⊆-max = ⊆-U

⊂⇒⊆ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂_ _⊆_
⊂⇒⊆ = proj₁

⊂-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊂_ _⊂_ _⊂_
⊂-trans (P⊆Q , Q⊈P) (Q⊆R , R⊈Q) = (λ x∈P → Q⊆R (P⊆Q x∈P)) , (λ R⊆P → R⊈Q (λ x∈R → P⊆Q (R⊆P x∈R)))

⊂-⊆-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊂_ _⊆_ _⊂_
⊂-⊆-trans (P⊆Q , Q⊈P) Q⊆R = (λ x∈P → Q⊆R (P⊆Q x∈P)) , (λ R⊆P → Q⊈P (λ x∈Q → R⊆P (Q⊆R x∈Q)))

⊆-⊂-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊆_ _⊂_ _⊂_
⊆-⊂-trans P⊆Q (Q⊆R , R⊈Q) = (λ x∈P → Q⊆R (P⊆Q x∈P)) , (λ R⊆P → R⊈Q (λ R⊆Q → P⊆Q (R⊆P R⊆Q)))

⊂-respʳ-≐ : _Respectsʳ_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂_ _≐_
⊂-respʳ-≐ (Q⊆R , _) P⊂Q = ⊂-⊆-trans P⊂Q Q⊆R

⊂-respˡ-≐ : _Respectsˡ_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂_ _≐_
⊂-respˡ-≐ (_ , R⊆Q) P⊂Q = ⊆-⊂-trans R⊆Q P⊂Q

⊂-resp-≐ : _Respects₂_ {A = Pred A ℓ} _⊂_ _≐_
⊂-resp-≐ = ⊂-respʳ-≐ , ⊂-respˡ-≐

⊂-irrefl : Irreflexive {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐_ _⊂_
⊂-irrefl (_ , Q⊆P) (_ , Q⊈P) = Q⊈P Q⊆P

⊂-antisym : Antisymmetric {A = Pred A ℓ} _≐_ _⊂_
⊂-antisym (P⊆Q , _) (Q⊆P , _) = ⊆-antisym P⊆Q Q⊆P

⊂-asym : Asymmetric {A = Pred A ℓ} _⊂_
⊂-asym (_ , Q⊈P) = Q⊈P ∘ proj₁

∅-⊆′ : (P : Pred A ℓ) → ∅ ⊆′ P
∅-⊆′ _ _ = λ ()

⊆′-U : (P : Pred A ℓ) → P ⊆′ U
⊆′-U _ _ _ = _

⊆′-refl : Reflexive {A = Pred A ℓ} _⊆′_
⊆′-refl x x∈P = x∈P

⊆′-reflexive : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐′_ _⊆′_
⊆′-reflexive (P⊆Q , Q⊆P) = P⊆Q

⊆′-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊆′_ _⊆′_ _⊆′_
⊆′-trans P⊆Q Q⊆R x x∈P = Q⊆R x (P⊆Q x x∈P)

⊆′-antisym : Antisymmetric {A = Pred A ℓ} _≐′_ _⊆′_
⊆′-antisym = _,_

⊆′-min : Min {B = Pred A ℓ} _⊆′_ ∅
⊆′-min = ∅-⊆′

⊆′-max : Max {A = Pred A ℓ} _⊆′_ U
⊆′-max = ⊆′-U

⊂′⇒⊆′ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂′_ _⊆′_
⊂′⇒⊆′ = proj₁

⊂′-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊂′_ _⊂′_ _⊂′_
⊂′-trans (P⊆Q , Q⊈P) (Q⊆R , R⊈Q) = ⊆′-trans P⊆Q Q⊆R , λ R⊆P → R⊈Q (⊆′-trans R⊆P P⊆Q)

⊂′-⊆′-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊂′_ _⊆′_ _⊂′_
⊂′-⊆′-trans (P⊆Q , Q⊈P) Q⊆R = ⊆′-trans P⊆Q Q⊆R , λ R⊆P → Q⊈P (⊆′-trans Q⊆R R⊆P)

⊆′-⊂′-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _⊆′_ _⊂′_ _⊂′_
⊆′-⊂′-trans P⊆Q (Q⊆R , R⊈Q) = ⊆′-trans P⊆Q Q⊆R , λ R⊆P → R⊈Q (⊆′-trans R⊆P P⊆Q)

⊂′-respʳ-≐′ : _Respectsʳ_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂′_ _≐′_
⊂′-respʳ-≐′ (Q⊆R , _) P⊂Q = ⊂′-⊆′-trans P⊂Q Q⊆R

⊂′-respˡ-≐′ : _Respectsˡ_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂′_ _≐′_
⊂′-respˡ-≐′ (_ , R⊆Q) P⊂Q = ⊆′-⊂′-trans R⊆Q P⊂Q

⊂′-resp-≐′ : _Respects₂_ {A = Pred A ℓ₁} _⊂′_ _≐′_
⊂′-resp-≐′ = ⊂′-respʳ-≐′ , ⊂′-respˡ-≐′

⊂′-irrefl : Irreflexive {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐′_ _⊂′_
⊂′-irrefl (_ , Q⊆P) (_ , Q⊈P) = Q⊈P Q⊆P

⊂′-antisym : Antisymmetric {A = Pred A ℓ} _≐′_ _⊂′_
⊂′-antisym (P⊆Q , _) (Q⊆P , _) = ⊆′-antisym P⊆Q Q⊆P

⊆⇒⊆′ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊆_ _⊆′_
⊆⇒⊆′ P⊆Q _ x∈P = P⊆Q x∈P

⊆′⇒⊆ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊆′_ _⊆_
⊆′⇒⊆ P⊆Q x∈P = P⊆Q _ x∈P

⊂⇒⊂′ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂_ _⊂′_
⊂⇒⊂′ = Product.map ⊆⇒⊆′ (_∘ ⊆′⇒⊆)

⊂′⇒⊂ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊂′_ _⊂_
⊂′⇒⊂ = Product.map ⊆′⇒⊆ (_∘ ⊆⇒⊆′)

----------------------------------------------------------------------
-- Equality properties

≐-refl : Reflexive {A = Pred A ℓ} _≐_
≐-refl = id , id

≐-sym : Sym {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐_ _≐_
≐-sym = swap

≐-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _≐_ _≐_ _≐_
≐-trans = zip′ (λ P⊆Q Q⊆R x∈P → Q⊆R (P⊆Q x∈P)) (λ Q⊆P R⊆Q x∈R → Q⊆P (R⊆Q x∈R))

≐′-refl : Reflexive {A = Pred A ℓ} _≐′_
≐′-refl = (λ _ → id) , (λ _ → id)

≐′-sym : Sym {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐′_ _≐′_
≐′-sym = swap

≐′-trans : Trans {A = Pred A ℓ₁} {B = Pred A ℓ₂} {C = Pred A ℓ₃} _≐′_ _≐′_ _≐′_
≐′-trans = zip′ (λ P⊆Q Q⊆R x x∈P → Q⊆R x (P⊆Q x x∈P)) λ Q⊆P R⊆Q x x∈R → Q⊆P x (R⊆Q x x∈R)

≐⇒≐′ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐_ _≐′_
≐⇒≐′ = Product.map ⊆⇒⊆′ ⊆⇒⊆′

≐′⇒≐ : Binary._⇒_ {A = Pred A ℓ₁} {B = Pred A ℓ₂} _≐′_ _≐_
≐′⇒≐ = Product.map ⊆′⇒⊆ ⊆′⇒⊆

----------------------------------------------------------------------
-- Decidability properties

∁? : {P : Pred A ℓ} → Decidable P → Decidable (∁ P)
∁? P? x = ¬? (P? x)

_∪?_ : {P : Pred A ℓ₁} {Q : Pred A ℓ₂} →
       Decidable P → Decidable Q → Decidable (P ∪ Q)
_∪?_ P? Q? x = (P? x) ⊎-dec (Q? x)

_∩?_ : {P : Pred A ℓ₁} {Q : Pred A ℓ₂} →
       Decidable P → Decidable Q → Decidable (P ∩ Q)
_∩?_ P? Q? x = (P? x) ×-dec (Q? x)

_×?_ : {P : Pred A ℓ₁} {Q : Pred B ℓ₂} →
       Decidable P → Decidable Q → Decidable (P ⟨×⟩ Q)
_×?_ P? Q? (a , b) = (P? a) ×-dec (Q? b)

_⊙?_ : {P : Pred A ℓ₁} {Q : Pred B ℓ₂} →
       Decidable P → Decidable Q → Decidable (P ⟨⊙⟩ Q)
_⊙?_ P? Q? (a , b) = (P? a) ⊎-dec (Q? b)

_⊎?_ : {P : Pred A ℓ} {Q : Pred B ℓ} →
       Decidable P → Decidable Q → Decidable (P ⟨⊎⟩ Q)
_⊎?_ P? Q? (inj₁ a) = P? a
_⊎?_ P? Q? (inj₂ b) = Q? b

_~? : {P : Pred (A × B) ℓ} → Decidable P → Decidable (P ~)
_~? P? = P? ∘ swap

----------------------------------------------------------------------
-- Irrelevant properties

U-irrelevant : Irrelevant {A = A} U
U-irrelevant a b = refl

∁-irrelevant : (P : Pred A ℓ) → Irrelevant (∁ P)
∁-irrelevant P a b = refl
