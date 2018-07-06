------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic lemmas showing that various types are related (isomorphic or
-- equivalent or…)
------------------------------------------------------------------------

module Function.Related.TypeIsomorphisms where

open import Algebra
import Algebra.FunctionProperties as FP
import Algebra.Operations.Semiring as SemiringOperations
import Algebra.RingSolver.Natural-coefficients
open import Algebra.Structures
open import Data.Empty
open import Data.Nat as Nat using (zero; suc)
open import Data.Product as Prod hiding (swap)
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum as Sum
open import Data.Sum.Properties using (swap-involutive)
open import Data.Sum.Relation.Pointwise
open import Data.Unit
open import Level hiding (zero; suc)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; Equivalence)
open import Function.Inverse as Inv using (_↔_; Inverse; inverse)
open import Function.Related as Related
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec using (True)

------------------------------------------------------------------------
-- Properties of Σ and _×_

Σ-assoc : ∀ {a b c}
            {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = record
  { to         = P.→-to-⟶ λ p →
                   proj₁ (proj₁ p) , (proj₂ (proj₁ p) , proj₂ p)
  ; from       = P.→-to-⟶ _
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

------------------------------------------------------------------------
-- ⊥, ⊤, _×_ and _⊎_ form a commutative semiring

×-CommutativeMonoid : Symmetric-kind → (ℓ : Level) →
                      CommutativeMonoid _ _
×-CommutativeMonoid k ℓ = record
  { Carrier             = Set ℓ
  ; _≈_                 = Related ⌊ k ⌋
  ; _∙_                 = _×_
  ; ε                   = Lift ℓ ⊤
  ; isCommutativeMonoid = record
    { isSemigroup   = record
      { isEquivalence = Setoid.isEquivalence $ Related.setoid k ℓ
      ; assoc         = λ _ _ _ → ↔⇒ Σ-assoc
      ; ∙-cong        = _×-cong_
      }
    ; identityˡ = λ A → ↔⇒ $ ×-identityˡ A
    ; comm      = λ A B → ↔⇒ $ ×-comm A B
    }
  }
  where
  open FP _↔_

  ×-identityˡ : LeftIdentity (Lift ℓ ⊤) _×_
  ×-identityˡ _ = inverse proj₂ (_ ,_) (λ _ → P.refl) (λ _ → P.refl)

  ×-comm : Commutative _×_
  ×-comm _ _ = inverse Prod.swap Prod.swap (λ _ → P.refl) (λ _ → P.refl)

⊎-CommutativeMonoid : Symmetric-kind → (ℓ : Level) →
                      CommutativeMonoid _ _
⊎-CommutativeMonoid k ℓ = record
  { Carrier             = Set ℓ
  ; _≈_                 = Related ⌊ k ⌋
  ; _∙_                 = _⊎_
  ; ε                   = Lift ℓ ⊥
  ; isCommutativeMonoid = record
    { isSemigroup   = record
      { isEquivalence = Setoid.isEquivalence $ Related.setoid k ℓ
      ; assoc         = λ A B C → ↔⇒ $ ⊎-assoc A B C
      ; ∙-cong        = _⊎-cong_
      }
    ; identityˡ = λ A → ↔⇒ $ ⊎-identityˡ A
    ; comm      = λ A B → ↔⇒ $ ⊎-comm A B
    }
  }
  where
  open FP _↔_

  ⊎-identityˡ : LeftIdentity (Lift ℓ ⊥) _⊎_
  ⊎-identityˡ A = record
    { to         = P.→-to-⟶ [ (λ ()) ∘′ lower , id ]
    ; from       = P.→-to-⟶ inj₂
    ; inverse-of = record
      { right-inverse-of = λ _ → P.refl
      ; left-inverse-of  = [ ⊥-elim ∘ lower , (λ _ → P.refl) ]
      }
    }

  ⊎-assoc : Associative _⊎_
  ⊎-assoc A B C = record
    { to         = P.→-to-⟶ [ [ inj₁ , inj₂ ∘ inj₁ ] , inj₂ ∘ inj₂ ]
    ; from       = P.→-to-⟶ [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ] ]
    ; inverse-of = record
      { left-inverse-of  = [ [ (λ _ → P.refl) , (λ _ → P.refl) ] , (λ _ → P.refl) ]
      ; right-inverse-of = [ (λ _ → P.refl) , [ (λ _ → P.refl) , (λ _ → P.refl) ] ]
      }
    }

  ⊎-comm : Commutative _⊎_
  ⊎-comm _ _ = inverse swap swap swap-involutive swap-involutive

×⊎-CommutativeSemiring : Symmetric-kind → (ℓ : Level) →
                         CommutativeSemiring (Level.suc ℓ) ℓ
×⊎-CommutativeSemiring k ℓ = record
  { Carrier               = Set ℓ
  ; _≈_                   = Related ⌊ k ⌋
  ; _+_                   = _⊎_
  ; _*_                   = _×_
  ; 0#                    = Lift ℓ ⊥
  ; 1#                    = Lift ℓ ⊤
  ; isCommutativeSemiring = isCommutativeSemiring
  }
  where
  open CommutativeMonoid
  open FP _↔_

  ×-zeroˡ : LeftZero (Lift ℓ ⊥) _×_
  ×-zeroˡ A = inverse proj₁ (⊥-elim ∘′ lower)
                     (⊥-elim ∘ lower ∘ proj₁) (⊥-elim ∘ lower)

  ×-distribʳ-⊎ : _×_ DistributesOverʳ _⊎_
  ×-distribʳ-⊎ A B C = inverse to from from∘to to∘from
    where
    to : (B ⊎ C) × A → B × A ⊎ C × A
    to = uncurry [ curry inj₁ , curry inj₂ ]

    from : B × A ⊎ C × A → (B ⊎ C) × A
    from = [ Prod.map inj₁ id , Prod.map inj₂ id ]

    from∘to : ∀ x → from (to x) ≡ x
    from∘to = uncurry [ (λ _ _ → P.refl) , (λ _ _ → P.refl) ]

    to∘from : ∀ x → to (from x) ≡ x
    to∘from = [ (λ _ → P.refl) , (λ _ → P.refl) ]

  abstract

    -- If isCommutativeSemiring is made concrete, then it takes much
    -- more time to type-check coefficient-dec (at the time of
    -- writing, on a given system, using certain Agda options).

    isCommutativeSemiring :
      IsCommutativeSemiring (Related ⌊ k ⌋) _⊎_ _×_ (Lift ℓ ⊥) (Lift ℓ ⊤)
    isCommutativeSemiring = record
      { +-isCommutativeMonoid = isCommutativeMonoid $
                                  ⊎-CommutativeMonoid k ℓ
      ; *-isCommutativeMonoid = isCommutativeMonoid $
                                  ×-CommutativeMonoid k ℓ
      ; distribʳ              = λ A B C → ↔⇒ $ ×-distribʳ-⊎ A B C
      ; zeroˡ                 = λ A → ↔⇒ $ ×-zeroˡ A
      }

private

  -- A decision procedure used by the solver below.

  coefficient-dec :
    ∀ s ℓ →
    let open CommutativeSemiring (×⊎-CommutativeSemiring s ℓ)
        open SemiringOperations semiring renaming (_×_ to Times)
    in

    ∀ m n → Dec (Times m 1# ∼[ ⌊ s ⌋ ] Times n 1#)

  coefficient-dec equivalence ℓ m n with m | n
  ... | zero  | zero  = yes (Eq.equivalence id id)
  ... | zero  | suc _ = no  (λ eq → lower (Equivalence.from eq ⟨$⟩ inj₁ _))
  ... | suc _ | zero  = no  (λ eq → lower (Equivalence.to   eq ⟨$⟩ inj₁ _))
  ... | suc _ | suc _ = yes (Eq.equivalence (λ _ → inj₁ _) (λ _ → inj₁ _))
  coefficient-dec bijection ℓ m n = Dec.map′ to (from m n) (Nat._≟_ m n)
    where
    open CommutativeSemiring (×⊎-CommutativeSemiring bijection ℓ)
      using (1#; semiring)
    open SemiringOperations semiring renaming (_×_ to Times)

    to : ∀ {m n} → m ≡ n → Times m 1# ↔ Times n 1#
    to {m} P.refl = Times m 1# ∎
      where open Related.EquationalReasoning

    from : ∀ m n → Times m 1# ↔ Times n 1# → m ≡ n
    from zero    zero    _   = P.refl
    from zero    (suc n) 0↔+ = ⊥-elim $ lower $ Inverse.from 0↔+ ⟨$⟩ inj₁ _
    from (suc m) zero    +↔0 = ⊥-elim $ lower $ Inverse.to   +↔0 ⟨$⟩ inj₁ _
    from (suc m) (suc n) +↔+ = P.cong suc $ from m n (pred↔pred +↔+)
      where
      open P.≡-Reasoning

      ↑⊤ : Set ℓ
      ↑⊤ = Lift _ ⊤

      inj₁≢inj₂ : ∀ {A : Set ℓ} {x : ↑⊤ ⊎ A} {y} →
                  x ≡ inj₂ y → x ≡ inj₁ _ → ⊥
      inj₁≢inj₂ {x = x} {y} eq₁ eq₂ =
        P.subst [ const ⊥ , const ⊤ ] (begin
          inj₂ y  ≡⟨ P.sym eq₁ ⟩
          x       ≡⟨ eq₂ ⟩
          inj₁ _  ∎)
          _

      g′ : {A B : Set ℓ}
           (f : (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B)) (x : A) (y z : ↑⊤ ⊎ B) →
           Inverse.to f ⟨$⟩ inj₂ x ≡ y →
           Inverse.to f ⟨$⟩ inj₁ _ ≡ z →
           B
      g′ _ _ (inj₂ y)       _  _   _   = y
      g′ _ _ (inj₁ _) (inj₂ z) _   _   = z
      g′ f _ (inj₁ _) (inj₁ _) eq₁ eq₂ = ⊥-elim $
        inj₁≢inj₂ (Inverse.to-from f eq₁) (Inverse.to-from f eq₂)

      g : {A B : Set ℓ} → (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B) → A → B
      g f x = g′ f x _ _ P.refl P.refl

      g′∘g′ : ∀ {A B} (f : (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B))
              x y₁ z₁ y₂ z₂ eq₁₁ eq₂₁ eq₁₂ eq₂₂ →
              g′ (reverse f) (g′ f x y₁ z₁ eq₁₁ eq₂₁) y₂ z₂ eq₁₂ eq₂₂ ≡
              x
      g′∘g′ f x (inj₂ y₁) _ (inj₂ y₂) _ eq₁₁ _ eq₁₂ _ =
        P.cong [ const y₂ , id ] (begin
          inj₂ y₂                     ≡⟨ P.sym eq₁₂ ⟩
          Inverse.from f ⟨$⟩ inj₂ y₁  ≡⟨ Inverse.to-from f eq₁₁ ⟩
          inj₂ x                      ∎)
      g′∘g′ f x (inj₁ _) (inj₂ _) (inj₁ _) (inj₂ z₂) eq₁₁ _ _ eq₂₂ =
        P.cong [ const z₂ , id ] (begin
          inj₂ z₂                    ≡⟨ P.sym eq₂₂ ⟩
          Inverse.from f ⟨$⟩ inj₁ _  ≡⟨ Inverse.to-from f eq₁₁ ⟩
          inj₂ x                     ∎)
      g′∘g′ f _ (inj₂ y₁) _ (inj₁ _) _ eq₁₁ _ eq₁₂ _ =
        ⊥-elim $ inj₁≢inj₂ (Inverse.to-from f eq₁₁) eq₁₂
      g′∘g′ f _ (inj₁ _) (inj₂ z₁) (inj₂ y₂) _ _ eq₂₁ eq₁₂ _ =
        ⊥-elim $ inj₁≢inj₂ eq₁₂ (Inverse.to-from f eq₂₁)
      g′∘g′ f _ (inj₁ _) (inj₂ _) (inj₁ _) (inj₁ _) eq₁₁ _ _ eq₂₂ =
        ⊥-elim $ inj₁≢inj₂ (Inverse.to-from f eq₁₁) eq₂₂
      g′∘g′ f _ (inj₁ _) (inj₁ _) _ _ eq₁₁ eq₂₁ _ _ =
        ⊥-elim $ inj₁≢inj₂ (Inverse.to-from f eq₁₁)
                           (Inverse.to-from f eq₂₁)

      g∘g : ∀ {A B} (f : (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B)) x →
            g (reverse f) (g f x) ≡ x
      g∘g f x = g′∘g′ f x _ _ _ _ P.refl P.refl P.refl P.refl

      pred↔pred : {A B : Set ℓ} → (↑⊤ ⊎ A) ↔ (↑⊤ ⊎ B) → A ↔ B
      pred↔pred X⊎↔X⊎ = inverse (g X⊎↔X⊎) (g (reverse X⊎↔X⊎))
                                (g∘g X⊎↔X⊎) (g∘g (reverse X⊎↔X⊎))

module Solver s {ℓ} =
  Algebra.RingSolver.Natural-coefficients
    (×⊎-CommutativeSemiring s ℓ)
    (coefficient-dec s ℓ)

private

  -- A test of the solver above.

  test : {ℓ : Level} (A B C : Set ℓ) →
         (Lift ℓ ⊤ × A × (B ⊎ C)) ↔ (A × B ⊎ C × (Lift ℓ ⊥ ⊎ A))
  test = solve 3 (λ A B C → con 1 :* (A :* (B :+ C)) :=
                            A :* B :+ C :* (con 0 :+ A))
                 Inv.id
    where open Solver bijection

------------------------------------------------------------------------
-- Some reordering lemmas

ΠΠ↔ΠΠ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        ((x : A) (y : B) → P x y) ↔ ((y : B) (x : A) → P x y)
ΠΠ↔ΠΠ _ = inverse flip flip (λ _ → P.refl) (λ _ → P.refl)

∃∃↔∃∃ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        (∃₂ λ x y → P x y) ↔ (∃₂ λ y x → P x y)
∃∃↔∃∃ P = inverse to from (λ _ → P.refl) (λ _ → P.refl)
  where
  to : (∃₂ λ x y → P x y) → (∃₂ λ y x → P x y)
  to (x , y , Pxy) = (y , x , Pxy)

  from : (∃₂ λ y x → P x y) → (∃₂ λ x y → P x y)
  from (y , x , Pxy) = (x , y , Pxy)

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π↔Π : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) ↔ ({x : A} → B x)
Π↔Π = inverse (λ f {x} → f x) (λ f x → f) (λ _ → P.refl) (λ _ → P.refl)

------------------------------------------------------------------------
-- _→_ preserves the symmetric relations

_→-cong-⇔_ :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
A⇔B →-cong-⇔ C⇔D = Eq.equivalence
  (λ f x → Equivalence.to   C⇔D ⟨$⟩ f (Equivalence.from A⇔B ⟨$⟩ x))
  (λ f x → Equivalence.from C⇔D ⟨$⟩ f (Equivalence.to   A⇔B ⟨$⟩ x))

→-cong :
  ∀ {a b c d} →
  P.Extensionality a c → P.Extensionality b d →
  ∀ {k} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ∼[ ⌊ k ⌋ ] B → C ∼[ ⌊ k ⌋ ] D → (A → C) ∼[ ⌊ k ⌋ ] (B → D)
→-cong extAC extBD {equivalence} A⇔B C⇔D = A⇔B →-cong-⇔ C⇔D
→-cong extAC extBD {bijection}   A↔B C↔D = record
  { to         = Equivalence.to   A→C⇔B→D
  ; from       = Equivalence.from A→C⇔B→D
  ; inverse-of = record
    { left-inverse-of  = λ f → extAC λ x → begin
        Inverse.from C↔D ⟨$⟩ (Inverse.to C↔D ⟨$⟩
          f (Inverse.from A↔B ⟨$⟩ (Inverse.to A↔B ⟨$⟩ x)))  ≡⟨ Inverse.left-inverse-of C↔D _ ⟩
        f (Inverse.from A↔B ⟨$⟩ (Inverse.to A↔B ⟨$⟩ x))     ≡⟨ P.cong f $ Inverse.left-inverse-of A↔B x ⟩
        f x                                                 ∎
    ; right-inverse-of = λ f → extBD λ x → begin
        Inverse.to C↔D ⟨$⟩ (Inverse.from C↔D ⟨$⟩
          f (Inverse.to A↔B ⟨$⟩ (Inverse.from A↔B ⟨$⟩ x)))  ≡⟨ Inverse.right-inverse-of C↔D _ ⟩
        f (Inverse.to A↔B ⟨$⟩ (Inverse.from A↔B ⟨$⟩ x))     ≡⟨ P.cong f $ Inverse.right-inverse-of A↔B x ⟩
        f x                                                 ∎
    }
  }
  where
  open P.≡-Reasoning
  A→C⇔B→D = ↔⇒ A↔B →-cong-⇔ ↔⇒ C↔D

------------------------------------------------------------------------
-- ¬_ preserves the symmetric relations

¬-cong-⇔ : ∀ {a b} {A : Set a} {B : Set b} →
           A ⇔ B → (¬ A) ⇔ (¬ B)
¬-cong-⇔ A⇔B = A⇔B →-cong-⇔ (⊥ ∎)
  where open Related.EquationalReasoning

¬-cong : ∀ {a b} →
         P.Extensionality a Level.zero →
         P.Extensionality b Level.zero →
         ∀ {k} {A : Set a} {B : Set b} →
         A ∼[ ⌊ k ⌋ ] B → (¬ A) ∼[ ⌊ k ⌋ ] (¬ B)
¬-cong extA extB A≈B = →-cong extA extB A≈B (⊥ ∎)
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⇔_ preserves _⇔_

-- The type of the following proof is a bit more general.

Related-cong :
  ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ∼[ ⌊ k ⌋ ] B → C ∼[ ⌊ k ⌋ ] D → (A ∼[ ⌊ k ⌋ ] C) ⇔ (B ∼[ ⌊ k ⌋ ] D)
Related-cong {A = A} {B} {C} {D} A≈B C≈D =
  Eq.equivalence (λ A≈C → B  ∼⟨ sym A≈B ⟩
                          A  ∼⟨ A≈C ⟩
                          C  ∼⟨ C≈D ⟩
                          D  ∎)
                 (λ B≈D → A  ∼⟨ A≈B ⟩
                          B  ∼⟨ B≈D ⟩
                          D  ∼⟨ sym C≈D ⟩
                          C  ∎)
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- A lemma relating True dec and P, where dec : Dec P

True↔ : ∀ {p} {P : Set p}
        (dec : Dec P) → ((p₁ p₂ : P) → p₁ ≡ p₂) → True dec ↔ P
True↔ (yes p) irr = inverse (λ _ → p) (λ _ → _) (λ _ → P.refl) (irr p)
True↔ (no ¬p) _   = inverse (λ()) ¬p (λ()) (⊥-elim ∘ ¬p)

------------------------------------------------------------------------
-- Equality between pairs can be expressed as a pair of equalities

Σ-≡,≡↔≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             P.subst B p (proj₂ p₁) ≡ proj₂ p₂) ↔
          (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A = A} {B} = inverse to from left-inverse-of right-inverse-of
  where
  to : {p₁ p₂ : Σ A B} →
       Σ (proj₁ p₁ ≡ proj₁ p₂)
         (λ p → P.subst B p (proj₂ p₁) ≡ proj₂ p₂) →
       p₁ ≡ p₂
  to {._ , ._} (P.refl , P.refl) = P.refl

  from : {p₁ p₂ : Σ A B} →
         p₁ ≡ p₂ →
         Σ (proj₁ p₁ ≡ proj₁ p₂)
           (λ p → P.subst B p (proj₂ p₁) ≡ proj₂ p₂)
  from P.refl = P.refl , P.refl

  left-inverse-of : {p₁ p₂ : Σ A B}
                    (p : Σ (proj₁ p₁ ≡ proj₁ p₂)
                           (λ x → P.subst B x (proj₂ p₁) ≡ proj₂ p₂)) →
                    from (to p) ≡ p
  left-inverse-of {._ , ._} (P.refl , P.refl) = P.refl

  right-inverse-of : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂) → to (from p) ≡ p
  right-inverse-of P.refl = P.refl

×-≡,≡↔≡ : ∀ {a b} {A : Set a} {B : Set b} {p₁ p₂ : A × B} →
          (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂) ↔ p₁ ≡ p₂
×-≡,≡↔≡ {A = A} {B} = inverse to from left-inverse-of right-inverse-of
  where
  to : {p₁ p₂ : A × B} →
       (proj₁ p₁ ≡ proj₁ p₂) × (proj₂ p₁ ≡ proj₂ p₂) → p₁ ≡ p₂
  to {._ , ._} (P.refl , P.refl) = P.refl

  from : {p₁ p₂ : A × B} → p₁ ≡ p₂ →
         (proj₁ p₁ ≡ proj₁ p₂) × (proj₂ p₁ ≡ proj₂ p₂)
  from P.refl = P.refl , P.refl

  left-inverse-of : {p₁ p₂ : A × B} →
                    (p : (proj₁ p₁ ≡ proj₁ p₂) × (proj₂ p₁ ≡ proj₂ p₂)) →
                    from (to p) ≡ p
  left-inverse-of {._ , ._} (P.refl , P.refl) = P.refl

  right-inverse-of : {p₁ p₂ : A × B} (p : p₁ ≡ p₂) → to (from p) ≡ p
  right-inverse-of P.refl = P.refl

×-≡×≡↔≡,≡ : ∀ {a b} {A : Set a} {B : Set b} {x y} (p : A × B) →
            (x ≡ proj₁ p × y ≡ proj₂ p) ↔ (x , y) ≡ p
×-≡×≡↔≡,≡ {x = x} {y} p = inverse to from from∘to to∘from
   where
   to : (x ≡ proj₁ p × y ≡ proj₂ p) → (x , y) ≡ p
   to = uncurry $ P.cong₂ _,_

   from : (x , y) ≡ p → (x ≡ proj₁ p × y ≡ proj₂ p)
   from = < P.cong proj₁ , P.cong proj₂ >

   from∘to : ∀ v → from (to v) ≡ v
   from∘to = λ _ → P.cong₂ _,_ (P.≡-irrelevance _ _) (P.≡-irrelevance _ _)

   to∘from : ∀ v → to (from v) ≡ v
   to∘from = λ _ → P.≡-irrelevance _ _

