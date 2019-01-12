------------------------------------------------------------------------
-- The Agda standard library
--
-- Category of algebras
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Category
open import Category.Functor
open import Category.Structures
open import Relation.Binary using (Reflexive; Symmetric; Transitive; TransFlip)

module Category.Construct.Algebra {o m r}
                                  (cat : Category o m r)
                                  (fun : EndoFunctor (Category.rawCategory cat)) where

open Functor fun
open Category.Category cat
open import Category.Algebra (Functor.rawFunctor fun)
open ≈-Reasoning

infix 4 _⇒alg_
record _⇒alg_ (algu : Algebra) (algv : Algebra) : Set (m ⊔ r) where
  field
    translation : Carrier algu ⇒ Carrier algv
    commutes    : evaluate algv ∘ fmap translation ≈ translation ∘ evaluate algu
open _⇒alg_

id⇒alg : ∀ (alg : Algebra) → alg ⇒alg alg
id⇒alg alg = record
  { translation = id
  ; commutes = begin
    evaluate alg ∘ fmap id ≈⟨ fmap-identity over evaluate alg ⟩
    evaluate alg ∘ id      ≈⟨ identityʳ ⟩
    evaluate alg           ≈⟨ ≈sym identityˡ ⟩
    id ∘ evaluate alg      ∎
  }

infixr 9 _∘alg_
_∘alg_ : TransFlip _⇒alg_ _⇒alg_ _⇒alg_
_∘alg_ {i = u} {j = v} {k = w} vw uv = record
  { translation = tvw ∘ tuv
  ; commutes = begin
    algw ∘ fmap (tvw ∘ tuv)      ≈⟨ fmap-homomorphism over algw ⟩
    algw ∘ (fmap tvw ∘ fmap tuv) ≈⟨ ≈sym assoc ⟩
    (algw ∘ fmap tvw) ∘ fmap tuv ≈⟨ vw .commutes under fmap tuv ⟩
    (tvw ∘ algv) ∘ fmap tuv      ≈⟨ assoc ⟩
    tvw ∘ algv ∘ fmap tuv        ≈⟨ uv .commutes over tvw ⟩
    tvw ∘ (tuv ∘ algu)           ≈⟨ ≈sym assoc ⟩
    (tvw ∘ tuv) ∘ algu           ∎
  } where
    algu = evaluate u
    algv = evaluate v
    algw = evaluate w
    tvw = translation vw
    tuv = translation uv

module _ {algu : Algebra} {algv : Algebra} where
  infix 4 _≈alg_
  record _≈alg_ (m : algu ⇒alg algv) (n : algu ⇒alg algv) : Set r where
    field
      morphs-eq : translation m ≈ translation n

  ≈alg-reflexive : Reflexive _≈alg_
  ≈alg-reflexive = record { morphs-eq = ≈refl }
  ≈alg-symmetric : Symmetric _≈alg_
  ≈alg-symmetric record { morphs-eq = eq } = record { morphs-eq = ≈sym eq }
  ≈alg-transitive : Transitive _≈alg_
  ≈alg-transitive record { morphs-eq = eqmn } record { morphs-eq = eqno } =
                  record { morphs-eq = ≈trans eqmn eqno }

∘alg-associative : ∀ {A B C D}{f : A ⇒alg B}{g : B ⇒alg C}{h : C ⇒alg D}
                 → (h ∘alg g) ∘alg f ≈alg h ∘alg (g ∘alg f)
∘alg-associative = record { morphs-eq = assoc }
∘alg-identityʳ : ∀ {A B}{f : A ⇒alg B} → f ∘alg (id⇒alg _) ≈alg f
∘alg-identityʳ = record { morphs-eq = identityʳ }
∘alg-identityˡ : ∀ {A B}{f : A ⇒alg B} → (id⇒alg _) ∘alg f ≈alg f
∘alg-identityˡ = record { morphs-eq = identityˡ }
∘alg-respects-≈ : ∀ {A B C}{f h : B ⇒alg C}{g i : A ⇒alg B}
                → f ≈alg h → g ≈alg i → f ∘alg g ≈alg h ∘alg i
∘alg-respects-≈ record { morphs-eq = f≈h } record { morphs-eq = g≈i } =
                record { morphs-eq = ∘-respects-≈ f≈h g≈i }

algebraCat : Category _ _ _
algebraCat = record
  { Obj = Algebra
  ; _⇒_ = _⇒alg_
  ; _≈_ = _≈alg_
  ; id = λ {x} → id⇒alg x
  ; _∘_ = _∘alg_
  ; isCategory = record
    { assoc = ∘alg-associative
    ; identityʳ = ∘alg-identityʳ
    ; identityˡ = ∘alg-identityˡ
    ; equiv = record
      { refl = ≈alg-reflexive
      ; sym = ≈alg-symmetric
      ; trans = ≈alg-transitive
      }
    ; ∘-respects-≈ = ∘alg-respects-≈
  } }
