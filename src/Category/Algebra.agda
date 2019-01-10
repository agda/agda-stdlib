------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebras for endofunctors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Category.Category using (Category)

module Category.Algebra {ℓ} (cat : Category ℓ) where

open import Level
open Category cat
open import Category.Functor cat cat
  renaming (RawFunctor to RawEndoFunctor)

module _ {fun : Obj → Obj} (F : RawEndoFunctor fun) where
  open RawEndoFunctor F
  
  record Algebra : Set (suc ℓ) where
    field
      Carrier  : Obj
      evaluate : fun Carrier ⇒ Carrier
  open Algebra public

  open import Category.Structures
  module AlgebraCategory (isCat : IsCategory cat) (isFun : IsFunctor cat cat F) where
    open IsCategory isCat
    open IsFunctor isFun
    open ≈-Reasoning

    record AlgebraMorphism (algu : Algebra) (algv : Algebra) : Set ℓ where
      field
        translation : Carrier algu ⇒ Carrier algv
        commutes    : evaluate algv ∘ fmap translation ≈ translation ∘ evaluate algu
    open AlgebraMorphism
    
    idAlgebraMorphism : ∀ (alg : Algebra) → AlgebraMorphism alg alg
    idAlgebraMorphism alg = record
      { translation = id
      ; commutes = begin
        evaluate alg ∘ fmap id ≈⟨ fmap-identity over evaluate alg ⟩
        evaluate alg ∘ id      ≈⟨ identityʳ ⟩
        evaluate alg           ≈⟨ ≈sym identityˡ ⟩
        id ∘ evaluate alg      ∎
      }

    infixr 9 _∘alg_
    _∘alg_ : ∀ {algu algv algw : Algebra}
           → AlgebraMorphism algv algw → AlgebraMorphism algu algv → AlgebraMorphism algu algw
    _∘alg_ {algu = au} {algv = av} {algw = aw} vw uv = record
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
        algu = evaluate au
        algv = evaluate av
        algw = evaluate aw
        tvw = translation vw
        tuv = translation uv

    module _ {algu : Algebra} {algv : Algebra} where
      infix 4 _≈alg_
      record _≈alg_ (m : AlgebraMorphism algu algv) (n : AlgebraMorphism algu algv) : Set ℓ where
        field
          morphs-eq : translation m ≈ translation n
      open import Relation.Binary
    
      ≈alg-reflexive : Reflexive _≈alg_
      ≈alg-reflexive = record { morphs-eq = ≈refl }
      ≈alg-symmetric : Symmetric _≈alg_
      ≈alg-symmetric record { morphs-eq = eq } = record { morphs-eq = ≈sym eq }
      ≈alg-transitive : Transitive _≈alg_
      ≈alg-transitive record { morphs-eq = eqmn } record { morphs-eq = eqno } =
                      record { morphs-eq = ≈trans eqmn eqno }

    algebraCat : Category ℓ
    algebraCat = record
      { Obj = Algebra
      ; _⇒_ = AlgebraMorphism
      ; _≈_ = _≈alg_
      ; id = λ {x} → idAlgebraMorphism x
      ; _∘_ = _∘alg_
      }

    module _ where
      open Category algebraCat renaming (_⇒_ to _⇒alg_)
      
      ∘alg-associative : ∀ {A B C D}{f : A ⇒alg B}{g : B ⇒alg C}{h : C ⇒alg D}
                       → (h ∘alg g) ∘alg f ≈alg h ∘alg (g ∘alg f)
      ∘alg-associative = record { morphs-eq = assoc }
      ∘alg-identityʳ : ∀ {A B}{f : A ⇒alg B} → f ∘alg (idAlgebraMorphism _) ≈alg f
      ∘alg-identityʳ = record { morphs-eq = identityʳ }
      ∘alg-identityˡ : ∀ {A B}{f : A ⇒alg B} → (idAlgebraMorphism _) ∘alg f ≈alg f
      ∘alg-identityˡ = record { morphs-eq = identityˡ }
      ∘alg-respects-≈ : ∀ {A B C}{f h : B ⇒alg C}{g i : A ⇒alg B}
                      → f ≈alg h → g ≈alg i → f ∘alg g ≈alg h ∘alg i
      ∘alg-respects-≈ record { morphs-eq = f≈h } record { morphs-eq = g≈i } =
                      record { morphs-eq = ∘-respects-≈ f≈h g≈i }

    algebraCatIsCategory : IsCategory algebraCat
    algebraCatIsCategory = record
      { assoc = ∘alg-associative
      ; identityʳ = ∘alg-identityʳ
      ; identityˡ = ∘alg-identityˡ
      ; equiv = record
        { refl = ≈alg-reflexive
        ; sym = ≈alg-symmetric
        ; trans = ≈alg-transitive
      }
      ; ∘-respects-≈ = ∘alg-respects-≈
      }
