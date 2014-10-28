------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotients for Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality.Quotients where

open import Function
open import Level hiding (lift)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning

record Quotient {c ℓ} (S : Setoid c ℓ) : Set (suc (c ⊔ ℓ)) where
  open Setoid S renaming (Carrier to A)
  field 
    Q   : Set c
    abs : A → Q 

  compat : {B : Q → Set c} → ((a : A) → B (abs a)) → Set (c ⊔ ℓ)
  compat f = {a a′ : A} → a ≈ a′ → f a ≅ f a′
     
  field 
    absCompat : compat abs
    lift      : {B : Q → Set c}(f : (a : A) → B (abs a)) → compat {B} f →
                (q : Q) → B q
    liftConv  : {B : Q → Set c}(f : (a : A) → B (abs a))(p : compat {B} f)
                (a : A) → lift {B} f p (abs a) ≅ f a

Quotients : ∀{c ℓ} → Set (suc  (c ⊔ ℓ))
Quotients {c}{ℓ} = (S : Setoid c ℓ) → Quotient S

module _ {c}{ℓ}(S : Setoid c ℓ)(Qu : Quotient S) where

  open Setoid S renaming (Carrier to A) hiding (refl; sym; trans)
  open Quotient Qu

  liftUniqueness : {B : Q → Set c}{B' : Q → Set c}
                   (f : (a : A) → B (abs a)) → (p : compat {B} f)
                   (g : (x : Q) → B' x) → ((a : A) → g (abs a) ≅ f a) → 
                   ∀ x → lift {B} f p x ≅ g x
  liftUniqueness f p g r = lift (λ x →  
    begin
    lift f p (abs x)
    ≅⟨ liftConv f p x ⟩
    f x
    ≅⟨ sym (r x) ⟩
    g (abs x)
    ∎) 
    λ p' → hir (cong (lift f p) (absCompat p'))

  liftAbs : ∀ x → lift {λ _ → Q} abs absCompat x ≅ x
  liftAbs = liftUniqueness abs absCompat id (λ _ → refl)

  liftCong : {B B' : Q → Set c}
             {f : (a : A) → B (abs a)}{g : (a : A) → B' (abs a)}
             {p : compat {B} f}{p' : compat {B'} g} → (∀ x → f x ≅ g x) → 
             ∀ x → lift {B} f p x ≅ lift {B'} g p' x
  liftCong {B}{B'}{f}{g}{p}{p'} h = 
    liftUniqueness f p (lift g p') (λ a → trans (liftConv g p' a) (sym (h a)))

  isLift : {B : Q → Set c}(f : (x : Q) → B x) → 
           ∀ x → lift {B} (f ∘ abs) (cong f ∘ absCompat) x ≅ f x
  isLift f = 
    liftUniqueness (f ∘ abs) (cong f ∘ absCompat) f (λ _ → refl)

  absEpi : {B : Q → Set c}{f g : (x : Q) → B x} → 
           (∀ x → f (abs x) ≅ g (abs x)) → ∀ x → f x ≅ g x
  absEpi {f = f}{g = g} p x = 
    begin
    f x
    ≅⟨ sym (isLift f x) ⟩
    lift (f ∘ abs) (cong f ∘ absCompat) x
    ≅⟨ liftCong p x ⟩
    lift (g ∘ abs) (cong g ∘ absCompat) x
    ≅⟨ isLift g x ⟩
    g x
    ∎

--
postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}{f : ∀ a → B a}
                {g : ∀ a → B' a} → (∀ a → f a ≅ g a) → f ≅ g

compat₂ : ∀{ℓ c}{S S' : Setoid c ℓ}{Qu : Quotient S}{Qu' : Quotient S'}
          {B : Quotient.Q Qu → Quotient.Q Qu' → Set c}
          (f : (s : Setoid.Carrier S)(s' : Setoid.Carrier S') →
               B (Quotient.abs Qu s) (Quotient.abs Qu' s')) → Set _
compat₂ {S = S}{S'} f = 
  let open Setoid S
      open Setoid S' renaming (_≈_ to _≈'_) in
  ∀{a b a' b'} → a ≈ a' → b ≈' b' → f a b ≅ f a' b'

lift₂ : ∀{c ℓ}{S S' : Setoid c ℓ}{Qu : Quotient S}{Qu' : Quotient S'}
        {B : Quotient.Q Qu → Quotient.Q Qu' → Set c}
        (f : (s : Setoid.Carrier S)(s' : Setoid.Carrier S') →
             B (Quotient.abs Qu s) (Quotient.abs Qu' s')) →
        compat₂ {S = S}{S'}{Qu}{Qu'}{B = B} f → 
        (q : Quotient.Q Qu)(q' : Quotient.Q Qu') → B q q'
lift₂ {S = S}{S'}{Qu}{Qu'}{B} f p = let
  open Setoid S renaming (Carrier to A; refl to srefl)
  open Setoid S' renaming (refl to srefl')
  open Quotient Qu
  open Quotient Qu' renaming (Q to Q'; lift to lift'; abs to abs')
  g : (a : A)(q : Q') → B (abs a) q
  g a = lift' (f a) (p srefl) in
  lift g (λ {x}{x'} p' → ext (liftCong S' Qu' (λ _ → p p' srefl')))

lift₂Conv : ∀{c ℓ}{S S' : Setoid c ℓ}{Qu : Quotient S}{Qu' : Quotient S'}
        {B : Quotient.Q Qu → Quotient.Q Qu' → Set c}
        (f : (s : Setoid.Carrier S)(s' : Setoid.Carrier S') →
             B (Quotient.abs Qu s) (Quotient.abs Qu' s')) →
        (p : compat₂ {Qu = Qu}{Qu'}{B} f)
        (a : Setoid.Carrier S)(a' : Setoid.Carrier S') →
        lift₂ {Qu = Qu}{Qu'}{B} f p (Quotient.abs Qu a) (Quotient.abs Qu' a')
        ≅
        f a a'
lift₂Conv {S = S}{S'}{Qu}{Qu'}{B} f p a a' = let
  open Setoid S renaming (Carrier to A; refl to srefl)
  open Setoid S' renaming (refl to srefl')
  open Quotient Qu 
  open Quotient Qu'
    renaming (Q to Q'; lift to lift'; liftConv to liftConv'; abs to abs')
  g : (a : A)(q : Q') → B (abs a) q
  g a = lift' (f a) (p srefl) in  
  begin
  lift₂ {Qu = Qu}{Qu'} f p (abs a) (abs' a')
  ≅⟨ cong (λ (f : ∀ q' → B (abs a) q') → f (abs' a'))
          (liftConv g (λ p' → ext (liftCong S' Qu' λ _ → p p' (srefl'))) a)  ⟩
  g a (abs' a') 
  ≡⟨⟩
  lift' {B = B (abs a)} (f a) (p srefl) (abs' a')
  ≅⟨ liftConv' (f a) (p srefl) a' ⟩
  f a a'
  ∎ where open ≅-Reasoning

compat₃ : ∀{ℓ c}{S S' S'' : Setoid c ℓ}
  {Qu : Quotient S}{Qu' : Quotient S'}{Qu'' : Quotient S''}
  {B : Quotient.Q Qu → Quotient.Q Qu' → Quotient.Q Qu'' → Set c}
  (f : (s : Setoid.Carrier S)(s' : Setoid.Carrier S')(s'' : Setoid.Carrier S'')
       → B (Quotient.abs Qu s) (Quotient.abs Qu' s') (Quotient.abs Qu'' s'')) →
       Set _
compat₃ {S = S}{S'}{S''} f = 
  let open Setoid S
      open Setoid S' renaming (_≈_ to _≈'_)
      open Setoid S'' renaming (_≈_ to _≈''_) in
  ∀{a b a' b' c c'} → a ≈ a' → b ≈' b' → c ≈'' c' → f a b c ≅ f a' b' c'


lift₃ : ∀{c ℓ}{S S' S'' : Setoid c ℓ}
  {Qu : Quotient S}{Qu' : Quotient S'}{Qu'' : Quotient S''}
  {B : Quotient.Q Qu → Quotient.Q Qu' → Quotient.Q Qu'' → Set c}
  (f : (s : Setoid.Carrier S)(s' : Setoid.Carrier S')
       (s'' : Setoid.Carrier S'') →
       B (Quotient.abs Qu s) (Quotient.abs Qu' s') (Quotient.abs Qu'' s'')) →
  compat₃ {Qu = Qu}{Qu'}{Qu''}{B = B} f → 
  (q : Quotient.Q Qu)(q' : Quotient.Q Qu')(q'' : Quotient.Q Qu'') → B q q' q''
lift₃ {S = S}{S'}{S''}{Qu}{Qu'}{Qu''}{B} f p =
 let
  open Setoid S renaming (Carrier to A; refl to srefl)
  open Setoid S' renaming (Carrier to A'; refl to srefl')
  open Setoid S'' renaming (Carrier to A''; refl to srefl'')
  open Quotient Qu 
  open Quotient Qu' renaming (Q to Q'; abs to abs'; lift to lift')
  open Quotient Qu'' renaming (Q to Q''; abs to abs''; lift to lift'')
  g : (a : A)(a' : A')(q'' : Q'') → B (abs a) (abs' a') q''
  g a a' = lift'' (f a a') (p srefl srefl')
  h : (a : A)(q' : Q')(q'' : Q'') → B (abs a) q' q''
  h a  = lift' (g a) (λ p' → ext (liftCong _ Qu'' (λ _ → p srefl p' srefl'')))
 in
  lift h λ p' → ext (liftCong
    _
    Qu'
    λ _ → ext (liftCong _ Qu'' λ _ → p p' srefl' srefl''))

