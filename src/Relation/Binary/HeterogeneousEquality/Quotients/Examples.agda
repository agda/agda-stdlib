module Examples where

open import Relation.Binary.HeterogeneousEquality
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.HeterogeneousEquality.Quotients
open import Level hiding (lift)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Product
open import Function

postulate quot : Quotients {Level.zero}{Level.zero}

ℕ² = ℕ × ℕ

_∼_ : ℕ² → ℕ² → Set
(x , y) ∼ (x' , y') = x + y' ≅ x' + y

infix 10 _∼_

+-suc-cancel : ∀ {m n} → ℕ.suc m ≡.≡ ℕ.suc n → m ≡.≡ n
+-suc-cancel ≡.refl = ≡.refl

+-left-cancel : ∀ {n n'} m → m + n ≡.≡ m + n' → n ≡.≡ n'
+-left-cancel zero p = p
+-left-cancel (suc m) p = +-left-cancel m (+-suc-cancel p) 

∼trans : ∀{i j k} → i ∼ j → j ∼ k → i ∼ k
∼trans {x , y}{x' , y'}{x'' , y''} p q = ≡-to-≅ $ +-left-cancel y' $ ≅-to-≡ $
  begin
  y' + (x + y'')
  ≡⟨ ≡.sym $ +-assoc y' x y'' ⟩
  (y' + x) + y''
  ≡⟨ ≡.cong (λ x → x + y'') (+-comm y' x) ⟩
  (x + y') + y''
  ≅⟨ cong (λ x → x + y'') p ⟩
  (x' + y) + y''
  ≡⟨ ≡.cong (λ x → x + y'') (+-comm x' y) ⟩
  (y + x') + y''
  ≡⟨ +-assoc y x' y'' ⟩
  y + (x' + y'')
  ≅⟨ cong (_+_ y) q ⟩
  y + (x'' + y')
  ≡⟨ +-comm y (x'' + y') ⟩
  (x'' + y') + y
  ≡⟨ ≡.cong (λ x → x + y) (+-comm x'' y') ⟩
  (y' + x'') + y
  ≡⟨ +-assoc y' x'' y ⟩
  y' + (x'' + y)
  ∎ 
  where open ≅-Reasoning

Int = quot (record { 
  Carrier       = ℕ² ; 
  _≈_           = _∼_ ; 
  isEquivalence = record { 
    refl  = refl ; 
    sym   = sym ; 
    trans = λ {i}{j}{k} → ∼trans {i}{j}{k}}})
open Quotient Int renaming (Q to ℤ)

_+²_ : ℕ² → ℕ² → ℕ²
(x , y) +² (x' , y') = x + x' , y + y'


+²cong : ∀{a b a' b'} → a ∼ a' → b ∼ b' → a +² b ∼ a' +² b'
+²cong {x , y}{x¹ , y¹}{x² , y²}{x³ , y³} p p' =
  begin
  (x + x¹) + (y² + y³)
  ≡⟨ ≡.cong (λ x → x + (y² + y³)) (+-comm x x¹) ⟩
  (x¹ + x) + (y² + y³)
  ≡⟨ +-assoc x¹ x (y² + y³) ⟩
  x¹ + (x + (y² + y³))
  ≡⟨ ≡.cong (_+_ x¹) (≡.sym (+-assoc x y² y³)) ⟩
  x¹ + ((x + y²) + y³)
  ≅⟨  cong (λ x → x¹ + (x + y³)) p ⟩
  x¹ + ((x² + y) + y³)
  ≡⟨ ≡.cong (_+_ x¹) (+-assoc x² y y³)  ⟩
  x¹ + (x² + (y + y³))
  ≡⟨ ≡.cong (λ x → x¹ + (x² + x)) (+-comm y y³) ⟩
  x¹ + (x² + (y³ + y))
  ≡⟨ ≡.sym (+-assoc x¹ x² (y³ + y)) ⟩
  (x¹ + x²) + (y³ + y)
  ≡⟨ ≡.cong (λ x → x + (y³ + y)) (+-comm x¹ x²) ⟩
  (x² + x¹) + (y³ + y)
  ≡⟨ +-assoc x² x¹ (y³ + y)  ⟩
  x² + (x¹ + (y³ + y))
  ≡⟨ ≡.cong (_+_ x²) (≡.sym (+-assoc x¹ y³ y)) ⟩
  x² + ((x¹ + y³) + y)
  ≅⟨ cong (λ x → x² + (x + y)) p' ⟩
  x² + ((x³ + y¹) + y)
  ≡⟨ ≡.cong (_+_ x²) (+-assoc x³ y¹ y) ⟩
  x² + (x³ + (y¹ + y))
  ≡⟨ ≡.cong (λ x → x² + (x³ + x)) (+-comm y¹ y) ⟩
  x² + (x³ + (y + y¹))
  ≡⟨ ≡.sym (+-assoc x² x³ (y + y¹))  ⟩
  x² + x³ + (y + y¹)
  ∎
  where open ≅-Reasoning

_+ℤ_ : ℤ → ℤ → ℤ
i +ℤ j = lift₂
  {Qu = Int}
  {Qu' = Int}
  (λ i j → abs (i +² j))
  (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p') )
  i
  j

zero² : ℕ²
zero² = 0 , 0

zeroℤ : ℤ
zeroℤ = abs zero²

+²-right-identity : (i : ℕ²) → (i +² zero²) ∼ i
+²-right-identity (x , y) =
  begin
  (x + 0) + y
  ≡⟨ ≡.cong (λ x → x + y) (+-right-identity x) ⟩
  x + y
  ≡⟨ ≡.cong (_+_ x) (≡.sym (+-right-identity y)) ⟩
  x + (y + 0) ∎
  where open ≅-Reasoning

+ℤ-right-identity : (i : ℤ)  → i +ℤ zeroℤ ≅ i
+ℤ-right-identity i = lift {λ i → i +ℤ zeroℤ ≅ i} (λ (i : ℕ²) →
  begin
  abs i +ℤ zeroℤ
  ≡⟨⟩
  abs i +ℤ abs zero²
  ≅⟨ lift₂Conv {Qu = Int}{Qu' = Int}{B = λ _ _ → ℤ} (λ i j → abs (i +² j))
               (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p'))
               i
               zero² ⟩
  abs (i +² zero²)
  ≅⟨ absCompat (+²-right-identity i) ⟩ -- could prove this just using cong abs
  abs i
  ∎)
  (hir' ∘ absCompat) i
  where open ≅-Reasoning

+²-left-identity : (i : ℕ²) → (zero² +² i) ∼ i
+²-left-identity i = refl

+ℤ-left-identity : (i : ℤ)  → zeroℤ +ℤ i ≅ i
+ℤ-left-identity i = lift {λ i → zeroℤ +ℤ i ≅ i} (λ (i : ℕ²) →
  begin
  zeroℤ +ℤ abs i
  ≡⟨⟩
  abs zero² +ℤ abs i
  ≅⟨ lift₂Conv {Qu = Int}{Qu' = Int}{B = λ _ _ → ℤ} (λ i j → abs (i +² j))
               (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p'))
               zero²
               i ⟩
  abs (zero² +² i)
  ≅⟨ absCompat (+²-left-identity i) ⟩
  abs i
  ∎)
  (hir' ∘ absCompat)
  i
  where open ≅-Reasoning


+²-associativity : (i j k : ℕ²) → (i +² j) +² k ∼ i +² (j +² k)
+²-associativity (a , b) (c , d) (e , f) =
  begin
  ((a + c) + e) + (b + (d + f))
  ≡⟨ ≡.cong₂ _+_ (+-assoc a c e) (≡.sym (+-assoc b d f)) ⟩
  (a + (c + e)) + ((b + d) + f)
  ∎ where open ≅-Reasoning

+ℤ-associativity : (i j k : ℤ) → (i +ℤ j) +ℤ k ≅ i +ℤ (j +ℤ k)
+ℤ-associativity i j k =
  lift₃ {Qu = Int}{Int}{Int}{B = λ i j k → (i +ℤ j) +ℤ k ≅ i +ℤ (j +ℤ k)}
        (λ i j k →
        begin
        (abs i +ℤ abs j) +ℤ abs k
        ≅⟨ cong (λ i → i +ℤ abs k)
                (lift₂Conv {Qu = Int}{Qu' = Int}{B = λ _ _ → ℤ}
                           (λ i₁ j₁ → abs (i₁ +² j₁))
                           (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p'))
                           i
                           j) ⟩
        abs (i +² j) +ℤ abs k
        ≅⟨ lift₂Conv {Qu = Int}{Qu' = Int}{B = λ _ _ → ℤ}
                     (λ i₁ j₁ → abs (i₁ +² j₁))
                     (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p'))
                     (i +² j)
                     k ⟩
        abs ((i +² j) +² k)
        ≅⟨ absCompat (+²-associativity i j k ) ⟩
        abs (i +² (j +² k))
        ≅⟨ sym $ lift₂Conv {Qu = Int}{Qu' = Int}{B = λ _ _ → ℤ}
                     (λ i₁ j₁ → abs (i₁ +² j₁))
                     (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p'))
                     i
                     (j +² k) ⟩
        abs i +ℤ (abs (j +² k))
        ≅⟨ cong (_+ℤ_ (abs i))
                (sym $ lift₂Conv {Qu = Int}{Qu' = Int}{B = λ _ _ → ℤ}
                                 (λ i₁ j₁ → abs (i₁ +² j₁))
                                 (λ {a}{b}{a'} p p' → absCompat (+²cong {a}{b}{a'} p p'))
                                 j
                                 k) ⟩
        abs i +ℤ (abs j +ℤ abs k)
        ∎)
        (λ p q r → hir (cong₂ _+ℤ_ (cong₂ _+ℤ_ (absCompat p)
                                               (absCompat q))
                                   (absCompat r))  )
        i
        j
        k where open ≅-Reasoning


