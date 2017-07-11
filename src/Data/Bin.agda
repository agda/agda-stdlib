------------------------------------------------------------------------
-- The Agda standard library
--
-- A binary representation of natural numbers
------------------------------------------------------------------------

module Data.Bin where

open import Data.Nat as Nat using (ℕ; zero; z≤n; s≤s; _∸_)
            renaming (suc to sucN; _<_ to _<n_; _>_ to _>n_;
                      _≤_ to _≤n_; _≰_ to _≰n_; _+_ to _+n_; _*_ to _*n_)
open import Data.Digit
open import Data.Fin as Fin using (Fin; zero) renaming (suc to 1+_)
open import Data.Fin.Properties as FP using (_+′_)
open import Data.List.Base as List hiding (downFrom)
open import Function
open import Data.Product using (uncurry; _,_; _×_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- for S.M. proposal --
open import Relation.Nullary using (yes; no)
import Relation.Binary.PropositionalEquality as PE
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit  using (⊤)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Data.Fin.Properties as FinP using (decSetoid; prop-toℕ-≤)
open import Data.Digit using (Bit; fromDigits)
open PE.≡-Reasoning renaming (_≡⟨_⟩_ to _≡[_]_; begin_ to ≡begin_;
                                                          _∎ to _≡end)
open import Data.Product               using (proj₁; proj₂; ∃)
open import Data.Nat.Properties.Simple using (+-comm; *-comm)
open import Data.Nat.Properties using
     (m+n∸n≡m; _*-mono_; module ≤-Reasoning; natEquiv;
      natDTO; tail0; 1*; +cong₁; +cong₂; suc>0; ≤0→=0; <→≢; >→≢;
      Even; odd-suc; even-2*; half; half-n*2; monot-half; half-suc-n≤n
     )
open import Data.Nat.DivMod as DM using (DivMod; _divMod_; _div_;
                                                           half-n=n-div-2)
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                          _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)




------------------------------------------------------------------------
-- The type

-- A representation of binary natural numbers in which there is
-- exactly one representative for every number.

-- The function toℕ below defines the meaning of Bin.

infix 8 _1#

-- bs stands for the binary number 1<reverse bs>, which is positive.

Bin⁺ : Set
Bin⁺ = List Bit

data Bin : Set where
  -- Zero.
  0#  : Bin
  -- bs 1# stands for the binary number 1<reverse bs>.
  _1# : (bs : Bin⁺) → Bin

------------------------------------------------------------------------
-- Conversion functions

-- Converting to a list of bits starting with the _least_ significant
-- one.

toBits : Bin → List Bit
toBits 0#      = [ zero ]
toBits (bs 1#) = bs ++ [ 1b ]

-- Converting to a natural number.

toℕ : Bin → ℕ
toℕ = fromDigits ∘ toBits

-- Converting from a list of bits, starting with the _least_
-- significant one.

fromBits : List Bit → Bin
fromBits []                = 0#
fromBits (b          ∷ bs) with fromBits bs
fromBits (b          ∷ bs) | bs′ 1# = (b ∷ bs′) 1#
fromBits (zero       ∷ bs) | 0#     = 0#
fromBits ((1+ zero)  ∷ bs) | 0#     = [] 1#
fromBits ((1+ 1+ ()) ∷ bs) | _

private
  pattern 2+_ n = sucN (sucN n)

  ntoBits′ : ℕ → ℕ → List Bit
  ntoBits′     0    _      = []
  ntoBits′     1    0      = zero ∷ 1b ∷ []
  ntoBits′     1    1      = 1b ∷ []
  ntoBits′ (2+ k)   0      = zero ∷ ntoBits′ (sucN k) k
  ntoBits′ (2+ k)   1      = 1b ∷ ntoBits′ (sucN k) (sucN k)
  ntoBits′ (sucN k) (2+ n) = ntoBits′ k n

  ntoBits : ℕ → List Bit
  ntoBits n = ntoBits′ n n

-- Converting from a natural number.

fromℕ : ℕ → Bin
fromℕ n = fromBits $ ntoBits n

------------------------------------------------------------------------
-- Order relation.

-- Wrapped so that the parameters can be inferred.

infix 4 _<_

data _<_ (b₁ b₂ : Bin) : Set where
  less : (lt : (Nat._<_ on toℕ) b₁ b₂) → b₁ < b₂

------------------------------------------------------------------------
-- Arithmetic

-- Power of two.

infixr 8 2^_

2^_ : ℕ → Bin⁺
2^ 0        = []
2^ (sucN n) = zero ∷ 2^ n

-- Base 2 logarithm (rounded downwards).

⌊log₂_⌋ : Bin⁺ → ℕ
⌊log₂ (b ∷ bs) ⌋ = sucN ⌊log₂ bs ⌋
⌊log₂ []       ⌋ = 0

-- Multiplication by 2.

infix 7 _*2 _*2+1

_*2 : Bin → Bin
0#      *2 = 0#
(bs 1#) *2 = (zero ∷ bs) 1#

_*2+1 : Bin → Bin
0#      *2+1 = [] 1#
(bs 1#) *2+1 = (1b ∷ bs) 1#

-- Division by 2, rounded downwards.

⌊_/2⌋ : Bin → Bin
⌊ 0#          /2⌋ = 0#
⌊ [] 1#       /2⌋ = 0#
⌊ (b ∷ bs) 1# /2⌋ = bs 1#

-- Addition.

Carry : Set
Carry = Bit

addBits : Carry → Bit → Bit → Carry × Bit
addBits c b₁ b₂ with c +′ (b₁ +′ b₂)
... | zero          = (zero , zero)
... | 1+ zero       = (zero , 1b)
... | 1+ 1+ zero    = (1b , zero)
... | 1+ 1+ 1+ zero = (1b , 1b)
... | 1+ 1+ 1+ 1+ ()

addCarryToBitList : Carry → List Bit → List Bit
addCarryToBitList zero      bs               = bs
addCarryToBitList (1+ zero) []               = 1b ∷ []
addCarryToBitList (1+ zero) (zero      ∷ bs) = 1b ∷ bs
addCarryToBitList (1+ zero) ((1+ zero) ∷ bs) = zero ∷ addCarryToBitList 1b bs
addCarryToBitList (1+ 1+ ()) _
addCarryToBitList _ ((1+ 1+ ()) ∷ _)

addBitLists : Carry → List Bit → List Bit → List Bit
addBitLists c []         bs₂        = addCarryToBitList c bs₂
addBitLists c bs₁        []         = addCarryToBitList c bs₁
addBitLists c (b₁ ∷ bs₁) (b₂ ∷ bs₂) with addBits c b₁ b₂
... | (c' , b') = b' ∷ addBitLists c' bs₁ bs₂

infixl 6 _+_

_+_ : Bin → Bin → Bin
m + n = fromBits (addBitLists zero (toBits m) (toBits n))

-- Multiplication.

infixl 7 _*_

_*_ : Bin → Bin → Bin
0#                  * n = 0#
[]               1# * n = n
-- (b + 2 * bs 1#) * n = b * n + 2 * (bs 1# * n)
(b         ∷ bs) 1# * n with bs 1# * n
(b         ∷ bs) 1# * n | 0#     = 0#
(zero      ∷ bs) 1# * n | bs' 1# = (zero ∷ bs') 1#
((1+ zero) ∷ bs) 1# * n | bs' 1# = n + (zero ∷ bs') 1#
((1+ 1+ ()) ∷ _) 1# * _ | _

-- Successor.

suc : Bin → Bin
suc n = [] 1# + n

-- Division by 2, rounded upwards.

⌈_/2⌉ : Bin → Bin
⌈ n /2⌉ = ⌊ suc n /2⌋

-- Predecessor.

pred : Bin⁺ → Bin
pred []                = 0#
pred (zero       ∷ bs) = pred bs *2+1
pred ((1+ zero)  ∷ bs) = (zero ∷ bs) 1#
pred ((1+ 1+ ()) ∷ bs)

-- downFrom n enumerates all numbers from n - 1 to 0. This function is
-- linear in n. Analysis: fromℕ takes linear time, and the preds used
-- take amortised constant time (to see this, let the cost of a pred
-- be 2, and put 1 debit on every bit which is 1).

downFrom : ℕ → List Bin
downFrom n = helper n (fromℕ n)
  where
  helper : ℕ → Bin → List Bin
  helper zero     0#      = []
  helper (sucN n) (bs 1#) = n′ ∷ helper n n′
    where n′ = pred bs
  -- Impossible cases:
  helper zero     (_ 1#) = []
  helper (sucN _) 0#     = []

------------------------------------------------------------------------
-- Tests

-- The tests below are run when this module is type checked.

-- First some test helpers:

private

  testLimit : ℕ
  testLimit = 5

  nats : List ℕ
  nats = List.downFrom testLimit

  nats⁺ : List ℕ
  nats⁺ = filter (λ n → ⌊ 1 Nat.≤? n ⌋) nats

  natPairs : List (ℕ × ℕ)
  natPairs = List.zip nats (reverse nats)

  _=[_]_ : (ℕ → ℕ) → List ℕ → (Bin → Bin) → Set
  f =[ ns ] g = List.map f ns ≡ List.map (toℕ ∘ g ∘ fromℕ) ns

  _=[_]₂_ : (ℕ → ℕ → ℕ) → List (ℕ × ℕ) → (Bin → Bin → Bin) → Set
  f =[ ps ]₂ g =
    List.map (uncurry f) ps ≡ List.map (toℕ ∘ uncurry (g on fromℕ)) ps

-- And then the tests:

private

  test-*2+1 : (λ n → Nat._+_ (Nat._*_ n 2) 1) =[ nats ] _*2+1
  test-*2+1 = refl

  test-*2 : (λ n → Nat._*_ n 2) =[ nats ] _*2
  test-*2 = refl

  test-⌊_/2⌋ : Nat.⌊_/2⌋ =[ nats ] ⌊_/2⌋
  test-⌊_/2⌋ = refl

  test-+ : Nat._+_ =[ natPairs ]₂ _+_
  test-+ = refl

  test-* : Nat._*_ =[ natPairs ]₂ _*_
  test-* = refl

  test-suc : sucN =[ nats ] suc
  test-suc = refl

  test-⌈_/2⌉ : Nat.⌈_/2⌉ =[ nats ] ⌈_/2⌉
  test-⌈_/2⌉ = refl

  drop-1# : Bin → Bin⁺
  drop-1# 0#      = []
  drop-1# (bs 1#) = bs

  test-pred : Nat.pred =[ nats⁺ ] (pred ∘ drop-1#)
  test-pred = refl

  test-downFrom : List.map toℕ (downFrom testLimit) ≡
                  List.downFrom testLimit
  test-downFrom = refl




-- Of proposal by S.M. *******************************************************
-- ℕ <--> Bin⁺  isomorphism for suc.


open DecTotalOrder natDTO using (_≟_)
           renaming (reflexive to ≤refl; trans to ≤trans; antisym to ≤antisym)

-- We use the binary code (Bin⁺) representation in which
--
-- 0 <--> [],  and a binary code either is  []  or ends with  1b
--                                                        (as the higher bit).
-- This higher bit condition is expressed below as  HasLast1if, HasLast1.
--
-- We prove below that   ℕ  <--suc-isomorphic-->  Bin⁺ ∩ HasLast1if.


-- Several lemmata for  HasLast1(if) -------------

HasLast1 : Bin⁺ → Set
HasLast1 []           = ⊥
HasLast1 (b ∷ [])     = b ≡ 1b
HasLast1 (_ ∷ b ∷ bs) = HasLast1 (b ∷ bs)

hasLast1-cons : (b : Bit) → (bs : Bin⁺) → HasLast1 bs → HasLast1 (b ∷ bs)
hasLast1-cons _ (b' ∷ bs) hl1-b':bs =  hl1-b':bs
hasLast1-cons _ []        ()

HasLast1if : Bin⁺ → Set              -- "empty or ends with 1b"
HasLast1if []           =  ⊤
HasLast1if (b ∷ [])     =  b ≡ 1b
HasLast1if (_ ∷ b ∷ bs) =  HasLast1if (b ∷ bs)

hasLast1→hasLast1if : ∀ bs → HasLast1 bs → HasLast1if bs
hasLast1→hasLast1if []           ()
hasLast1→hasLast1if (_ ∷ [])     hl1      = hl1
hasLast1→hasLast1if (_ ∷ b ∷ bs) hl1-b-bs =
                                       hasLast1→hasLast1if (b ∷ bs) hl1-b-bs

hasLast1if→hasLast1 : ∀ b bs → HasLast1if (b ∷ bs) → HasLast1 (b ∷ bs)
hasLast1if→hasLast1 _ []            hl =  hl
hasLast1if→hasLast1 _ (_ ∷ [])      hl =  hl
hasLast1if→hasLast1 b (_ ∷ b' ∷ bs) hl =  hasLast1if→hasLast1 b (b' ∷ bs) hl

hasLast1if-tail0 : (bs : Bin⁺) → HasLast1if bs → HasLast1if $ tail0 bs
hasLast1if-tail0 []          _ = ⊤.tt
hasLast1if-tail0 (_ ∷ [])    _ = ⊤.tt
hasLast1if-tail0 (_ ∷ _ ∷ _) p = p

------------------------------------------------------------------------------
private addC1 = addCarryToBitList 1b

hasLast1-addC1 : (bs : Bin⁺) → HasLast1if bs → HasLast1 (addC1 bs)
hasLast1-addC1 []                _  = PE.refl
hasLast1-addC1 ((1+ zero) ∷ [])  _  = PE.refl
hasLast1-addC1 (zero      ∷ [])  ()
hasLast1-addC1 ((1+ (1+ ())) ∷ _)

hasLast1-addC1 (zero ∷ b ∷ bs) hl1if-0:b:bs =
                                           hasLast1if→hasLast1 b bs hl1if-b:bs
               where
               hl1if-b:bs = hasLast1if-tail0 (zero ∷ b ∷ bs) hl1if-0:b:bs

hasLast1-addC1 ((1+ zero) ∷ b:bs) hl1if-1:b:bs =  hl1-0:addC1-b:bs
         where
         hl1if-b:bs     = hasLast1if-tail0 (1b ∷ b:bs) hl1if-1:b:bs
         addC1-b:bs     = addC1 b:bs
         hl1-addC1-b:bs = hasLast1-addC1 (b:bs) hl1if-b:bs   -- recursion

         hl1-0:addC1-b:bs : HasLast1 (zero ∷ addC1-b:bs)
         hl1-0:addC1-b:bs = hasLast1-cons zero addC1-b:bs hl1-addC1-b:bs

------------------------------------------------------------------------------
fromDigits>0 : (bs : Bin⁺) → HasLast1 bs → fromDigits bs >n 0
fromDigits>0 []                 ()
fromDigits>0 (zero ∷ [])        ()
fromDigits>0 ((1+ zero) ∷ [])   _          =  suc>0
fromDigits>0 ((1+ (1+ ())) ∷ _) _
fromDigits>0 ((1+ zero) ∷ _)    _          =  suc>0
fromDigits>0 (zero ∷ b ∷ bs)    hl1-0:b:bs =
    ≤begin
         1                            ≤[ fromDigits>0 (b ∷ bs) hl1-b:bs ]
         fromDigits (b ∷ bs)          ≤[ n≤n*2 _ ]
         fromDigits (b ∷ bs) *n 2    ≡≤[ PE.refl ]
         fromDigits (zero ∷ b ∷ bs)
    ≤end
    where hl1-b:bs : HasLast1 (b ∷ bs)
          hl1-b:bs = hl1-0:b:bs

          1≤2 = s≤s z≤n

          n≤n*2 : ∀ n → (n ≤n n *n 2)
          n≤n*2 n = ≤begin  n         ≡≤[ PE.sym $ 1* n ]
                            1 *n n     ≤[ _*-mono_ {1} {2} {n} {n} 1≤2
                                                           (≤refl PE.refl) ]
                            2 *n n    ≡≤[ *-comm 2 n ]
                            n *n 2
                    ≤end

------------------------------------------------------------------------------
bitDecSetoid = FinP.decSetoid 2
open DecSetoid bitDecSetoid using ()
                                  renaming (_≟_ to _≟b_; setoid to bitSetoid)

------------------------------------------------------------------------------
0≢fromDigits : ∀ b bs → HasLast1if (b ∷ bs) → 0 ≢ fromDigits (b ∷ bs)
0≢fromDigits b bs hl1if-b:bs =  0≢-b:bsN                    -- auxiliary thing
             where
             0≢-b:bsN :  0 ≢ fromDigits (b ∷ bs)
             0≢-b:bsN =  <→≢ 0<b:bsN
                         where
                         hasLast1-b:bs = hasLast1if→hasLast1 b bs hl1if-b:bs

                         0<b:bsN : 0 <n fromDigits (b ∷ bs)
                         0<b:bsN = fromDigits>0 (b ∷ bs) hasLast1-b:bs

------------------------------------------------------------------------------
injective-fromDigits : ∀ {bs bs'} → HasLast1if bs → HasLast1if bs' →
                                    fromDigits bs ≡ fromDigits bs' → bs ≡ bs'

injective-fromDigits {[]} {[]}     _ _          _       =  PE.refl
injective-fromDigits {[]} {b ∷ bs} _ hl1if-b:bs 0=b:bsN =
                                         ⊥-elim $ 0≢fromDigits b bs hl1if-b:bs
                                                                       0=b:bsN
injective-fromDigits {b ∷ bs} {[]} hl1if-b:bs _ b:bsN=0 =
                                       ⊥-elim $ 0≢fromDigits b bs hl1if-b:bs $
                                                                PE.sym b:bsN=0

injective-fromDigits {b ∷ bs} {b' ∷ bs'} hl1-b:bs hl1-b':bs' b:bs-N=b':bs'-N
  with
      b ≟b b'

... | yes b=b' =  PE.cong₂ _∷_ b=b' bs=bs'
      where
      hasLast1if-bs  = hasLast1if-tail0 (b ∷ bs)   hl1-b:bs
      hasLast1if-bs' = hasLast1if-tail0 (b' ∷ bs') hl1-b':bs'

      bN  = Fin.toℕ b
      b'N = Fin.toℕ b'

      bN=b'N :  bN ≡ b'N
      bN=b'N =  PE.cong Fin.toℕ b=b'

      bsN  = fromDigits bs
      bs'N = fromDigits bs'

      bsN*2=bs'N*2 : bsN *n 2 ≡ bs'N *n 2
                                         -- use  b:bs-N=b':bs'-N  for
      bsN*2=bs'N*2 =                     -- fromDigits (b ∷ bs) = bN+bsN*2 ≡..
        ≡begin
          bsN *n 2                   ≡[ PE.sym $ m+n∸n≡m _ bN ]
          (bsN *n 2 +n bN) ∸ bN      ≡[ PE.cong (\x → x ∸ bN) $ +-comm _ bN ]
          (bN +n bsN *n 2) ∸ bN      ≡[ PE.cong (\x → x ∸ bN)
                                                          b:bs-N=b':bs'-N ]
          (b'N +n bs'N *n 2) ∸ bN    ≡[ PE.cong (_∸_ _) bN=b'N ]
          (b'N +n bs'N *n 2) ∸ b'N   ≡[ PE.cong (\x → x ∸ b'N) $
                                                               +-comm b'N _ ]
          (bs'N *n 2 +n b'N) ∸ b'N   ≡[ m+n∸n≡m _ b'N ]
          bs'N *n 2
        ≡end

      bsN=bs'N =  ≡begin bsN                ≡[ PE.sym $ half-n*2 bsN ]
                         half (bsN *n 2)    ≡[ PE.cong half bsN*2=bs'N*2 ]
                         half (bs'N *n 2)   ≡[ half-n*2 bs'N ]
                         bs'N
                  ≡end

      bs=bs' = injective-fromDigits {bs} {bs'} hasLast1if-bs hasLast1if-bs'
                                                             bsN=bs'N

... | no b≢b'       -- to be rejected
      with b | b'

...   | _          | 1+ (1+ ())
...   | 1+ (1+ ()) | _
...   | zero       | zero      = ⊥-elim $ b≢b' PE.refl
...   | 1+ zero    | 1+ zero   = ⊥-elim $ b≢b' PE.refl

...   | zero | 1+ zero =  ⊥-elim $ odd-1+bs'N*2 even-1+bs'N*2
                        -- bsN * 2  ≡  1 + bs'N * 2
                        -- contradicts to  Even lhs × Odd rhs
                    where
                    bsN          = fromDigits bs
                    bs'N         = fromDigits bs'
                    even-bsN*2   = even-2* bsN
                    even-bs'N*2  = even-2* bs'N
                    odd-1+bs'N*2 = odd-suc even-bs'N*2

                    even-1+bs'N*2 : Even (1 +n bs'N *n 2)
                    even-1+bs'N*2 = PE.subst Even b:bs-N=b':bs'-N even-bsN*2

...   | 1+ zero | zero =  ⊥-elim $ odd-1+bsN*2 even-1+bsN*2
            where
            bsN         = fromDigits bs
            bs'N        = fromDigits bs'
            even-bsN*2  = even-2* bsN
            even-bs'N*2 = even-2* bs'N
            odd-1+bsN*2 = odd-suc even-bsN*2

            even-1+bsN*2 : Even (1 +n bsN *n 2)
            even-1+bsN*2 = PE.subst Even (PE.sym b:bs-N=b':bs'-N) even-bs'N*2


------------------------------------------------------------------------------
toBDigits : (n : ℕ) → ∃ \ (bs : Bin⁺) → fromDigits bs ≡ n × HasLast1if bs
--
-- Re-implementing  toDigits  for  base = 2  and  0 <--> [].
-- We hope that proofs for  toBDigits  will be simpler than for  toDigits.

toBDigits n =  toBits' n n (≤refl PE.refl)
  where
  toBits' : (n counter : ℕ) → n ≤n counter → ∃ \ (bs : Bin⁺) →
                                             fromDigits bs ≡ n × HasLast1if bs
  -- counter  is for termination proof; it decreases with each division by 2;
  --          and it holds counter ≡ 0 ==> n ≡ 0.

  toBits' 0       _         _       =  ([] , PE.refl ,    ⊤.tt)
  toBits' _       0         n≤0     =  ([] , PE.sym n=0 , ⊤.tt)
                                                            where
                                                            n=0 = ≤0→=0 n≤0
  toBits' (sucN n) (sucN cnt) n'≤cnt' =  (r ∷ bs , from-r:bs=n' , hl1if-r:bs)
    where
    open DM.DivMod

    n'   = sucN n
    cnt' = sucN cnt
    res  = n' divMod 2
    q    = quotient res

    r : Fin 2
    r = remainder res

    rN        = Fin.toℕ r
    n'=rN+q*2 = property res
    half-cnt' = half cnt'

    q=half-n' :  q ≡ half n'
    q=half-n' =  PE.sym $ half-n=n-div-2 n'

    q≤cnt : q ≤n cnt
    q≤cnt = ≤begin  q          ≡≤[ q=half-n' ]
                    half n'     ≤[ monot-half n'≤cnt' ]
                    half cnt'   ≤[ half-suc-n≤n cnt ]
                    cnt
            ≤end

    pair      = toBits' q cnt q≤cnt
    bs        = proj₁ pair
    from-bs=q = proj₁ $ proj₂ pair
    hl1if-bs  = proj₂ $ proj₂ pair

    from-r:bs=n' :  fromDigits (r ∷ bs) ≡ n'
    from-r:bs=n' =
         ≡begin
           fromDigits (r ∷ bs)            ≡[ PE.refl ]
           rN +n ((fromDigits bs) *n 2)   ≡[ +cong₂ {rN} $
                                             PE.cong (_*n 2) from-bs=q ]
           rN +n (q *n 2)                 ≡[ PE.sym n'=rN+q*2 ]
           n'
         ≡end

    hl1-r:bs : HasLast1 (r ∷ bs)
    hl1-r:bs = go r bs hl1if-bs from-r:bs=n'
      where
      go : (r : Bit) → (bs : Bin⁺) → HasLast1if bs →
                             fromDigits (r ∷ bs) ≡ n' → HasLast1 (r ∷ bs)
      go (1+ (1+ ()))
      go _            (b ∷ bs') hl1if-bs _          =  hasLast1if→hasLast1
                                                              b bs' hl1if-bs
      go (1+ zero)    []        _        _          =  PE.refl
      go zero         []        _        from[0]=n' =  ⊥-elim $ n'/=0 n'=0
         where
         n'/=0 = >→≢ (suc>0 {n})

         n'=0 : n' ≡ 0
         n'=0 = ≡begin  n'                             ≡[ PE.sym from[0]=n' ]
                        fromDigits ((zero {2}) ∷ [])   ≡[ PE.refl ]
                        0
                ≡end

    hl1if-r:bs : HasLast1if (r ∷ bs)
    hl1if-r:bs = hasLast1→hasLast1if (r ∷ bs) hl1-r:bs

------------------------------------------------------------------------------
toBDigs : ℕ → Bin⁺
toBDigs = proj₁ ∘ toBDigits

fromDigits-toBDigs=id : ∀ {n} → fromDigits (toBDigs n) ≡ n
fromDigits-toBDigs=id {n} =  proj₁ $ proj₂ $ toBDigits n
--
-- Two equations for the two mutually inverse bijections for
--                                            ℕ  <->  Bin⁺ ∩ HasLast1if
--
toBDigs-fromDigits=id : {bs : Bin⁺} → HasLast1if bs →
                                                  toBDigs (fromDigits bs) ≡ bs
toBDigs-fromDigits=id {[]}      _         =  PE.refl
toBDigs-fromDigits=id {b ∷ bs} hl1if-b:bs =
  case
      toBDigits n
  of \
  { (bs' , (from-bs'=n , _)) → injective-fromDigits hl1if-b+n*2
                                       hl1if-b:bs from-toBDigs-b+n*2=from-b:bs
  }
  where
  n           = fromDigits bs
  bN          = Fin.toℕ b
  b+n*2       = bN +n n *n 2
  hl1if-b+n*2 = proj₂ $ proj₂ $ toBDigits b+n*2

  from-toBDigs-b+n*2=from-b:bs : fromDigits (toBDigs b+n*2) ≡
                                                         fromDigits (b ∷ bs)
  from-toBDigs-b+n*2=from-b:bs = PE.trans fromDigits-toBDigs=id PE.refl


------------------------------------------------------------------------------
fromDigits-suc-eq : {bs : Bin⁺} → fromDigits (addC1 bs) ≡ sucN (fromDigits bs)

fromDigits-suc-eq {[]}               = PE.refl
fromDigits-suc-eq {(1+ (1+ ())) ∷ _}

fromDigits-suc-eq {zero ∷ bs}      =  PE.refl
                       -- 1 + (fromDigits (bs) * 2 ≡ suc ((fromDigits bs) * 2)
fromDigits-suc-eq {(1+ zero) ∷ bs} =  PE.cong (_*n 2) $ fromDigits-suc-eq {bs}
  -- because the goal
  --         (fromDigits (addC1 bs)) * 2  ≡  suc (suc ((fromDigits bs) * 2))
  -- is normalized to  ...
  --         (fromDigits (addC1 bs)) * 2  ≡  suc (1 + (fromDigits bs) * 2),
  -- and then the recursive proof is applied in LHS.

-- fromDigits-suc-eq  and  toBDigs-suc-eq   prove the two isomorphisms for
--                                                   ℕ  <->  Bin⁺ ∩ HasLast1if

------------------------------------------------------------------------------
toBDigs-suc-eq :  {n : ℕ} → toBDigs (sucN n) ≡ addC1 (toBDigs n)
toBDigs-suc-eq {n}  with  toBDigits n
...
    | (bs , (from-bs=n , hl1if-bs)) =  goal
    where
    bs'       = addC1 bs
    hl1if-bs' = hasLast1→hasLast1if bs' $ hasLast1-addC1 bs hl1if-bs

    e : fromDigits bs' ≡ sucN n
    e = ≡begin  fromDigits bs'         ≡[ fromDigits-suc-eq {bs} ]
                sucN (fromDigits bs)   ≡[ PE.cong sucN from-bs=n ]
                sucN n
        ≡end

    goal : toBDigs (sucN n) ≡ addC1 bs
    goal = ≡begin
             toBDigs (sucN n)           ≡[ PE.cong toBDigs $ PE.sym e ]
             toBDigs (fromDigits bs')   ≡[ toBDigs-fromDigits=id hl1if-bs' ]
             bs'
           ≡end
