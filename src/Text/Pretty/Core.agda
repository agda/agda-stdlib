------------------------------------------------------------------------
-- The Agda standard library
--
-- Pretty Printing
-- This module is based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Text.Pretty.Core where

import Level

open import Data.Bool.Base using (Bool)
open import Data.Erased    as Erased using (Erased) hiding (module Erased)
open import Data.List.Base as List   using (List; []; _∷_)
open import Data.Nat.Base            using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties
open import Data.Product as Prod using (_×_; _,_; uncurry; proj₁; proj₂)
import Data.Product.Relation.Unary.All as Allᴾ

open import Data.Tree.Binary as Tree using (Tree; leaf; node)
open import Data.Tree.Binary.Relation.Unary.All as Allᵀ using (leaf; node)
import Data.Tree.Binary.Relation.Unary.All.Properties as Allᵀₚ
import Data.Tree.Binary.Properties as Treeₚ

open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Maybe.Relation.Unary.All as Allᴹ using (nothing; just)

open import Data.String.Base as String
open import Data.String.Unsafe as Stringₚ
open import Function.Base
open import Relation.Nullary using (Dec)
open import Relation.Unary using (IUniversal; _⇒_)
open import Relation.Binary.PropositionalEquality

open import Data.Refinement hiding (map)
import Data.Refinement.Relation.Unary.All as Allᴿ

------------------------------------------------------------------------
-- Block of text

-- Content is a representation of the first line and the middle of the block.
-- We use a tree rather than a list for the middle of the block so that we can
-- extend it with lines on the left and on the line for free. We will ultimately
-- render the block by traversing the tree left to right in a depth-first manner.

Content : Set
Content = Maybe (String × Tree String)

size : Content → ℕ
size = maybe′ (suc ∘ Tree.size ∘ proj₂) 0

All : ∀ {p} (P : String → Set p) → (Content → Set p)
All P = Allᴹ.All (Allᴾ.All P (Allᵀ.All P))

All≤ : ℕ → Content → Set
All≤ n = All (λ s → length s ≤ n)

record Block : Set where
  field
    height    : ℕ
    block     : [ xs ∈ Content ∣ size xs ≡ height ]
  -- last line
    lastWidth : ℕ
    last      : [ s ∈ String ∣ length s ≡ lastWidth ]
  -- max of all the widths
    maxWidth  : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n (block .value) ]

------------------------------------------------------------------------
-- Raw string

text : String → Block
text s = record
  { height    = 0
  ; block     = nothing , ⦇ refl ⦈
  ; lastWidth = width
  ; last      = s , ⦇ refl ⦈
  ; maxWidth  = width , ⦇ (≤-refl , nothing) ⦈
  } where width = length s; open Erased

------------------------------------------------------------------------
-- Empty

empty : Block
empty = text ""

------------------------------------------------------------------------
-- Helper functions

node? : Content → String → Tree String → Content
node? (just (x , xs)) y ys = just (x , node xs y ys)
node? nothing         y ys = just (y , ys)

∣node?∣ : ∀ b y ys → size (node? b y ys)
                   ≡ size b + suc (Tree.size ys)
∣node?∣ (just (x , xs)) y ys = refl
∣node?∣ nothing         y ys = refl

≤-Content : ∀ {m n} {b : Content} → m ≤ n → All≤ m b → All≤ n b
≤-Content {m} {n} m≤n = Allᴹ.map (Prod.map step (Allᵀ.map step))

  where

  step : ∀ {p} → p ≤ m → p ≤ n
  step = flip ≤-trans m≤n

All≤-node? : ∀ {l m r n} →
             All≤ n l → length m ≤ n → Allᵀ.All (λ s → length s ≤ n) r →
             All≤ n (node? l m r)
All≤-node? nothing           py pys = just (py , pys)
All≤-node? (just (px , pxs)) py pys = just (px , node pxs py pys)

------------------------------------------------------------------------
-- Appending two documents

private
  module append (x y : Block) where

    module x = Block x
    module y = Block y

    blockx = x.block .value
    blocky = y.block .value

    widthx = x.maxWidth .value
    widthy = y.maxWidth .value

    lastx = x.last .value
    lasty = y.last .value

    height : ℕ
    height = (_+_ on Block.height) x y

    lastWidth : ℕ
    lastWidth = (_+_ on Block.lastWidth) x y

    pad : Maybe String
    pad with x.lastWidth
    ... | 0 = nothing
    ... | l = just (replicate l ' ')

    size-pad : maybe′ length 0 pad ≡ x.lastWidth
    size-pad with x.lastWidth
    ... | 0         = refl
    ... | l@(suc _) = length-replicate l

    indent : Maybe String → String → String
    indent = maybe′ _++_ id

    size-indent : ∀ ma str → length (indent ma str)
                ≡ maybe′ length 0 ma + length str
    size-indent nothing    str = refl
    size-indent (just pad) str = length-++ pad str

    indents : Maybe String → Tree String → Tree String
    indents = maybe′ (Tree.map ∘ _++_) id

    size-indents : ∀ ma t → Tree.size (indents ma t) ≡ Tree.size t
    size-indents nothing    t = refl
    size-indents (just pad) t = Treeₚ.size-map (pad ++_) t

    unfold-indents : ∀ ma t → indents ma t ≡ Tree.map (indent ma) t
    unfold-indents nothing    t = sym (Treeₚ.map-id t)
    unfold-indents (just pad) t = refl

    vContent : Content × String
    vContent with blocky
    ... | nothing        = blockx
                         , lastx ++ lasty
    ... | just (hd , tl) = node?
      {-,--------------,-}
      {-|-} blockx   {-|-}
      {-|-}          {-'---,-}    {-,------------------,-}
      {-|-} (lastx       {-|-} ++ {-|-}  hd)         {-|-}
      {-'------------------'-}    {-|-}              {-|-}
      (indents pad                {-|-}  tl)    {-,----'-}
      , indent pad                {-|-} lasty   {-|-}
                                  {-'-------------'-}

    vBlock = proj₁ vContent
    vLast  = proj₂ vContent

    isBlock : size blockx ≡ x.height → size blocky ≡ y.height →
              size vBlock ≡ height
    isBlock ∣x∣ ∣y∣ with blocky
    ... | nothing        = begin
      size blockx         ≡⟨ ∣x∣ ⟩
      x.height            ≡˘⟨ +-identityʳ x.height ⟩
      x.height + 0        ≡⟨ cong (_ +_) ∣y∣ ⟩
      x.height + y.height ∎ where open ≡-Reasoning
    ... | just (hd , tl) = begin
      ∣node∣                          ≡⟨ ∣node?∣ blockx middle rest ⟩
      ∣blockx∣ + suc (Tree.size rest) ≡⟨ cong ((size blockx +_) ∘′ suc) ∣rest∣ ⟩
      ∣blockx∣ + suc (Tree.size tl)   ≡⟨ cong₂ _+_ ∣x∣ ∣y∣ ⟩
      x.height + y.height             ∎ where

      open ≡-Reasoning
      ∣blockx∣ = size blockx
      middle   = lastx ++ hd
      rest     = indents pad tl
      ∣rest∣   = size-indents pad tl
      ∣node∣   = size (node? blockx middle rest)

    block : [ xs ∈ Content ∣ size xs ≡ height ]
    block .value = vBlock
    block .proof = ⦇ isBlock (Block.block x .proof) (Block.block y .proof) ⦈
      where open Erased

    isLastLine : length lastx ≡ x.lastWidth →
                 length lasty ≡ y.lastWidth →
                 length vLast ≡ lastWidth
    isLastLine ∣x∣ ∣y∣ with blocky
    ... | nothing        = begin
      length (lastx ++ lasty)       ≡⟨ length-++ lastx lasty ⟩
      length lastx + length lasty   ≡⟨ cong₂ _+_ ∣x∣ ∣y∣ ⟩
      x.lastWidth + y.lastWidth     ∎ where open ≡-Reasoning
    ... | just (hd , tl) = begin
      length (indent pad lasty)          ≡⟨ size-indent pad lasty ⟩
      maybe′ length 0 pad + length lasty ≡⟨ cong₂ _+_ size-pad ∣y∣ ⟩
      x.lastWidth + y.lastWidth          ∎ where open ≡-Reasoning

    last : [ s ∈ String ∣ length s ≡ lastWidth ]
    last .value = vLast
    last .proof = ⦇ isLastLine (Block.last x .proof) (Block.last y .proof) ⦈
      where open Erased

    vMaxWidth : ℕ
    vMaxWidth = widthx ⊔ (x.lastWidth + widthy)

    isMaxWidth₁ : y.lastWidth ≤ widthy → lastWidth ≤ vMaxWidth
    isMaxWidth₁ p = begin
      lastWidth            ≤⟨ +-monoʳ-≤ x.lastWidth p ⟩
      x.lastWidth + widthy ≤⟨ n≤m⊔n _ _ ⟩
      vMaxWidth            ∎ where open ≤-Reasoning

    isMaxWidth₂ : length lastx ≡ x.lastWidth →
                  x.lastWidth ≤ widthx →
                  All≤ widthx blockx →
                  All≤ widthy blocky →
                  All≤ vMaxWidth vBlock
    isMaxWidth₂ ∣x∣≡ ∣x∣≤ ∣xs∣ ∣ys∣ with blocky
    ... | nothing        = ≤-Content (m≤m⊔n _ _) ∣xs∣
    isMaxWidth₂ ∣x∣≡ ∣x∣≤ ∣xs∣ (just (∣hd∣ , ∣tl∣))
        | just (hd , tl) =
      All≤-node? (≤-Content (m≤m⊔n _ _) ∣xs∣)
                 middle
                 (subst (Allᵀ.All _) (sym $ unfold-indents pad tl)
                 $ Allᵀₚ.map⁺ (indent pad) (Allᵀ.map (indented _) ∣tl∣))
      where

      middle : length (lastx ++ hd) ≤ vMaxWidth
      middle = begin
        length (lastx ++ hd)     ≡⟨ length-++ lastx hd ⟩
        length lastx + length hd ≡⟨ cong (_+ _) ∣x∣≡ ⟩
        x.lastWidth + length hd  ≤⟨ +-monoʳ-≤ x.lastWidth ∣hd∣ ⟩
        x.lastWidth + widthy     ≤⟨ n≤m⊔n _ _ ⟩
        vMaxWidth                ∎ where open ≤-Reasoning

      indented : ∀ s → length s ≤ widthy →
                 length (indent pad s) ≤ vMaxWidth
      indented s ∣s∣ = begin
        length (indent pad s)          ≡⟨ size-indent pad s ⟩
        maybe′ length 0 pad + length s ≡⟨ cong (_+ _) size-pad ⟩
        x.lastWidth + length s         ≤⟨ +-monoʳ-≤ x.lastWidth ∣s∣ ⟩
        x.lastWidth + widthy           ≤⟨ n≤m⊔n (widthx) _ ⟩
        vMaxWidth                      ∎ where open ≤-Reasoning

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n vBlock ]
    maxWidth .value = vMaxWidth
    maxWidth .proof =
      ⦇ _,_ ⦇ isMaxWidth₁ (map proj₁ (Block.maxWidth y .proof)) ⦈
            ⦇ isMaxWidth₂ (Block.last x .proof)
                          (map proj₁ (Block.maxWidth x .proof))
                          (map proj₂ (Block.maxWidth x .proof))
                          (map proj₂ (Block.maxWidth y .proof))
            ⦈
      ⦈ where open Erased

infixl 4 _<>_
_<>_ : Block → Block → Block
x <> y = record { append x y }

------------------------------------------------------------------------
-- Flush (introduces a new line)

private
  module flush (x : Block) where

    module x = Block x
    blockx  = x.block .value
    lastx   = x.last .value
    widthx  = x.maxWidth .value
    heightx = x.height

    height    = suc heightx
    lastWidth = 0
    vMaxWidth = widthx

    last : [ s ∈ String ∣ length s ≡ lastWidth ]
    last = "" , ⦇ refl ⦈ where open Erased

    vContent = node? blockx lastx leaf

    isBlock : size blockx ≡ heightx → size vContent ≡  height
    isBlock ∣x∣ = begin
      size vContent   ≡⟨ ∣node?∣ blockx lastx leaf ⟩
      size blockx + 1 ≡⟨ cong (_+ 1) ∣x∣ ⟩
      heightx + 1     ≡⟨ +-comm heightx 1 ⟩
      height          ∎ where open ≡-Reasoning

    block : [ xs ∈ Content ∣ size xs ≡ height ]
    block .value = vContent
    block .proof = Erased.map isBlock $ Block.block x .proof

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n vContent ]
    maxWidth .value = widthx
    maxWidth .proof = map (z≤n ,_)
      ⦇ All≤-node? ⦇ proj₂ (Block.maxWidth x .proof) ⦈
                   ⦇ middle (Block.last x .proof) ⦇ proj₁ (Block.maxWidth x .proof) ⦈ ⦈
                   (pure leaf)
      ⦈ where

      open Erased

      middle : length lastx ≡ x.lastWidth → x.lastWidth ≤ vMaxWidth →
               length lastx ≤ vMaxWidth
      middle p q = begin
        length lastx ≡⟨ p ⟩
        x.lastWidth  ≤⟨ q ⟩
        vMaxWidth    ∎ where open ≤-Reasoning

flush : Block → Block
flush x = record { flush x }

------------------------------------------------------------------------
-- Other functions

render : Block → String
render x = unlines
  $ maybe′ (uncurry (λ hd tl → hd ∷ Tree.Infix.toList tl)) []
  $ node? (Block.block x .value) (Block.last x .value) leaf

valid : (width : ℕ) (b : Block) → Dec (Block.maxWidth b .value ≤ width)
valid width b = Block.maxWidth b .value ≤? width
