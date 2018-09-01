------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of strict orders for keys for AVL trees.
------------------------------------------------------------------------

open import Relation.Binary

module Data.AVL.Key.Relation.StrictOrder
       {k r} (Key : Set k) (_<_ : Rel Key r)
       where

open import Data.AVL.Key Key

open import Level
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Product
open import Function
open import Relation.Nullary

-- An extended strict ordering relation.

infix 4 _<⁺_

_<⁺_ : Key⁺ → Key⁺ → Set r
⊥⁺    <⁺ [ _ ] = Lift r ⊤
⊥⁺    <⁺ ⊤⁺    = Lift r ⊤
[ k ] <⁺ [ l ] = k < l
[ _ ] <⁺ ⊤⁺    = Lift r ⊤
_     <⁺ _     = Lift r ⊥

-- A pair of ordering constraints.

infix 4 _<_<_

_<_<_ : Key⁺ → Key → Key⁺ → Set r
l < k < u = l <⁺ [ k ] × [ k ] <⁺ u

<⁺-asym : Asymmetric _<_ → Asymmetric _<⁺_
<⁺-asym <-asym {[ k ]} {[ l ]} = <-asym
<⁺-asym <-asym {⊥⁺} {⊥⁺} ()
<⁺-asym <-asym {⊥⁺} {⊤⁺} _ ()
<⁺-asym <-asym {⊥⁺} {[ l ]} _ ()
<⁺-asym <-asym {⊤⁺} {⊥⁺} ()
<⁺-asym <-asym {⊤⁺} {⊤⁺} ()
<⁺-asym <-asym {⊤⁺} {[ l ]} ()
<⁺-asym <-asym {[ k ]} {⊥⁺} ()
<⁺-asym <-asym {[ k ]} {⊤⁺}  _ ()

<⁺-trans : Transitive _<_ → Transitive _<⁺_
<⁺-trans <-trans {⊥⁺}    {l}     {⊤⁺}    = _
<⁺-trans <-trans {⊥⁺}    {l}     {[ k ]} = _
<⁺-trans <-trans {[ k ]} {l}     {⊤⁺}    = _
<⁺-trans <-trans {[ k ]} {[ l ]} {[ m ]} = <-trans
<⁺-trans <-trans {⊤⁺} {l} {m} ()
<⁺-trans <-trans {⊥⁺} {⊥⁺} {⊥⁺} ()
<⁺-trans <-trans {⊥⁺} {⊤⁺} {⊥⁺} _ ()
<⁺-trans <-trans {⊥⁺} {[ k ]} {⊥⁺} _ ()
<⁺-trans <-trans {[ k ]} {⊥⁺} {⊥⁺} ()
<⁺-trans <-trans {[ k ]} {⊤⁺} {⊥⁺} _ ()
<⁺-trans <-trans {[ k ]} {[ l ]} {⊥⁺} _ ()
<⁺-trans <-trans {[ k ]} {⊥⁺} {[ m ]} ()
<⁺-trans <-trans {[ k ]} {⊤⁺} {[ m ]} _ ()

<⁺-dec : Decidable _<_ → Decidable _<⁺_
<⁺-dec <-dec ⊥⁺    ⊥⁺    = no λ ()
<⁺-dec <-dec ⊥⁺    ⊤⁺    = yes _
<⁺-dec <-dec ⊥⁺    [ l ] = yes _
<⁺-dec <-dec ⊤⁺    ⊥⁺    = no λ ()
<⁺-dec <-dec ⊤⁺    ⊤⁺    = no λ ()
<⁺-dec <-dec ⊤⁺    [ l ] = no λ ()
<⁺-dec <-dec [ k ] ⊥⁺    = no λ ()
<⁺-dec <-dec [ k ] ⊤⁺    = yes _
<⁺-dec <-dec [ k ] [ l ] = <-dec k l

module _ {e} {_≈_ : Rel Key e} where

  open import Data.AVL.Key.Relation.Pointwise Key _≈_

  <⁺-tri : Trichotomous _≈_ _<_ → Trichotomous _≈⁺_ _<⁺_
  <⁺-tri <-tri ⊥⁺    ⊥⁺    = tri≈ lower _ lower
  <⁺-tri <-tri ⊥⁺    ⊤⁺    = tri< _ lower lower
  <⁺-tri <-tri ⊥⁺    [ l ] = tri< _ lower lower
  <⁺-tri <-tri ⊤⁺    ⊥⁺    = tri> lower lower _
  <⁺-tri <-tri ⊤⁺    ⊤⁺    = tri≈ lower _ lower
  <⁺-tri <-tri ⊤⁺    [ l ] = tri> lower lower _
  <⁺-tri <-tri [ k ] ⊥⁺    = tri> lower lower _
  <⁺-tri <-tri [ k ] ⊤⁺    = tri< _ lower lower
  <⁺-tri <-tri [ k ] [ l ] = <-tri k l

  <⁺-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈⁺_ _<⁺_
  <⁺-irrefl <-irrefl {⊥⁺}    {⊥⁺}    _ ()
  <⁺-irrefl <-irrefl {⊥⁺}    {⊤⁺}    ()
  <⁺-irrefl <-irrefl {⊥⁺}    {[ k ]} ()
  <⁺-irrefl <-irrefl {⊤⁺}    {l}     _ ()
  <⁺-irrefl <-irrefl {[ k ]} {⊥⁺}    ()
  <⁺-irrefl <-irrefl {[ k ]} {⊤⁺}    ()
  <⁺-irrefl <-irrefl {[ k ]} {[ l ]} = <-irrefl

  <⁺-respˡ-≈⁺ : _<_ Respectsˡ _≈_ → _<⁺_ Respectsˡ _≈⁺_
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_}     {⊥⁺}    {⊥⁺}    _ = id
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_}     {⊤⁺}    {⊤⁺}    _ = id
  <⁺-respˡ-≈⁺ <-respˡ-≈ {⊤⁺}    {[ l ]} {[ m ]} = _
  <⁺-respˡ-≈⁺ <-respˡ-≈ {[ k ]} {[ l ]} {[ m ]} = <-respˡ-≈
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_} {⊥⁺}    {⊤⁺}    ()
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_} {⊥⁺}    {[ m ]} ()
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_} {⊤⁺}    {⊥⁺}    ()
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_} {⊤⁺}    {[ m ]} ()
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_} {[ l ]} {⊥⁺}    ()
  <⁺-respˡ-≈⁺ <-respˡ-≈ {_} {[ l ]} {⊤⁺}    ()
  <⁺-respˡ-≈⁺ <-respˡ-≈ {⊥⁺}    {[ l ]} {[ m ]} _ ()

  <⁺-respʳ-≈⁺ : _<_ Respectsʳ _≈_ → _<⁺_ Respectsʳ _≈⁺_
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k}     {⊥⁺}    {⊥⁺}    _ = id
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k}     {⊤⁺}    {⊤⁺}    _ = id
  <⁺-respʳ-≈⁺ <-respʳ-≈ {⊥⁺}    {[ l ]} {[ m ]} = _
  <⁺-respʳ-≈⁺ <-respʳ-≈ {⊤⁺}    {[ l ]} {[ m ]} _ = id
  <⁺-respʳ-≈⁺ <-respʳ-≈ {[ k ]} {[ l ]} {[ m ]} = <-respʳ-≈
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k} {⊥⁺} {⊤⁺} ()
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k} {⊥⁺} {[ m ]} ()
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k} {⊤⁺} {⊥⁺} ()
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k} {⊤⁺} {[ m ]} ()
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k} {[ l ]} {⊥⁺} ()
  <⁺-respʳ-≈⁺ <-respʳ-≈ {k} {[ l ]} {⊤⁺} ()

  <⁺-resp-≈⁺ : _<_ Respects₂ _≈_ → _<⁺_ Respects₂ _≈⁺_
  <⁺-resp-≈⁺ = map <⁺-respʳ-≈⁺ <⁺-respˡ-≈⁺

  <⁺-isStrictPartialOrder :
    IsStrictPartialOrder _≈_ _<_ → IsStrictPartialOrder _≈⁺_ _<⁺_
  <⁺-isStrictPartialOrder strict = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; irrefl        = λ {x} → <⁺-irrefl irrefl {x}
    ; trans         = λ {x} → <⁺-trans trans {x}
    ; <-resp-≈      = <⁺-resp-≈⁺ <-resp-≈
    } where open IsStrictPartialOrder strict

  <⁺-isDecStrictPartialOrder :
    IsDecStrictPartialOrder _≈_ _<_ → IsDecStrictPartialOrder _≈⁺_ _<⁺_
  <⁺-isDecStrictPartialOrder dectot = record
    { isStrictPartialOrder = <⁺-isStrictPartialOrder isStrictPartialOrder
    ; _≟_                  = ≈⁺-dec _≟_
    ; _<?_                 = <⁺-dec _<?_
    } where open IsDecStrictPartialOrder dectot

  <⁺-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsStrictTotalOrder _≈⁺_ _<⁺_
  <⁺-isStrictTotalOrder strictot = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; trans         = λ {x} → <⁺-trans trans {x}
    ; compare       = <⁺-tri compare
    } where open IsStrictTotalOrder strictot
