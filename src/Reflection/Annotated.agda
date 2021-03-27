------------------------------------------------------------------------
-- The Agda standard library
--
-- Annotated reflected syntax.
--
-- NOTE: This file does not check under --without-K due to restrictions
--       in the termination checker. In particular recursive functions
--       over a universe of types is not supported by --without-K.
------------------------------------------------------------------------

{-# OPTIONS --safe --with-K #-}

module Reflection.Annotated where

open import Level                               using (Level; 0ℓ; suc; _⊔_)
open import Category.Applicative                using (RawApplicative)
open import Data.Bool.Base                      using (Bool; false; true; if_then_else_)
open import Data.List.Base                      using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product                        using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base                    using (String)

open import Reflection
open import Reflection.Universe

open Clause
open Pattern
open Sort

------------------------------------------------------------------------
-- Annotations and annotated types

-- An Annotation is a type indexed by a reflected term.
Annotation : ∀ ℓ → Set (suc ℓ)
Annotation ℓ = ∀ {u} → ⟦ u ⟧ → Set ℓ

-- An annotated type is a family over an Annotation and a reflected term.
Typeₐ : ∀ ℓ → Univ → Set (suc ℓ)
Typeₐ ℓ u = Annotation ℓ → ⟦ u ⟧ → Set ℓ

private
  variable
    ℓ             : Level
    u             : Univ
    Ann Ann₁ Ann₂ : Annotation ℓ

-- ⟪_⟫ packs up an element of an annotated type with a top-level annotation.
infixr 30 ⟨_⟩_
data ⟪_⟫ {u} (Tyₐ : Typeₐ ℓ u) : Typeₐ ℓ u where
  ⟨_⟩_ : ∀ {t} → Ann t → Tyₐ Ann t → ⟪ Tyₐ ⟫ Ann t

ann : {Tyₐ : Typeₐ ℓ u} {t : ⟦ u ⟧} → ⟪ Tyₐ ⟫ Ann t → Ann t
ann (⟨ α ⟩ _) = α


------------------------------------------------------------------------
-- Annotated reflected syntax

-- Annotated lists are lists (All) of annotated values. No top-level
-- annotation added, since we don't want an annotation for every tail
-- of a list. Instead a top-level annotation is added on the outside.
-- See Argsₐ.
Listₐ : Typeₐ ℓ u → Typeₐ ℓ (⟨list⟩ u)
Listₐ Tyₐ Ann = All (Tyₐ Ann)

-- We define the rest of the annotated types in two variants:
-- The primed variant which has annotations on subterms, and the
-- non-primed variant which adds a top-level annotation to the primed
-- one.

data Absₐ′ (Tyₐ : Typeₐ ℓ u) : Typeₐ ℓ (⟨abs⟩ u) where
  abs : ∀ {t} x → Tyₐ Ann t → Absₐ′ Tyₐ Ann (abs x t)

Absₐ : Typeₐ ℓ u → Typeₐ ℓ (⟨abs⟩ u)
Absₐ Tyₐ = ⟪ Absₐ′ Tyₐ ⟫

data Argₐ′ (Tyₐ : Typeₐ ℓ u) : Typeₐ ℓ (⟨arg⟩ u) where
  arg : ∀ {t} i → Tyₐ Ann t → Argₐ′ Tyₐ Ann (arg i t)

Argₐ : Typeₐ ℓ u → Typeₐ ℓ (⟨arg⟩ u)
Argₐ Tyₐ = ⟪ Argₐ′ Tyₐ ⟫

data Namedₐ′ (Tyₐ : Typeₐ ℓ u) : Typeₐ ℓ (⟨named⟩ u) where
  _,_ : ∀ {t} x → Tyₐ Ann t → Namedₐ′ Tyₐ Ann (x , t)

Namedₐ : Typeₐ ℓ u → Typeₐ ℓ (⟨named⟩ u)
Namedₐ Tyₐ = ⟪ Namedₐ′ Tyₐ ⟫

-- Add a top-level annotation for Args.
Argsₐ : Typeₐ ℓ u → Typeₐ ℓ (⟨list⟩ (⟨arg⟩ u))
Argsₐ Tyₐ = ⟪ Listₐ (Argₐ Tyₐ) ⟫

mutual
  Termₐ : Typeₐ ℓ ⟨term⟩
  Termₐ = ⟪ Termₐ′ ⟫

  Patternₐ : Typeₐ ℓ ⟨pat⟩
  Patternₐ = ⟪ Patternₐ′ ⟫

  Sortₐ : Typeₐ ℓ ⟨sort⟩
  Sortₐ = ⟪ Sortₐ′ ⟫

  Clauseₐ : Typeₐ ℓ ⟨clause⟩
  Clauseₐ = ⟪ Clauseₐ′ ⟫

  Clausesₐ : Typeₐ ℓ (⟨list⟩ ⟨clause⟩)
  Clausesₐ = ⟪ Listₐ Clauseₐ ⟫

  Telₐ : Typeₐ ℓ ⟨tel⟩
  Telₐ = ⟪ Listₐ (Namedₐ (Argₐ Termₐ)) ⟫

  data Termₐ′ {ℓ} : Typeₐ ℓ ⟨term⟩ where
    var       : ∀ x {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (var x args)
    con       : ∀ c {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (con c args)
    def       : ∀ f {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (def f args)
    lam       : ∀ v {b}    → Absₐ  Termₐ Ann b    → Termₐ′ Ann (lam v b)
    pat-lam   : ∀ {cs args} → Clausesₐ Ann cs → Argsₐ Termₐ Ann args →
                  Termₐ′ Ann (pat-lam cs args)
    pi        : ∀ {a b} → Argₐ Termₐ Ann a → Absₐ Termₐ Ann b → Termₐ′ Ann (pi a b)
    agda-sort : ∀ {s} → Sortₐ Ann s → Termₐ′ Ann (agda-sort s)
    lit       : ∀ l → Termₐ′ Ann (lit l)
    meta      : ∀ x {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (meta x args)
    unknown   : Termₐ′ Ann unknown

  data Clauseₐ′ {ℓ} : Typeₐ ℓ ⟨clause⟩ where
    clause        : ∀ {tel ps t} → Telₐ Ann tel → Argsₐ Patternₐ Ann ps →
                      Termₐ Ann t → Clauseₐ′ Ann (clause tel ps t)
    absurd-clause : ∀ {tel ps} → Telₐ Ann tel → Argsₐ Patternₐ Ann ps →
                      Clauseₐ′ Ann (absurd-clause tel ps)

  data Sortₐ′ {ℓ} : Typeₐ ℓ ⟨sort⟩ where
    set     : ∀ {t} → Termₐ Ann t → Sortₐ′ Ann (set t)
    lit     : ∀ n → Sortₐ′ Ann (lit n)
    prop    : ∀ {t} → Termₐ Ann t → Sortₐ′ Ann (prop t)
    propLit : ∀ n → Sortₐ′ Ann (propLit n)
    inf     : ∀ n → Sortₐ′ Ann (inf n)
    unknown : Sortₐ′ Ann unknown

  data Patternₐ′ {ℓ} : Typeₐ ℓ ⟨pat⟩ where
    con    : ∀ c {ps} → Argsₐ Patternₐ Ann ps → Patternₐ′ Ann (con c ps)
    dot    : ∀ {t} → Termₐ Ann t → Patternₐ′ Ann (dot t)
    var    : ∀ x → Patternₐ′ Ann (var x)
    lit    : ∀ l → Patternₐ′ Ann (lit l)
    proj   : ∀ f → Patternₐ′ Ann (proj f)
    absurd : ∀ x → Patternₐ′ Ann (absurd x)


-- Mapping a code in the universe to its corresponding primed and
-- non-primed annotated type.

mutual
  Annotated′ : Typeₐ ℓ u
  Annotated′ {u = ⟨term⟩}    = Termₐ′
  Annotated′ {u = ⟨pat⟩}     = Patternₐ′
  Annotated′ {u = ⟨sort⟩}    = Sortₐ′
  Annotated′ {u = ⟨clause⟩}  = Clauseₐ′
  Annotated′ {u = ⟨list⟩ u}  = Listₐ Annotated
  Annotated′ {u = ⟨arg⟩ u}   = Argₐ′ Annotated
  Annotated′ {u = ⟨abs⟩ u}   = Absₐ′ Annotated
  Annotated′ {u = ⟨named⟩ u} = Namedₐ′ Annotated

  Annotated : Typeₐ ℓ u
  Annotated = ⟪ Annotated′ ⟫


------------------------------------------------------------------------
-- Annotating terms

-- An annotation function computes the top-level annotation given a
-- term annotated at all sub-terms.
AnnotationFun : Annotation ℓ → Set ℓ
AnnotationFun Ann = ∀ u {t : ⟦ u ⟧} → Annotated′ Ann t → Ann t


-- Given an annotation function we can do the bottom-up traversal of a
-- reflected term to compute an annotated version.
module _ (annFun : AnnotationFun Ann) where

  private
    annotated : {t : ⟦ u ⟧} → Annotated′ Ann t → Annotated Ann t
    annotated ps = ⟨ annFun _ ps ⟩ ps

  mutual
    annotate′ : (t : ⟦ u ⟧) → Annotated′ Ann t
    annotate′ {⟨term⟩}    (var x args)           = var x (annotate args)
    annotate′ {⟨term⟩}    (con c args)           = con c (annotate args)
    annotate′ {⟨term⟩}    (def f args)           = def f (annotate args)
    annotate′ {⟨term⟩}    (lam v t)              = lam v (annotate t)
    annotate′ {⟨term⟩}    (pat-lam cs args)      = pat-lam (annotate cs) (annotate args)
    annotate′ {⟨term⟩}    (pi a b)               = pi (annotate a) (annotate b)
    annotate′ {⟨term⟩}    (agda-sort s)          = agda-sort (annotate s)
    annotate′ {⟨term⟩}    (lit l)                = lit l
    annotate′ {⟨term⟩}    (meta x args)          = meta x (annotate args)
    annotate′ {⟨term⟩}    unknown                = unknown
    annotate′ {⟨pat⟩}     (con c ps)             = con c (annotate ps)
    annotate′ {⟨pat⟩}     (dot t)                = dot (annotate t)
    annotate′ {⟨pat⟩}     (var x)                = var x
    annotate′ {⟨pat⟩}     (lit l)                = lit l
    annotate′ {⟨pat⟩}     (proj f)               = proj f
    annotate′ {⟨pat⟩}     (absurd x)             = absurd x
    annotate′ {⟨sort⟩}    (set t)                = set (annotate t)
    annotate′ {⟨sort⟩}    (lit n)                = lit n
    annotate′ {⟨sort⟩}    (prop t)               = prop (annotate t)
    annotate′ {⟨sort⟩}    (propLit n)            = propLit n
    annotate′ {⟨sort⟩}    (inf n)                = inf n
    annotate′ {⟨sort⟩}    unknown                = unknown
    annotate′ {⟨clause⟩}  (clause tel ps t)      = clause (annotate tel) (annotate ps) (annotate t)
    annotate′ {⟨clause⟩}  (absurd-clause tel ps) = absurd-clause (annotate tel) (annotate ps)
    annotate′ {⟨abs⟩ u}   (abs x t)              = abs x (annotate t)
    annotate′ {⟨arg⟩ u}   (arg i t)              = arg i (annotate t)
    annotate′ {⟨list⟩ u}  []                     = []
    annotate′ {⟨list⟩ u}  (x ∷ xs)               = annotate x ∷ annotate′ xs
    annotate′ {⟨named⟩ u} (x , t)                = x , annotate t

    annotate : (t : ⟦ u ⟧) → Annotated Ann t
    annotate t = annotated (annotate′ t)


------------------------------------------------------------------------
-- Annotation function combinators

-- Mapping over annotations
mutual
  map′ : ∀ u → (∀ {u} {t : ⟦ u ⟧} → Ann₁ t → Ann₂ t) → {t : ⟦ u ⟧} → Annotated′ Ann₁ t → Annotated′ Ann₂ t
  map′ ⟨term⟩      f (var x args)         = var x (map f args)
  map′ ⟨term⟩      f (con c args)         = con c (map f args)
  map′ ⟨term⟩      f (def h args)         = def h (map f args)
  map′ ⟨term⟩      f (lam v b)            = lam v (map f b)
  map′ ⟨term⟩      f (pat-lam cs args)    = pat-lam (map f cs) (map f args)
  map′ ⟨term⟩      f (pi a b)             = pi (map f a) (map f b)
  map′ ⟨term⟩      f (agda-sort s)        = agda-sort (map f s)
  map′ ⟨term⟩      f (lit l)              = lit l
  map′ ⟨term⟩      f (meta x args)        = meta x (map f args)
  map′ ⟨term⟩      f unknown              = unknown
  map′ ⟨pat⟩       f (con c ps)           = con c (map f ps)
  map′ ⟨pat⟩       f (dot t)              = dot (map f t)
  map′ ⟨pat⟩       f (var x)              = var x
  map′ ⟨pat⟩       f (lit l)              = lit l
  map′ ⟨pat⟩       f (proj g)             = proj g
  map′ ⟨pat⟩       f (absurd x)           = absurd x
  map′ ⟨sort⟩      f (set t)              = set (map f t)
  map′ ⟨sort⟩      f (lit n)              = lit n
  map′ ⟨sort⟩      f (prop t)             = prop (map f t)
  map′ ⟨sort⟩      f (propLit n)          = propLit n
  map′ ⟨sort⟩      f (inf n)              = inf n
  map′ ⟨sort⟩      f unknown              = unknown
  map′ ⟨clause⟩    f (clause Γ ps args)   = clause (map f Γ) (map f ps) (map f args)
  map′ ⟨clause⟩    f (absurd-clause Γ ps) = absurd-clause (map f Γ) (map f ps)
  map′ (⟨list⟩ u)  f []                   = []
  map′ (⟨list⟩ u)  f (x ∷ xs)             = map f x ∷ map′ _ f xs
  map′ (⟨arg⟩ u)   f (arg i x)            = arg i (map f x)
  map′ (⟨abs⟩ u)   f (abs x t)            = abs x (map f t)
  map′ (⟨named⟩ u) f (x , t)              = x , map f t

  map : (∀ {u} {t : ⟦ u ⟧} → Ann₁ t → Ann₂ t) → ∀ {u} {t : ⟦ u ⟧} → Annotated Ann₁ t → Annotated Ann₂ t
  map f {u = u} (⟨ α ⟩ t) = ⟨ f α ⟩ map′ u f t


module _ {W : Set ℓ} (ε : W) (_∪_ : W → W → W) where

  -- This annotation function does nothing except combine ε's with _∪_.
  -- Lets you skip the boring cases when defining non-dependent
  -- annotation functions by adding a catch-all calling defaultAnn.
  defaultAnn : AnnotationFun (λ _ → W)
  defaultAnn ⟨term⟩      (var x args)         = ann args
  defaultAnn ⟨term⟩      (con c args)         = ann args
  defaultAnn ⟨term⟩      (def f args)         = ann args
  defaultAnn ⟨term⟩      (lam v b)            = ann b
  defaultAnn ⟨term⟩      (pat-lam cs args)    = ann cs ∪ ann args
  defaultAnn ⟨term⟩      (pi a b)             = ann a ∪ ann b
  defaultAnn ⟨term⟩      (agda-sort s)        = ann s
  defaultAnn ⟨term⟩      (lit l)              = ε
  defaultAnn ⟨term⟩      (meta x args)        = ann args
  defaultAnn ⟨term⟩      unknown              = ε
  defaultAnn ⟨pat⟩       (con c args)         = ann args
  defaultAnn ⟨pat⟩       (dot t)              = ann t
  defaultAnn ⟨pat⟩       (var x)              = ε
  defaultAnn ⟨pat⟩       (lit l)              = ε
  defaultAnn ⟨pat⟩       (proj f)             = ε
  defaultAnn ⟨pat⟩       (absurd x)           = ε
  defaultAnn ⟨sort⟩      (set t)              = ann t
  defaultAnn ⟨sort⟩      (lit n)              = ε
  defaultAnn ⟨sort⟩      (prop t)             = ann t
  defaultAnn ⟨sort⟩      (propLit n)          = ε
  defaultAnn ⟨sort⟩      (inf n)              = ε
  defaultAnn ⟨sort⟩      unknown              = ε
  defaultAnn ⟨clause⟩    (clause Γ ps t)      = ann Γ ∪ (ann ps ∪ ann t)
  defaultAnn ⟨clause⟩    (absurd-clause Γ ps) = ann Γ ∪ ann ps
  defaultAnn (⟨list⟩ u)  []                   = ε
  defaultAnn (⟨list⟩ u)  (x ∷ xs)             = ann x ∪ defaultAnn _ xs
  defaultAnn (⟨arg⟩ u)   (arg i x)            = ann x
  defaultAnn (⟨abs⟩ u)   (abs x t)            = ann t
  defaultAnn (⟨named⟩ u) (x , t)              = ann t


-- Cartisian product of two annotation functions.
infixr 4 _⊗_
_⊗_ : AnnotationFun Ann₁ → AnnotationFun Ann₂ → AnnotationFun (λ t → Ann₁ t × Ann₂ t)
(f ⊗ g) u t = f u (map′ u proj₁ t) , g u (map′ u proj₂ t)


------------------------------------------------------------------------
-- Annotation-driven traversal

-- Top-down applicative traversal of an annotated term. Applies an
-- action (without going into subterms) to terms whose annotation
-- satisfies a given criterion. Returns an unannotated term.

module Traverse {M : Set → Set} (appl : RawApplicative M) where

  open RawApplicative appl renaming (_⊛_ to _<*>_)

  module _ (apply? : ∀ {u} {t : ⟦ u ⟧} → Ann t → Bool)
           (action : ∀ {u} {t : ⟦ u ⟧} → Annotated Ann t → M ⟦ u ⟧) where

    mutual
      traverse′ : {t : ⟦ u ⟧} → Annotated′ Ann t → M ⟦ u ⟧
      traverse′ {⟨term⟩}    (var x args)         = var x <$> traverse args
      traverse′ {⟨term⟩}    (con c args)         = con c <$> traverse args
      traverse′ {⟨term⟩}    (def f args)         = def f <$> traverse args
      traverse′ {⟨term⟩}    (lam v b)            = lam v <$> traverse b
      traverse′ {⟨term⟩}    (pat-lam cs args)    = pat-lam <$> traverse cs <*> traverse args
      traverse′ {⟨term⟩}    (pi a b)             = pi <$> traverse a <*> traverse b
      traverse′ {⟨term⟩}    (agda-sort s)        = agda-sort <$> traverse s
      traverse′ {⟨term⟩}    (lit l)              = pure (lit l)
      traverse′ {⟨term⟩}    (meta x args)        = meta x <$> traverse args
      traverse′ {⟨term⟩}    unknown              = pure unknown
      traverse′ {⟨pat⟩}     (con c args)         = con c <$> traverse args
      traverse′ {⟨pat⟩}     (dot t)              = dot <$> traverse t
      traverse′ {⟨pat⟩}     (var x)              = pure (var x)
      traverse′ {⟨pat⟩}     (lit l)              = pure (lit l)
      traverse′ {⟨pat⟩}     (proj f)             = pure (proj f)
      traverse′ {⟨pat⟩}     (absurd x)           = pure (absurd x)
      traverse′ {⟨sort⟩}    (set t)              = set <$> traverse t
      traverse′ {⟨sort⟩}    (lit n)              = pure (lit n)
      traverse′ {⟨sort⟩}    (prop t)             = prop <$> traverse t
      traverse′ {⟨sort⟩}    (propLit n)          = pure (propLit n)
      traverse′ {⟨sort⟩}    (inf n)              = pure (inf n)
      traverse′ {⟨sort⟩}    unknown              = pure unknown
      traverse′ {⟨clause⟩}  (clause Γ ps t)      = clause <$> traverse Γ <*> traverse ps <*> traverse t
      traverse′ {⟨clause⟩}  (absurd-clause Γ ps) = absurd-clause <$> traverse Γ <*> traverse ps
      traverse′ {⟨list⟩ u}  []                   = pure []
      traverse′ {⟨list⟩ u}  (x ∷ xs)             = _∷_ <$> traverse x <*> traverse′ xs
      traverse′ {⟨arg⟩ u}   (arg i x)            = arg i <$> traverse x
      traverse′ {⟨abs⟩ u}   (abs x t)            = abs x <$> traverse t
      traverse′ {⟨named⟩ u} (x , t)              = x ,_ <$> traverse t

      traverse : {t : ⟦ u ⟧} → Annotated Ann t → M ⟦ u ⟧
      traverse t@(⟨ α ⟩ tₐ) = if apply? α then action t else traverse′ tₐ
