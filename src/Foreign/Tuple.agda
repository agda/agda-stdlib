module Foreign.Tuple where

data Pair (A : Set) (B : Set) : Set where
  pair : A -> B -> Pair A B

data Triple (A : Set)(B : Set)(C : Set) : Set where
  triple : A -> B -> C -> Triple A B C

data Quad (A : Set) (B : Set) (C : Set) (D : Set) : Set where
  quad : A -> B -> C -> D -> Quad A B C D

{-# COMPILED_DATA Pair (,) (,) #-}
{-# COMPILED_DATA Triple (,,) (,,) #-}
{-# COMPILED_DATA Quad (,,,) (,,,) #-}
