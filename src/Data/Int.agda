module Data.Int where

{-# IMPORT Data.Int #-}

postulate
  Int : Set
  Int8 : Set
  Int16 : Set
  Int32 : Set
  Int64 : Set

{-# COMPILED_TYPE Int Data.Int.Int #-}
{-# COMPILED_TYPE Int8 Data.Int.Int8 #-}
{-# COMPILED_TYPE Int16 Data.Int.Int16 #-}
{-# COMPILED_TYPE Int32 Data.Int.Int32 #-}
{-# COMPILED_TYPE Int64 Data.Int.Int64 #-}

