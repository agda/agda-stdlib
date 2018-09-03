module Relation.Binary.Construction.Free.Pointed where

open import Data.Maybe
  renaming (Maybe to Pointed; nothing to ∙; just to [_]; just-injective to []-injective)
  using ()
  public
