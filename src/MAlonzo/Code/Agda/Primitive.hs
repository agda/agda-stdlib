{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Agda.Primitive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name4 = "Agda.Primitive.Level"
type T4 = ()
d4
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Primitive.Level"
name6 = "Agda.Primitive.lzero"
d6 = ()
name10 = "Agda.Primitive.lsuc"
d10 = (\ _ -> ())
name16 = "Agda.Primitive._⊔_"
d16 = (\ _ _ -> ())
