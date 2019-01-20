{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Agda.Builtin.Sigma where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name14 = "Agda.Builtin.Sigma.Σ"
d14 a0 a1 a2 a3 = ()
data T14 = C32 AgdaAny AgdaAny
name28 = "Agda.Builtin.Sigma.Σ.fst"
d28 :: T14 -> AgdaAny
d28 v0
  = case coe v0 of
      C32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name30 = "Agda.Builtin.Sigma.Σ.snd"
d30 :: T14 -> AgdaAny
d30 v0
  = case coe v0 of
      C32 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
