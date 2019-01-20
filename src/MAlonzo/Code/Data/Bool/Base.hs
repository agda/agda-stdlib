{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Bool.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive

name6 = "Data.Bool.Base.not"
d6 :: Bool -> Bool
d6 v0
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Bool.C8
      else coe MAlonzo.Code.Agda.Builtin.Bool.C10
name8 = "Data.Bool.Base.T"
d8 :: Bool -> ()
d8 = erased
name14 = "Data.Bool.Base.if_then_else_"
d14 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> Bool -> AgdaAny -> AgdaAny -> AgdaAny
d14 v0 v1 v2 v3 v4 = du14 v2 v3 v4
du14 :: Bool -> AgdaAny -> AgdaAny -> AgdaAny
du14 v0 v1 v2 = if coe v0 then coe v1 else coe v2
name24 = "Data.Bool.Base._∧_"
d24 :: Bool -> Bool -> Bool
d24 v0 v1 = if coe v0 then coe v1 else coe v0
name30 = "Data.Bool.Base._∨_"
d30 :: Bool -> Bool -> Bool
d30 v0 v1 = if coe v0 then coe v0 else coe v1
name36 = "Data.Bool.Base._xor_"
d36 :: Bool -> Bool -> Bool
d36 v0 v1 = if coe v0 then coe (d6 (coe v1)) else coe v1
