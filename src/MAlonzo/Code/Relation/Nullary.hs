{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Nullary where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Empty.Irrelevant

name6 = "Relation.Nullary.¬_"
d6 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> ()
d6 = erased
name14 = "Relation.Nullary.Dec"
d14 a0 a1 = ()
data T14 = C22 AgdaAny | C26
name32 = "Relation.Nullary.recompute"
d32 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> T14 -> AgdaAny -> AgdaAny
d32 v0 v1 v2 v3 = du32 v0 v2
du32 :: MAlonzo.Code.Agda.Primitive.T4 -> T14 -> AgdaAny
du32 v0 v1
  = case coe v1 of
      C22 v2 -> coe v2
      C26 -> coe MAlonzo.Code.Data.Empty.Irrelevant.d10 v0 erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
