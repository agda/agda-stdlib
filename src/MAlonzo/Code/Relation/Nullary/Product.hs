{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Nullary.Product where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Nullary

name14 = "Relation.Nullary.Product._×-dec_"
d14 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14
d14 v0 v1 v2 v3 v4 v5 = du14 v4 v5
du14 ::
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14
du14 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v2
        -> case coe v1 of
             MAlonzo.Code.Relation.Nullary.C22 v3
               -> coe
                    (MAlonzo.Code.Relation.Nullary.C22
                       (coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v2) (coe v3))))
             MAlonzo.Code.Relation.Nullary.C26
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Relation.Nullary.C26
        -> coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
