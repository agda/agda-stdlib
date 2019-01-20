{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Strict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Strict
import qualified MAlonzo.Code.Agda.Primitive

name14 = "Strict._.force′"
d14 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d14 v0 v1 v2 v3 = du14 v0 v1
du14 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du14 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Strict.d18 v0 v1 erased erased
name20 = "Strict._.force′-≡"
d20 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Equality.T12
d20 = erased
name22 = "Strict._.seq"
d22 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d22 v0 v1 v2 v3 v4 v5 = du22 v4 v5
du22 :: AgdaAny -> AgdaAny -> AgdaAny
du22 v0 v1 = coe (seq (coe v0) (coe v1))
name34 = "Strict._.seq-≡"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d34 = erased
