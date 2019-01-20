{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Sum where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Level

name16 = "Data.Sum._.isInj₁"
d16 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny AgdaAny
d16 v0 v1 v2 v3 v4 = du16 v4
du16 ::
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny AgdaAny
du16 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C26 v1
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe v1))
      MAlonzo.Code.Data.Sum.Base.C30 v1
        -> coe MAlonzo.Code.Data.Maybe.Base.C20
      _ -> MAlonzo.RTE.mazUnreachableError
name22 = "Data.Sum._.isInj₂"
d22 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny AgdaAny
d22 v0 v1 v2 v3 v4 = du22 v4
du22 ::
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny AgdaAny
du22 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C26 v1
        -> coe MAlonzo.Code.Data.Maybe.Base.C20
      MAlonzo.Code.Data.Sum.Base.C30 v1
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
name28 = "Data.Sum._.From-inj₁"
d28 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  ()
d28 = erased
name32 = "Data.Sum._.from-inj₁"
d32 ::
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  AgdaAny
d32 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C26 v1 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C30 v1
        -> coe (MAlonzo.Code.Level.C20 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
name36 = "Data.Sum._.From-inj₂"
d36 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  ()
d36 = erased
name40 = "Data.Sum._.from-inj₂"
d40 ::
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  AgdaAny
d40 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C26 v1
        -> coe (MAlonzo.Code.Level.C20 erased)
      MAlonzo.Code.Data.Sum.Base.C30 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
