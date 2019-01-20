{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Maybe.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.These
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary

type AgdaMaybe a b = Maybe b
name10 = "Data.Maybe.Base.Maybe"
d10 a0 a1 = ()
type T10 a0 a1 = MAlonzo.Code.Data.Maybe.Base.AgdaMaybe a0 a1
pattern C18 a0 = Just a0
pattern C20 = Nothing
check18 :: forall xa. forall xA. xA -> T10 xa xA
check18 = Just
check20 :: forall xa. forall xA. T10 xa xA
check20 = Nothing
cover10 :: MAlonzo.Code.Data.Maybe.Base.AgdaMaybe a1 a2 -> ()
cover10 x
  = case x of
      Just _ -> ()
      Nothing -> ()
name22 = "Data.Maybe.Base.boolToMaybe"
d22 :: Bool -> T10 AgdaAny MAlonzo.Code.Agda.Builtin.Unit.T6
d22 v0 = if coe v0 then coe (C18 erased) else coe C20
name28 = "Data.Maybe.Base.is-just"
d28 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> T10 AgdaAny AgdaAny -> Bool
d28 v0 v1 v2 = du28 v2
du28 :: T10 AgdaAny AgdaAny -> Bool
du28 v0
  = case coe v0 of
      C18 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C10
      C20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C8
      _ -> MAlonzo.RTE.mazUnreachableError
name34 = "Data.Maybe.Base.is-nothing"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> T10 AgdaAny AgdaAny -> Bool
d34 v0 v1 v2 = du34 v2
du34 :: T10 AgdaAny AgdaAny -> Bool
du34 v0
  = coe (MAlonzo.Code.Data.Bool.Base.d6 (coe (du28 (coe v0))))
name40 = "Data.Maybe.Base.decToMaybe"
d40 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> T10 AgdaAny AgdaAny
d40 v0 v1 v2 = du40 v2
du40 :: MAlonzo.Code.Relation.Nullary.T14 -> T10 AgdaAny AgdaAny
du40 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v1 -> coe (C18 (coe v1))
      MAlonzo.Code.Relation.Nullary.C26 -> coe C20
      _ -> MAlonzo.RTE.mazUnreachableError
name56 = "Data.Maybe.Base.maybe"
d56 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (T10 AgdaAny AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T10 AgdaAny AgdaAny -> AgdaAny
d56 v0 v1 v2 v3 v4 v5 v6 = du56 v4 v5 v6
du56 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> T10 AgdaAny AgdaAny -> AgdaAny
du56 v0 v1 v2
  = case coe v2 of
      C18 v3 -> coe v0 v3
      C20 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name76 = "Data.Maybe.Base.maybe′"
d76 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T10 AgdaAny AgdaAny -> AgdaAny
d76 v0 v1 v2 v3 = du76
du76 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> T10 AgdaAny AgdaAny -> AgdaAny
du76 = coe du56
name82 = "Data.Maybe.Base.fromMaybe"
d82 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> T10 AgdaAny AgdaAny -> AgdaAny
d82 v0 v1 = du82
du82 :: AgdaAny -> T10 AgdaAny AgdaAny -> AgdaAny
du82 = coe du76 (\ v0 -> v0)
name92 = "Data.Maybe.Base._.From-just"
d92 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> T10 AgdaAny AgdaAny -> ()
d92 = erased
name96 = "Data.Maybe.Base._.from-just"
d96 :: T10 AgdaAny AgdaAny -> AgdaAny
d96 v0
  = case coe v0 of
      C18 v1 -> coe v1
      C20 -> coe (MAlonzo.Code.Level.C20 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
name108 = "Data.Maybe.Base.map"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
d108 v0 v1 v2 v3 v4 = du108 v4
du108 ::
  (AgdaAny -> AgdaAny) -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
du108 v0 = coe (du56 (coe (\ v1 -> C18 (coe v0 v1))) (coe C20))
name116 = "Data.Maybe.Base._<∣>_"
d116 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
d116 v0 v1 v2 v3 = du116 v2 v3
du116 ::
  T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
du116 v0 v1
  = case coe v0 of
      C18 v2 -> coe v0
      C20 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name140 = "Data.Maybe.Base._.alignWith"
d140 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Data.These.T12 -> AgdaAny) ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
d140 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du140 v6 v7 v8
du140 ::
  (MAlonzo.Code.Data.These.T12 -> AgdaAny) ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
du140 v0 v1 v2
  = case coe v1 of
      C18 v3
        -> case coe v2 of
             C18 v4
               -> coe
                    (C18 (coe v0 (MAlonzo.Code.Data.These.C26 (coe v3) (coe v4))))
             C20 -> coe (C18 (coe v0 (MAlonzo.Code.Data.These.C22 (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C20
        -> case coe v2 of
             C18 v3 -> coe (C18 (coe v0 (MAlonzo.Code.Data.These.C24 (coe v3))))
             C20 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name158 = "Data.Maybe.Base._.zipWith"
d158 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
d158 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du158 v6 v7 v8
du158 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny -> T10 AgdaAny AgdaAny
du158 v0 v1 v2
  = let v3 = C20 in
    case coe v1 of
      C18 v4
        -> case coe v2 of
             C18 v5 -> coe (C18 (coe v0 v4 v5))
             _ -> coe v3
      _ -> coe v3
name178 = "Data.Maybe.Base._.align"
d178 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  T10 AgdaAny AgdaAny ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny MAlonzo.Code.Data.These.T12
d178 v0 v1 v2 v3 = du178
du178 ::
  T10 AgdaAny AgdaAny ->
  T10 AgdaAny AgdaAny -> T10 AgdaAny MAlonzo.Code.Data.These.T12
du178 = coe (du140 (coe (\ v0 -> v0)))
name180 = "Data.Maybe.Base._.zip"
d180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  T10 AgdaAny AgdaAny ->
  T10 AgdaAny AgdaAny ->
  T10 AgdaAny MAlonzo.Code.Agda.Builtin.Sigma.T14
d180 v0 v1 v2 v3 = du180
du180 ::
  T10 AgdaAny AgdaAny ->
  T10 AgdaAny AgdaAny ->
  T10 AgdaAny MAlonzo.Code.Agda.Builtin.Sigma.T14
du180 = coe (du158 (coe MAlonzo.Code.Agda.Builtin.Sigma.C32))
name194 = "Data.Maybe.Base._.thisM"
d194 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () -> AgdaAny -> T10 AgdaAny AgdaAny -> MAlonzo.Code.Data.These.T12
d194 v0 v1 v2 v3 v4 = du194 v4
du194 ::
  AgdaAny -> T10 AgdaAny AgdaAny -> MAlonzo.Code.Data.These.T12
du194 v0
  = coe
      du76 (MAlonzo.Code.Data.These.C26 (coe v0))
      (MAlonzo.Code.Data.These.C22 (coe v0))
name198 = "Data.Maybe.Base._.thatM"
d198 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () -> T10 AgdaAny AgdaAny -> AgdaAny -> MAlonzo.Code.Data.These.T12
d198 v0 v1 v2 v3 = du198
du198 ::
  T10 AgdaAny AgdaAny -> AgdaAny -> MAlonzo.Code.Data.These.T12
du198
  = coe du76 MAlonzo.Code.Data.These.C26 MAlonzo.Code.Data.These.C24
