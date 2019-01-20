{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.These where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum.Base

name12 = "Data.These.These"
d12 a0 a1 a2 a3 = ()
data T12 = C22 AgdaAny | C24 AgdaAny | C26 AgdaAny AgdaAny
name40 = "Data.These._.fromSum"
d40 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T12
d40 v0 v1 v2 v3 = du40
du40 ::
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T12
du40 = coe MAlonzo.Code.Data.Sum.Base.du76 C22 C24
name62 = "Data.These.map"
d62 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T12 -> T12
d62 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du62 v8 v9 v10
du62 :: (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T12 -> T12
du62 v0 v1 v2
  = case coe v2 of
      C22 v3 -> coe (C22 (coe v0 v3))
      C24 v3 -> coe (C24 (coe v1 v3))
      C26 v3 v4 -> coe (C26 (coe v0 v3) (coe v1 v4))
      _ -> MAlonzo.RTE.mazUnreachableError
name98 = "Data.These.map₁"
d98 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> T12 -> T12
d98 v0 v1 v2 v3 v4 v5 v6 = du98 v6
du98 :: (AgdaAny -> AgdaAny) -> T12 -> T12
du98 v0 = coe (du62 (coe v0) (coe (\ v1 -> v1)))
name116 = "Data.These.map₂"
d116 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> T12 -> T12
d116 v0 v1 v2 v3 v4 v5 = du116
du116 :: (AgdaAny -> AgdaAny) -> T12 -> T12
du116 = coe (du62 (coe (\ v0 -> v0)))
name134 = "Data.These._.fold"
d134 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T12 -> AgdaAny
d134 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du134 v6 v7 v8 v9
du134 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T12 -> AgdaAny
du134 v0 v1 v2 v3
  = case coe v3 of
      C22 v4 -> coe v0 v4
      C24 v4 -> coe v1 v4
      C26 v4 v5 -> coe v2 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
name162 = "Data.These._.swap"
d162 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> () -> T12 -> T12
d162 v0 v1 v2 v3 = du162
du162 :: T12 -> T12
du162
  = coe
      (du134
         (coe C24) (coe C22) (coe (\ v0 v1 -> C26 (coe v1) (coe v0))))
name192 = "Data.These._.alignWith"
d192 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () -> (T12 -> AgdaAny) -> (T12 -> AgdaAny) -> T12 -> T12 -> T12
d192 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = du192 v12 v13 v14 v15
du192 :: (T12 -> AgdaAny) -> (T12 -> AgdaAny) -> T12 -> T12 -> T12
du192 v0 v1 v2 v3
  = case coe v2 of
      C22 v4
        -> case coe v3 of
             C22 v5 -> coe (C22 (coe v0 (C26 (coe v4) (coe v5))))
             C24 v5 -> coe (C26 (coe v0 v2) (coe v1 v3))
             C26 v5 v6
               -> coe
                    (C26 (coe v0 (C26 (coe v4) (coe v5))) (coe v1 (C24 (coe v6))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C24 v4
        -> case coe v3 of
             C22 v5 -> coe (C26 (coe v0 (C24 (coe v5))) (coe v1 (C22 (coe v4))))
             C24 v5 -> coe (C24 (coe v1 (C26 (coe v4) (coe v5))))
             C26 v5 v6
               -> coe
                    (C26 (coe v0 (C24 (coe v5))) (coe v1 (C26 (coe v4) (coe v6))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C26 v4 v5
        -> case coe v3 of
             C22 v6
               -> coe
                    (C26 (coe v0 (C26 (coe v4) (coe v6))) (coe v1 (C22 (coe v5))))
             C24 v6
               -> coe
                    (C26 (coe v0 (C22 (coe v4))) (coe v1 (C26 (coe v5) (coe v6))))
             C26 v6 v7
               -> coe
                    (C26
                       (coe v0 (C26 (coe v4) (coe v6))) (coe v1 (C26 (coe v5) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name278 = "Data.These._.align"
d278 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> () -> () -> T12 -> T12 -> T12
d278 v0 v1 v2 v3 v4 v5 v6 v7 = du278
du278 :: T12 -> T12 -> T12
du278 = coe (du192 (coe (\ v0 -> v0)) (coe (\ v0 -> v0)))
name288 = "Data.These._.leftMost"
d288 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> T12 -> AgdaAny
d288 v0 v1 = du288
du288 :: T12 -> AgdaAny
du288
  = coe
      (du134 (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 v1 -> v0)))
name290 = "Data.These._.rightMost"
d290 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> T12 -> AgdaAny
d290 v0 v1 = du290
du290 :: T12 -> AgdaAny
du290
  = coe
      (du134 (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 v1 -> v1)))
name292 = "Data.These._.mergeThese"
d292 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> T12 -> AgdaAny
d292 v0 v1 = du292
du292 :: (AgdaAny -> AgdaAny -> AgdaAny) -> T12 -> AgdaAny
du292 = coe (du134 (coe (\ v0 -> v0)) (coe (\ v0 -> v0)))
