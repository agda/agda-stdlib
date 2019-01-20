{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Function where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name4 = "Function.Fun₁"
d4 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> ()
d4 = erased
name10 = "Function.Fun₂"
d10 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> ()
d10 = erased
name38 = "Function._∘_"
d38 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d38 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du38 v6 v7 v8
du38 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du38 v0 v1 v2 = coe v0 v2 (coe v1 v2)
name58 = "Function._∘′_"
d58 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d58 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du58 v6 v7 v8
du58 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du58 v0 v1 v2 = coe v0 (coe v1 v2)
name68 = "Function.id"
d68 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> AgdaAny
d68 v0 v1 v2 = du68 v2
du68 :: AgdaAny -> AgdaAny
du68 v0 = coe v0
name80 = "Function.const"
d80 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d80 v0 v1 v2 v3 v4 v5 = du80 v4
du80 :: AgdaAny -> AgdaAny
du80 v0 = coe v0
name110 = "Function._ˢ_"
d110 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d110 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du110 v6 v7 v8
du110 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du110 v0 v1 v2 = coe v0 v2 (coe v1 v2)
name138 = "Function.flip"
d138 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d138 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du138 v6 v7 v8
du138 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du138 v0 v1 v2 = coe v0 v2 v1
name158 = "Function._$_"
d158 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d158 v0 v1 v2 v3 v4 v5 = du158 v4 v5
du158 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du158 v0 v1 = coe v0 v1
name172 = "Function._$′_"
d172 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d172 v0 v1 v2 v3 v4 = du172 v4
du172 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du172 v0 = coe v0
name186 = "Function._$!_"
d186 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d186 v0 v1 v2 v3 v4 v5 = du186 v4 v5
du186 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du186 v0 v1 = coe (seq (coe v1) (coe v0 v1))
name196 = "Function._$!′_"
d196 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d196 v0 v1 v2 v3 = du196
du196 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du196 = coe du186
name210 = "Function._|>_"
d210 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d210 v0 v1 v2 v3 v4 v5 = du210 v4 v5
du210 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du210 v0 v1 = coe v1 v0
name220 = "Function._|>′_"
d220 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d220 v0 v1 v2 v3 v4 v5 = du220 v4 v5
du220 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du220 v0 v1 = coe v1 v0
name234 = "Function._⟨_⟩_"
d234 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d234 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du234 v6 v7 v8
du234 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du234 v0 v1 v2 = coe v1 v0 v2
name254 = "Function._on_"
d254 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d254 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du254 v6 v7 v8 v9
du254 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du254 v0 v1 v2 v3 = coe v0 (coe v1 v2) (coe v1 v3)
name284 = "Function._-[_]-_"
d284 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d284 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du284 v10 v11 v12 v13 v14
du284 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du284 v0 v1 v2 v3 v4 = coe v1 (coe v0 v3 v4) (coe v2 v3 v4)
name300 = "Function._∋_"
d300 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> AgdaAny
d300 v0 v1 v2 = du300 v2
du300 :: AgdaAny -> AgdaAny
du300 v0 = coe v0
name310 = "Function.typeOf"
d310 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> ()
d310 = erased
name326 = "Function.case_return_of_"
d326 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny
d326 v0 v1 v2 v3 v4 v5 = du326 v3 v5
du326 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du326 v0 v1 = coe v1 v0
name342 = "Function.case_of_"
d342 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d342 v0 v1 v2 v3 v4 v5 = du342 v4 v5
du342 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du342 v0 v1 = coe v1 v0
