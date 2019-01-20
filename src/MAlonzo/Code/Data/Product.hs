{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Product where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive

name6 = "Data.Product.Σ.fst"
d6 :: MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
d6 v0 = coe (MAlonzo.Code.Agda.Builtin.Sigma.d28 (coe v0))
name8 = "Data.Product.Σ.snd"
d8 :: MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
d8 v0 = coe (MAlonzo.Code.Agda.Builtin.Sigma.d30 (coe v0))
name18 = "Data.Product.Σ-syntax"
d18 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> (AgdaAny -> ()) -> ()
d18 = erased
name26 = "Data.Product.∃"
d26 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> (AgdaAny -> ()) -> ()
d26 = erased
name31 = "Agda.Builtin.Sigma.Σ"
d31 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
name34 = "Data.Product.∃-syntax"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> (AgdaAny -> ()) -> ()
d34 = erased
name42 = "Data.Product.∄"
d42 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> (AgdaAny -> ()) -> ()
d42 = erased
name52 = "Data.Product.∄-syntax"
d52 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> (AgdaAny -> ()) -> ()
d52 = erased
name68 = "Data.Product.∃₂"
d68 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d68 = erased
name84 = "Data.Product._×_"
d84 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> () -> ()
d84 = erased
name100 = "Data.Product._,′_"
d100 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d100 v0 v1 v2 v3 = du100
du100 :: AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du100 = coe MAlonzo.Code.Agda.Builtin.Sigma.C32
name110 = "Data.Product.∃!"
d110 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d110 = erased
name130 = "Data.Product.-,_"
d130 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d130 v0 v1 v2 v3 v4 v5 = du130 v4 v5
du130 :: AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du130 v0 v1
  = coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v0) (coe v1))
name156 = "Data.Product.<_,_>"
d156 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d156 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du156 v6 v7 v8
du156 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du156 v0 v1 v2
  = coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v0 v2) (coe v1 v2))
name184 = "Data.Product.map"
d184 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du184 v8 v9 v10
du184 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du184 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v3 v4
        -> coe
             (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v0 v3) (coe v1 v3 v4))
      _ -> MAlonzo.RTE.mazUnreachableError
name206 = "Data.Product.map₁"
d206 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d206 v0 v1 v2 v3 v4 v5 v6 = du206 v6
du206 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du206 v0 = coe (du184 (coe v0) (coe (\ v1 v2 -> v2)))
name224 = "Data.Product.map₂"
d224 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d224 v0 v1 v2 v3 v4 v5 v6 = du224 v6
du224 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du224 v0 = coe (du184 (coe (\ v1 -> v1)) (coe v0))
name258 = "Data.Product.zip"
d258 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = du258 v12 v13 v14 v15
du258 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du258 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
               -> coe
                    (MAlonzo.Code.Agda.Builtin.Sigma.C32
                       (coe v0 v4 v6) (coe v1 v4 v6 v5 v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name280 = "Data.Product.swap"
d280 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d280 v0 v1 v2 v3 v4 = du280 v4
du280 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du280 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v1 v2
        -> coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
name298 = "Data.Product._-×-_"
d298 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d298 = erased
name320 = "Data.Product._-,-_"
d320 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d320 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du320 v8 v9 v10 v11
du320 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du320 v0 v1 v2 v3
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v0 v2 v3) (coe v1 v2 v3))
name344 = "Data.Product.curry"
d344 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d344 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du344 v6 v7 v8
du344 ::
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du344 v0 v1 v2
  = coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v1) (coe v2))
name364 = "Data.Product.curry′"
d364 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d364 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du364 v6 v7 v8
du364 ::
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du364 v0 v1 v2
  = coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v1) (coe v2))
name384 = "Data.Product.uncurry"
d384 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
d384 v0 v1 v2 v3 v4 v5 v6 v7 = du384 v6 v7
du384 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
du384 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v2 v3 -> coe v0 v2 v3
      _ -> MAlonzo.RTE.mazUnreachableError
name404 = "Data.Product.uncurry′"
d404 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
d404 v0 v1 v2 v3 v4 v5 = du404
du404 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
du404 = coe du384
