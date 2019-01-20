{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Sum.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Relation.Nullary

type AgdaEither a b c d = Either c d
name14 = "Data.Sum.Base._⊎_"
d14 a0 a1 a2 a3 = ()
type T14 a0 a1 a2 a3 = AgdaEither a0 a1 a2 a3
pattern C26 a0 = Left a0
pattern C30 a0 = Right a0
check26 ::
  forall xa. forall xb. forall xA. forall xB. xA -> T14 xa xb xA xB
check26 = Left
check30 ::
  forall xa. forall xb. forall xA. forall xB. xB -> T14 xa xb xA xB
check30 = Right
cover14 :: AgdaEither a1 a2 a3 a4 -> ()
cover14 x
  = case x of
      Left _ -> ()
      Right _ -> ()
name50 = "Data.Sum.Base.[_,_]"
d50 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (T14 AgdaAny AgdaAny AgdaAny AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny -> AgdaAny
d50 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du50 v6 v7 v8
du50 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny -> AgdaAny
du50 v0 v1 v2
  = case coe v2 of
      C26 v3 -> coe v0 v3
      C30 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
name76 = "Data.Sum.Base.[_,_]′"
d76 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny -> AgdaAny
d76 v0 v1 v2 v3 v4 v5 = du76
du76 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny -> AgdaAny
du76 = coe du50
name86 = "Data.Sum.Base.swap"
d86 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
d86 v0 v1 v2 v3 v4 = du86 v4
du86 ::
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
du86 v0
  = case coe v0 of
      C26 v1 -> coe (C30 (coe v1))
      C30 v1 -> coe (C26 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
name108 = "Data.Sum.Base.map"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
d108 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du108 v8 v9
du108 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
du108 v0 v1
  = coe
      (du50
         (coe (\ v2 -> C26 (coe v0 v2))) (coe (\ v2 -> C30 (coe v1 v2))))
name126 = "Data.Sum.Base.map₁"
d126 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
d126 v0 v1 v2 v3 v4 v5 v6 = du126 v6
du126 ::
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
du126 v0 = coe (du108 (coe v0) (coe (\ v1 -> v1)))
name142 = "Data.Sum.Base.map₂"
d142 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
d142 v0 v1 v2 v3 v4 v5 = du142
du142 ::
  (AgdaAny -> AgdaAny) ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  T14 AgdaAny AgdaAny AgdaAny AgdaAny
du142 = coe (du108 (coe (\ v0 -> v0)))
name156 = "Data.Sum.Base._-⊎-_"
d156 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d156 = erased
name170 = "Data.Sum.Base._.fromDec"
d170 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  T14 AgdaAny AgdaAny AgdaAny (AgdaAny -> MAlonzo.Code.Data.Empty.T4)
d170 v0 v1 v2 = du170 v2
du170 ::
  MAlonzo.Code.Relation.Nullary.T14 ->
  T14 AgdaAny AgdaAny AgdaAny (AgdaAny -> MAlonzo.Code.Data.Empty.T4)
du170 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v1 -> coe (C26 (coe v1))
      MAlonzo.Code.Relation.Nullary.C26 -> coe (C30 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
name176 = "Data.Sum.Base._.toDec"
d176 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  T14
    AgdaAny AgdaAny AgdaAny (AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Relation.Nullary.T14
d176 v0 v1 v2 = du176 v2
du176 ::
  T14
    AgdaAny AgdaAny AgdaAny (AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Relation.Nullary.T14
du176 v0
  = case coe v0 of
      C26 v1 -> coe (MAlonzo.Code.Relation.Nullary.C22 (coe v1))
      C30 v1 -> coe (\ v2 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
