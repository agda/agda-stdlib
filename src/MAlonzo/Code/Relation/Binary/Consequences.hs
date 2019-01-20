{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Consequences where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Nullary

name22 = "Relation.Binary.Consequences._.subst⟶respˡ"
d22 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d22 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du22 v5 v6 v7 v8 v9 v10 v11
du22 ::
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du22 v0 v1 v2 v3 v4 v5 v6
  = coe v1 (\ v7 -> coe v0 v7 v2) v3 v4 v5 v6
name32 = "Relation.Binary.Consequences._.subst⟶respʳ"
d32 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d32 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du32 v5 v6 v7 v8 v9 v10 v11
du32 ::
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du32 v0 v1 v2 v3 v4 v5 v6 = coe v1 (coe v0 v2) v3 v4 v5 v6
name42 = "Relation.Binary.Consequences._.subst⟶resp₂"
d42 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d42 v0 v1 v2 v3 v4 v5 v6 = du42 v5 v6
du42 ::
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du42 v0 v1
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (\ v2 -> coe v1 (coe v0 v2)))
         (coe (\ v2 -> coe v1 (\ v3 -> coe v0 v3 v2))))
name62 = "Relation.Binary.Consequences._.P-resp⟶¬P-resp"
d62 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  AgdaAny -> MAlonzo.Code.Data.Empty.T4
d62 = erased
name90 = "Relation.Binary.Consequences._.total⟶refl"
d90 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d90 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du90 v6 v7 v8 v9 v10 v11
du90 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du90 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
        -> let v8 = coe v2 v3 v4 in
           case coe v8 of
             MAlonzo.Code.Data.Sum.Base.C26 v9 -> coe v9
             MAlonzo.Code.Data.Sum.Base.C30 v9
               -> coe v6 v3 v3 v4 v5 (coe v7 v3 v4 v3 (coe v1 v3 v4 v5) v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name142 = "Relation.Binary.Consequences._.total+dec⟶dec"
d142 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d142 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du142 v6 v8 v9 v10 v11
du142 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du142 v0 v1 v2 v3 v4
  = let v5 = coe v1 v3 v4 in
    case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C26 v6
        -> coe (MAlonzo.Code.Relation.Nullary.C22 (coe v6))
      MAlonzo.Code.Data.Sum.Base.C30 v6
        -> let v7 = coe v2 v3 v4 in
           case coe v7 of
             MAlonzo.Code.Relation.Nullary.C22 v8
               -> coe (MAlonzo.Code.Relation.Nullary.C22 (coe v0 v3 v4 v8))
             MAlonzo.Code.Relation.Nullary.C26
               -> coe (\ v9 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name242 = "Relation.Binary.Consequences._.trans∧irr⟶asym"
d242 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d242 = erased
name254 = "Relation.Binary.Consequences._.irr∧antisym⟶asym"
d254 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d254 = erased
name264 = "Relation.Binary.Consequences._.asym⟶antisym"
d264 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d264 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du264 v1
du264 :: MAlonzo.Code.Agda.Primitive.T4 -> AgdaAny
du264 v0 = coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
name272 = "Relation.Binary.Consequences._.asym⟶irr"
d272 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d272 = erased
name290 = "Relation.Binary.Consequences._.tri⟶asym"
d290 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d290 = erased
name342 = "Relation.Binary.Consequences._.tri⟶irr"
d342 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d342 = erased
name402 = "Relation.Binary.Consequences._.tri⟶dec≈"
d402 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d402 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du402 v6 v7 v8
du402 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du402 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    case coe v3 of
      MAlonzo.Code.Relation.Binary.Core.C382 v4
        -> coe (\ v7 -> MAlonzo.Code.Relation.Nullary.C26) erased
      MAlonzo.Code.Relation.Binary.Core.C390 v5
        -> coe (MAlonzo.Code.Relation.Nullary.C22 (coe v5))
      MAlonzo.Code.Relation.Binary.Core.C398 v6
        -> coe (\ v7 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name438 = "Relation.Binary.Consequences._.tri⟶dec<"
d438 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d438 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du438 v6 v7 v8
du438 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du438 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    case coe v3 of
      MAlonzo.Code.Relation.Binary.Core.C382 v4
        -> coe (MAlonzo.Code.Relation.Nullary.C22 (coe v4))
      MAlonzo.Code.Relation.Binary.Core.C390 v5
        -> coe (\ v7 -> MAlonzo.Code.Relation.Nullary.C26) erased
      MAlonzo.Code.Relation.Binary.Core.C398 v6
        -> coe (\ v7 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name474 = "Relation.Binary.Consequences._.trans∧tri⟶respʳ≈"
d474 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du474 v2 v9 v10 v12
du474 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> AgdaAny
du474 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    case coe v4 of
      MAlonzo.Code.Relation.Binary.Core.C382 v5 -> coe v5
      MAlonzo.Code.Relation.Binary.Core.C390 v6
        -> coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
      MAlonzo.Code.Relation.Binary.Core.C398 v7
        -> coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
name558 = "Relation.Binary.Consequences._.trans∧tri⟶respˡ≈"
d558 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du558 v2 v8 v9 v11
du558 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  AgdaAny -> AgdaAny -> AgdaAny
du558 v0 v1 v2 v3
  = let v4 = coe v1 v3 v2 in
    case coe v4 of
      MAlonzo.Code.Relation.Binary.Core.C382 v5 -> coe v5
      MAlonzo.Code.Relation.Binary.Core.C390 v6
        -> coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
      MAlonzo.Code.Relation.Binary.Core.C398 v7
        -> coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
name626 = "Relation.Binary.Consequences._.trans∧tri⟶resp≈"
d626 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du626 v2 v9
du626 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du626 v0 v1
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (\ v2 v3 v4 v5 v6 -> du474 (coe v0) (coe v1) v2 v4))
         (coe (\ v2 v3 v4 v5 v6 -> du558 (coe v0) (coe v1) v2 v4)))
name660 = "Relation.Binary.Consequences._.wlog"
d660 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du660 v6 v7 v8 v9 v10
du660 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du660 v0 v1 v2 v3 v4
  = let v5 = coe v0 v3 v4 in
    case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C26 v6 -> coe v2 v3 v4 v6
      MAlonzo.Code.Data.Sum.Base.C30 v6 -> coe v1 v4 v3 (coe v2 v4 v3 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
name716 = "Relation.Binary.Consequences._.dec⟶weaklyDec"
d716 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny AgdaAny
d716 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du716 v6 v7 v8
du716 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny AgdaAny
du716 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    case coe v3 of
      MAlonzo.Code.Relation.Nullary.C22 v4
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe v4))
      MAlonzo.Code.Relation.Nullary.C26
        -> coe MAlonzo.Code.Data.Maybe.Base.C20
      _ -> MAlonzo.RTE.mazUnreachableError
name762 = "Relation.Binary.Consequences._.map-NonEmpty"
d762 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Core.T608 ->
  MAlonzo.Code.Relation.Binary.Core.T608
d762 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du762 v8 v9
du762 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Core.T608 ->
  MAlonzo.Code.Relation.Binary.Core.T608
du762 v0 v1
  = coe
      (MAlonzo.Code.Relation.Binary.Core.C634
         (coe (MAlonzo.Code.Relation.Binary.Core.d628 (coe v1)))
         (coe (MAlonzo.Code.Relation.Binary.Core.d630 (coe v1)))
         (coe
            v0 (MAlonzo.Code.Relation.Binary.Core.d628 (coe v1))
            (MAlonzo.Code.Relation.Binary.Core.d630 (coe v1))
            (MAlonzo.Code.Relation.Binary.Core.d632 (coe v1))))
