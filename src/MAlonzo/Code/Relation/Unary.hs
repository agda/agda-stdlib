{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Unary where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum.Base

name8 = "Relation.Unary.Pred"
d8 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> ()
d8 = erased
name22 = "Relation.Unary._.∅"
d22 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> ()
d22 = erased
name26 = "Relation.Unary._.｛_｝"
d26 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> AgdaAny -> ()
d26 = erased
name32 = "Relation.Unary._.U"
d32 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> ()
d32 = erased
name38 = "Relation.Unary._._∈_"
d38 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 -> AgdaAny -> (AgdaAny -> ()) -> ()
d38 = erased
name46 = "Relation.Unary._._∉_"
d46 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 -> AgdaAny -> (AgdaAny -> ()) -> ()
d46 = erased
name56 = "Relation.Unary._._⊆_"
d56 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d56 = erased
name68 = "Relation.Unary._._⊇_"
d68 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d68 = erased
name78 = "Relation.Unary._._⊈_"
d78 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d78 = erased
name88 = "Relation.Unary._._⊉_"
d88 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d88 = erased
name98 = "Relation.Unary._._⊂_"
d98 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d98 = erased
name108 = "Relation.Unary._._⊃_"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d108 = erased
name118 = "Relation.Unary._._⊄_"
d118 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d118 = erased
name128 = "Relation.Unary._._⊅_"
d128 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d128 = erased
name138 = "Relation.Unary._._⊆′_"
d138 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d138 = erased
name150 = "Relation.Unary._._⊇′_"
d150 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d150 = erased
name160 = "Relation.Unary._._⊈′_"
d160 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d160 = erased
name170 = "Relation.Unary._._⊉′_"
d170 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d170 = erased
name180 = "Relation.Unary._._⊂′_"
d180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d180 = erased
name190 = "Relation.Unary._._⊃′_"
d190 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d190 = erased
name200 = "Relation.Unary._._⊄′_"
d200 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d200 = erased
name210 = "Relation.Unary._._⊅′_"
d210 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d210 = erased
name218 = "Relation.Unary._.Empty"
d218 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> ()
d218 = erased
name226 = "Relation.Unary._.Satisfiable"
d226 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> ()
d226 = erased
name234 = "Relation.Unary._.Universal"
d234 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> ()
d234 = erased
name242 = "Relation.Unary._.IUniversal"
d242 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> ()
d242 = erased
name250 = "Relation.Unary._.Decidable"
d250 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> ()
d250 = erased
name258 = "Relation.Unary._.Irrelevant"
d258 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> ()
d258 = erased
name270 = "Relation.Unary._.∁"
d270 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 -> (AgdaAny -> ()) -> AgdaAny -> ()
d270 = erased
name280 = "Relation.Unary._._≬_"
d280 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d280 = erased
name292 = "Relation.Unary._._∪_"
d292 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> AgdaAny -> ()
d292 = erased
name304 = "Relation.Unary._._∩_"
d304 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> AgdaAny -> ()
d304 = erased
name316 = "Relation.Unary._._⇒_"
d316 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> AgdaAny -> ()
d316 = erased
name330 = "Relation.Unary._.⋃"
d330 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> ()
d330 = erased
name346 = "Relation.Unary._.⋂"
d346 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> ()
d346 = erased
name366 = "Relation.Unary._⊢_"
d366 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> ()) -> AgdaAny -> ()
d366 = erased
name386 = "Relation.Unary._⟨×⟩_"
d386 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()
d386 = erased
name408 = "Relation.Unary._⟨⊙⟩_"
d408 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()
d408 = erased
name428 = "Relation.Unary._⟨⊎⟩_"
d428 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny ->
  ()
d428 = erased
name446 = "Relation.Unary._⟨→⟩_"
d446 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d446 = erased
name470 = "Relation.Unary._⟨·⟩_"
d470 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
d470 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du470 v8 v9
du470 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> AgdaAny
du470 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v2 v3
        -> coe v3 (MAlonzo.Code.Agda.Builtin.Sigma.d28 (coe v0)) v2
      _ -> MAlonzo.RTE.mazUnreachableError
name490 = "Relation.Unary._~"
d490 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()
d490 = erased
name510 = "Relation.Unary._⟨∘⟩_"
d510 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()
d510 = erased
name538 = "Relation.Unary._//_"
d538 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()
d538 = erased
name564 = "Relation.Unary._\\\\_"
d564 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> ()
d564 = erased
