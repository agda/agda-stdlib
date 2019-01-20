{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.PropositionalEquality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary

name26 = "Relation.Binary.PropositionalEquality.subst₂"
d26 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny -> AgdaAny
d26 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 = du26 v12
du26 :: AgdaAny -> AgdaAny
du26 v0 = coe v0
name46 = "Relation.Binary.PropositionalEquality.cong"
d46 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d46 = erased
name66 = "Relation.Binary.PropositionalEquality.cong-app"
d66 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d66 = erased
name92 = "Relation.Binary.PropositionalEquality.cong₂"
d92 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d92 = erased
name98 = "Relation.Binary.PropositionalEquality.setoid"
d98 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Binary.T128
d98 v0 v1 = du98
du98 :: MAlonzo.Code.Relation.Binary.T128
du98
  = coe
      (\ v0 v1 v2 -> MAlonzo.Code.Relation.Binary.C971 v2) erased erased
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du68
name106 = "Relation.Binary.PropositionalEquality.decSetoid"
d106 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Relation.Binary.T200
d106 v0 v1 v2 = du106 v2
du106 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Relation.Binary.T200
du106 v0
  = coe
      (\ v1 v2 v3 -> MAlonzo.Code.Relation.Binary.C1311 v3) erased erased
      (MAlonzo.Code.Relation.Binary.C1173
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du68)
         (coe v0))
name114 = "Relation.Binary.PropositionalEquality.isPreorder"
d114 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Binary.T16
d114 v0 v1 = du114
du114 :: MAlonzo.Code.Relation.Binary.T16
du114
  = coe
      (MAlonzo.Code.Relation.Binary.C25
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du68)
         (coe (\ v0 v1 v2 -> v2)) erased)
name118 = "Relation.Binary.PropositionalEquality.preorder"
d118 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Binary.T74
d118 v0 v1 = du118
du118 :: MAlonzo.Code.Relation.Binary.T74
du118
  = coe
      (\ v0 v1 v2 v3 -> MAlonzo.Code.Relation.Binary.C739 v3) erased
      erased erased du114
name138 = "Relation.Binary.PropositionalEquality._.≡-≟-identity"
d138 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d138 v0 v1 v2 v3 v4 v5 = du138 v0 v2 v3 v4
du138 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du138 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    case coe v4 of
      MAlonzo.Code.Relation.Nullary.C22 v5
        -> coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v5) erased)
      MAlonzo.Code.Relation.Nullary.C26
        -> coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
name156 = "Relation.Binary.PropositionalEquality._.≢-≟-identity"
d156 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T12 ->
   MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d156 v0 v1 v2 v3 v4 v5 = du156 v0 v2 v3 v4
du156 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du156 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    case coe v4 of
      MAlonzo.Code.Relation.Nullary.C22 v5
        -> coe MAlonzo.Code.Data.Empty.d10 v0 erased erased
      MAlonzo.Code.Relation.Nullary.C26
        -> coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
name180 = "Relation.Binary.PropositionalEquality._→-setoid_"
d180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> MAlonzo.Code.Relation.Binary.T128
d180 v0 v1 v2 v3 = du180
du180 :: MAlonzo.Code.Relation.Binary.T128
du180
  = coe
      (MAlonzo.Code.Function.Equality.du204
         (coe
            (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du96
               (coe du98))))
name198 = "Relation.Binary.PropositionalEquality._≗_"
d198 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d198 = erased
name216 = "Relation.Binary.PropositionalEquality.:→-to-Π"
d216 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Function.Equality.T16
d216 v0 v1 v2 v3 v4 v5 = du216 v4 v5
du216 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Function.Equality.T16
du216 v0 v1
  = coe
      (MAlonzo.Code.Function.Equality.C29
         (coe v1) (coe (\ v2 v3 v4 -> du234 (coe v0) (coe v1) v2)))
name228 = "Relation.Binary.PropositionalEquality._._._≈_"
d228 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d228 = erased
name234 = "Relation.Binary.PropositionalEquality._.cong′"
d234 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d234 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du234 v4 v5 v6
du234 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du234 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d40
      (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d78 (coe v0))
      v2 (coe v1 v2)
name246 = "Relation.Binary.PropositionalEquality.→-to-⟶"
d246 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Binary.T128 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Function.Equality.T16
d246 v0 v1 v2 v3 v4 = du246 v4
du246 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Function.Equality.T16
du246 v0
  = coe
      (du216
         (coe
            (\ v1 v2 v3 ->
               MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.C581 v3)
            erased erased
            (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du32
               (coe (MAlonzo.Code.Relation.Binary.d144 (coe v0))))))
name264 = "Relation.Binary.PropositionalEquality.Reveal_·_is_"
d264 a0 a1 a2 a3 a4 a5 a6 = ()
data T264 = C284
name282 = "Relation.Binary.PropositionalEquality.Reveal_·_is_.eq"
d282 :: T264 -> MAlonzo.Code.Agda.Builtin.Equality.T12
d282 = erased
name300 = "Relation.Binary.PropositionalEquality.inspect"
d300 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> T264
d300 = erased
name316
  = "Relation.Binary.PropositionalEquality.≡-Reasoning.begin_"
d316 ::
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d316 = erased
name324 = "Relation.Binary.PropositionalEquality.≡-Reasoning._≡⟨⟩_"
d324 ::
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d324 = erased
name334
  = "Relation.Binary.PropositionalEquality.≡-Reasoning._≡⟨_⟩_"
d334 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d334 = erased
name342 = "Relation.Binary.PropositionalEquality.≡-Reasoning._∎"
d342 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d342 = erased
name348 = "Relation.Binary.PropositionalEquality.Extensionality"
d348 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> ()
d348 = erased
name374
  = "Relation.Binary.PropositionalEquality.extensionality-for-lower-levels"
d374 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d374 = erased
name402 = "Relation.Binary.PropositionalEquality.∀-extensionality"
d402 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d402 = erased
name424 = "Relation.Binary.PropositionalEquality.isPropositional"
d424 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> ()
d424 = erased
name442 = "Relation.Binary.PropositionalEquality.trans-reflʳ"
d442 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d442 = erased
name462 = "Relation.Binary.PropositionalEquality.trans-assoc"
d462 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d462 = erased
name474 = "Relation.Binary.PropositionalEquality.trans-symˡ"
d474 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d474 = erased
name486 = "Relation.Binary.PropositionalEquality.trans-symʳ"
d486 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d486 = erased
name498 = "Relation.Binary.PropositionalEquality.cong-id"
d498 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d498 = erased
name522 = "Relation.Binary.PropositionalEquality.cong-∘"
d522 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d522 = erased
name544 = "Relation.Binary.PropositionalEquality.subst-subst"
d544 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d544 = erased
name568 = "Relation.Binary.PropositionalEquality.subst-∘"
d568 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d568 = erased
name586 = "Relation.Binary.PropositionalEquality.subst-subst-sym"
d586 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d586 = erased
name604 = "Relation.Binary.PropositionalEquality.subst-sym-subst"
d604 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12
d604 = erased
name636 = "Relation.Binary.PropositionalEquality.subst-application"
d636 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d636 = erased
name660 = "Relation.Binary.PropositionalEquality.naturality"
d660 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d660 = erased
name682 = "Relation.Binary.PropositionalEquality.cong-≡id"
d682 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d682 = erased
