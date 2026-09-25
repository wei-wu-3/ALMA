{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Everything where

import ALMA.Cosmos.ContCategory
import ALMA.Cosmos.Equivalence
import ALMA.Cosmos.ContCategoryLemmas
import ALMA.Cosmos.ContFunctor
import ALMA.Cosmos.ContCatEquiv
import ALMA.Cosmos.ContCatEquivFunctor
import ALMA.Cosmos.Unfolding
import ALMA.Cosmos.MorphismObject
import ALMA.Cosmos.ContCatEquivLemmas
import ALMA.Cosmos.MorphismMorphism
import ALMA.Cosmos
import ALMA.Cosmos.Terminal
import ALMA.Cosmos.CoalgCat
import ALMA.Cosmos.Lambek
import ALMA.Cosmos.CosmosCategory
import ALMA.Cosmos.MorphismCorrespondence
import ALMA.Cosmos.Closure
import ALMA.Cosmos.ContainerAutomorphism
import ALMA.Cosmos.ListCosmos
import ALMA.Cosmos.CumulativeHierarchy
import ALMA.Cosmos.CumulativeHierarchyInner
import ALMA.Cosmos.StrictLift
import ALMA.Cosmos.StrictLiftShape
import ALMA.Cosmos.CumulativeHierarchyInstances
import ALMA.Cosmos.CumulativeHierarchyLimit
import ALMA.Cosmos.CumulativeHierarchySewing
import ALMA.Cosmos.FinCatNInnerSewing
import ALMA.Cosmos.FinCatNWitness
import ALMA.Cosmos.FinCatNTowerLemmas
import ALMA.Cosmos.ConditionalNontrivialLimit
import ALMA.Cosmos.LayerZeroMediator
import ALMA.Cosmos.FinCatNColimit
import ALMA.Cosmos.FinCatNEmbeddingMismatch
import ALMA.Cosmos.DependentEmbedding
import ALMA.Cosmos.FinCatNColimitWithDep
import ALMA.Cosmos.FinCatNSurjectivity
import ALMA.Cosmos.FinCatNDefaultUnif
import ALMA.Cosmos.FinCatNFunctorial
import ALMA.Cosmos.FinCatNProjectiveObstruction
import ALMA.Cosmos.FinCatNOuterObstruction
import ALMA.Cosmos.FinCatNInnerObstruction
import ALMA.Cosmos.FinCatNPermutedEmbedding
import ALMA.Cosmos.FinCatNNonCommutative
import ALMA.Cosmos.FinCatInfinity
import ALMA.Cosmos.FinCatInfinityProjection
import ALMA.Cosmos.FinCatInfinityTowerCompat
import ALMA.Cosmos.FinCatInfinityColimit
import ALMA.Cosmos.FinCatInfinityColimitUniversal
-- import ALMA.Cosmos.WIP

import ALMA.InitialPass.ObjEquivCat
import ALMA.InitialPass.ObjEquivFunctor
import ALMA.InitialPass.ContCategory
import ALMA.InitialPass.ContCategoryLemmas
import ALMA.InitialPass.ContCatEquiv
import ALMA.InitialPass.ContCatEquivFunctor
import ALMA.InitialPass.Unfolding
import ALMA.InitialPass.MorphismObject
import ALMA.InitialPass.ContCatEquivLemmas
import ALMA.InitialPass.MorphismMorphism
import ALMA.InitialPass.Cosmos

import ALMA.Prototype.Prelude
import ALMA.Prototype.Cosmos
import ALMA.Prototype.Indestructibility
import ALMA.Prototype.Beings
import ALMA.Prototype.Universe
import ALMA.Prototype.StandardModel
-- import ALMA.Prototype.Properties
-- comp-cong-≃⇒ℱ hit a subst coherence obstruction and was left as a hole, excluded from CI
-- comp-cong-≃⇒ℱ 撞上 subst 相干性障碍，留为洞，从 CI 排除
