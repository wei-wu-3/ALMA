{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Everything where

------------------------------------------------------------------------
-- Active main line
-- 活跃主线

import ALMA.Base.IndexedMType
import ALMA.Base.Container
import ALMA.Base.MCategory
import ALMA.Base.MCorr  -- Carried correspondence kernel (zero subst / cast)
                        -- 携带式对应内核（零 subst / cast）
import ALMA.Base.MCorrSetoid  -- Setoid-parameterised carried correspondence pilot
import ALMA.Base.MCorrSetoidCat  -- deterministic carried morphisms FMapˢ over setoid systems (setoid 系统上的确定性携带态射 FMapˢ)
                             -- setoid 参数化携带式对应（试点切片）

import ALMA.Base.Equivalence
import ALMA.Base.Equivalence.Core
import ALMA.Base.Equivalence.SubstTransport
import ALMA.Base.Equivalence.Properties
import ALMA.Base.Equivalence.LayeredEqGenDepth
import ALMA.Base.Equivalence.Map
import ALMA.Base.Equivalence.ScaleInvariant
import ALMA.Base.Equivalence.DiscreteEq
import ALMA.Base.Equivalence.GroupInvariant
import ALMA.Base.Equivalence.LinearDynamics
import ALMA.Base.Equivalence.TopologicalEq
import ALMA.Base.Equivalence.ManifoldEq
import ALMA.Base.Equivalence.Lattice
import ALMA.Base.Equivalence.StrongEquiv

import ALMA.Cosmos.ContCategory
import ALMA.Cosmos.ContCategoryLemmas
import ALMA.Cosmos.ContFunctor
import ALMA.Cosmos.ContCatEquiv
import ALMA.Cosmos.ContCatEquivFunctor
import ALMA.Cosmos.Unfolding
import ALMA.Cosmos.MorphismObject
import ALMA.Cosmos.MorphismObject.Covariant
import ALMA.Cosmos.MorphismObject.MorphismObject
import ALMA.Cosmos.ContCatEquivLemmas
import ALMA.Cosmos.MorphismMorphism
import ALMA.Cosmos
import ALMA.Cosmos.M.Object  -- M-Cosmos object layer on the setoid M base (setoid 参数化 M 底座上的 M-Cosmos 对象层)
import ALMA.Cosmos.M.ContainerInstance  -- container instance type seam: old deterministic Cosmos morphism as M-Cosmos special case (容器实例类型接缝：旧确定性 Cosmos 态射作为 M-Cosmos 特例)
import ALMA.Cosmos.M.Terminal  -- M-base terminality namespace: ana + eta, zero subst (M 底座终性命名空间：ana + eta，零 subst)
import ALMA.Cosmos.M.CoalgCat  -- M-base coalgebra category + terminal coalgebra, carried bisimulation, zero subst (M 底座余代数范畴与终余代数，携带互模拟，零 subst)
import ALMA.Cosmos.M.Lambek  -- M-base Lambek lemma: terminal coalgebra weak iso collapses to ana eta, zero subst (M 底座 Lambek 引理：终余代数弱同构坍缩为 ana eta，零 subst)
import ALMA.Cosmos.M.CosmosCategory  -- M-Cosmos category: MCorrCatˢ specialised to M-Cosmos levels (M-Cosmos 范畴：MCorrCatˢ 在 M-Cosmos 层级处特化)
import ALMA.Cosmos.M.DetCongruence  -- fixed-label deterministic congruence (gow-setoid map-cong engine, zero subst) (固定标签确定性同余：gow-setoid map-cong 引擎，零 subst)
import ALMA.Cosmos.M.GenCongruence  -- label-changing deterministic congruence engine (generalises DetCongruence), zero subst
import ALMA.Cosmos.M.ListSwap  -- list universe label-changing swap01 endomorphism via GenCongruence, zero subst
import ALMA.Cosmos.M.ListCosmos  -- uniform binary universe: fixed-label swap01 (n=2) edge permutation, zero subst
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
import ALMA.Cosmos.Instances
-- import ALMA.Cosmos.WIP  -- uniqueness blocked at FMap/⇒ℱX layer;
                           -- retrying carried-style below
                           -- 唯一性在 FMap/⇒ℱX 层受阻；改为携带式重新尝试

import ALMA.Cosmos.Carried.SeqColimit
import ALMA.Cosmos.Carried.DetSys
import ALMA.Cosmos.Carried.TrivProj
import ALMA.Cosmos.Carried.FinNatUIP
import ALMA.Cosmos.Carried.FinProj
import ALMA.Cosmos.Carried.LimitSystem
import ALMA.Cosmos.Carried.FinColimit
import ALMA.Cosmos.Carried.FinTower
import ALMA.Cosmos.Carried.DetColimit
import ALMA.Cosmos.Carried.Boundaries
import ALMA.Cosmos.Carried.FinEmbed

------------------------------------------------------------------------
-- Frozen archives
-- 冻结存档

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
-- import ALMA.Prototype.Properties  -- comp-cong-≃⇒ℱ hit a subst coherence
                                     -- obstruction and was left as a hole,
                                     -- excluded from CI
                                     -- comp-cong-≃⇒ℱ 撞上 subst 相干性障碍，
                                     -- 留为洞，从 CI 排除
