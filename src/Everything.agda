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
import ALMA.Cosmos  -- carried M-base entry point: thin re-export of container base + M/Carried
import ALMA.Cosmos.M.Object  -- M-Cosmos object layer on the setoid M base (setoid 参数化 M 底座上的 M-Cosmos 对象层)
import ALMA.Cosmos.M.ContainerInstance  -- container instance type seam: old deterministic Cosmos morphism as M-Cosmos special case (容器实例类型接缝：旧确定性 Cosmos 态射作为 M-Cosmos 特例)
import ALMA.Cosmos.M.Terminal  -- M-base terminality namespace: ana + eta, zero subst (M 底座终性命名空间：ana + eta，零 subst)
import ALMA.Cosmos.M.CoalgCat  -- M-base coalgebra category + terminal coalgebra, carried bisimulation, zero subst (M 底座余代数范畴与终余代数，携带互模拟，零 subst)
import ALMA.Cosmos.M.Lambek  -- M-base Lambek lemma: terminal coalgebra weak iso collapses to ana eta, zero subst (M 底座 Lambek 引理：终余代数弱同构坍缩为 ana eta，零 subst)
import ALMA.Cosmos.M.CosmosCategory  -- M-Cosmos category: MCorrCatˢ specialised to M-Cosmos levels (M-Cosmos 范畴：MCorrCatˢ 在 M-Cosmos 层级处特化)
import ALMA.Cosmos.M.DetCongruence  -- fixed-label deterministic congruence (gow-setoid map-cong engine, zero subst) (固定标签确定性同余：gow-setoid map-cong 引擎，零 subst)
import ALMA.Cosmos.M.GenCongruence  -- label-changing deterministic congruence engine (generalises DetCongruence), zero subst
import ALMA.Cosmos.M.ListSwap  -- list universe label-changing swap01 endomorphism via GenCongruence, zero subst
import ALMA.Cosmos.M.ListSwapDef
import ALMA.Cosmos.M.MorphismCorrespondence
import ALMA.Cosmos.M.ContainerAutomorphism
import ALMA.Cosmos.M.TowerSeparation  -- FinCat n (n>=2) idN vs const0N non-bisimulation separation witness, zero subst
import ALMA.Cosmos.M.PermutationNonCommutative  -- S_n n>=3 non-abelian + 3-cycle; S_2 abelian, zero subst
import ALMA.Cosmos.M.NontrivialLimit  -- no non-trivial limit into a total/terminal target; reflection dichotomy, zero subst
import ALMA.Cosmos.M.SewingObstruction  -- M edge retract iff routing fixed point; sewing obstruction + direction dichotomy, zero subst
import ALMA.Cosmos.M.PermutedEmbedding  -- feasible invertible carried swap need not preserve F0; refutes criterion C, zero subst
import ALMA.Cosmos.M.HierarchyAbsorption  -- manifest: strict cumulative hierarchy results absorbed by M/Carried; archive guard
import ALMA.Cosmos.M.ListCosmos  -- uniform binary universe: fixed-label swap01 (n=2) edge permutation, zero subst

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

------------------------------------------------------------------------
-- Legacy container cosmos, frozen archive
-- Pre-M container terminal-coalgebra and strict cumulative-hierarchy
-- sources, retained for the record; superseded by Cosmos.M /
-- Cosmos.Carried (see Cosmos.M.HierarchyAbsorption). Modules that
-- still compile stay ACTIVE so CI keeps checking them; modules that
-- depend on names removed from the degenerated public root (the old
-- record Cosmos / out / UnitCosmos over Unfolding) are commented out.
--
-- 旧容器宇宙，冻结存档。M 之前的容器终余代数与严格累积层级源码，留档
-- 备查，已被 Cosmos.M / Cosmos.Carried 取代（覆盖清单见
-- Cosmos.M.HierarchyAbsorption）。仍可编译者保持活动、继续受 CI 检查；
-- 依赖被退化根入口移除之名（Unfolding 上的旧 record Cosmos / out /
-- UnitCosmos）者注释。
------------------------------------------------------------------------

-- Still-compiling legacy container / correspondence primitives.
-- 仍可编译的旧容器/对应基件（活动，CI 继续检查）。
import ALMA.Cosmos.ContCatEquivFunctor
import ALMA.Cosmos.ContCatEquivLemmas
import ALMA.Cosmos.MorphismMorphism
import ALMA.Cosmos.MorphismObject
import ALMA.Cosmos.MorphismObject.Covariant
import ALMA.Cosmos.MorphismObject.MorphismObject
import ALMA.Cosmos.Unfolding

-- Non-compiling after the M-root degeneration; depend directly or
-- transitively on the removed record Cosmos / out / UnitCosmos.
-- M 根退化后不可编译；直接或传递依赖被移除的 record Cosmos/out/UnitCosmos。
-- import ALMA.Cosmos.ContainerAutomorphism  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CosmosCategory  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.Closure  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CoalgCat  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.ConditionalNontrivialLimit  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CumulativeHierarchy  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CumulativeHierarchyInner  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CumulativeHierarchyInstances  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CumulativeHierarchyLimit  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.CumulativeHierarchySewing  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.DependentEmbedding  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatInfinity  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatInfinityColimit  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatInfinityColimitUniversal  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatInfinityProjection  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatInfinityTowerCompat  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNColimit  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNColimitWithDep  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNDefaultUnif  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNEmbeddingMismatch  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNFunctorial  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNInnerObstruction  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNInnerSewing  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNNonCommutative  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNOuterObstruction  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNPermutedEmbedding  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNProjectiveObstruction  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNSurjectivity  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNTowerLemmas  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.FinCatNWitness  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.Instances  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.Lambek  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.LayerZeroMediator  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.ListCosmos  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.MorphismCorrespondence  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.StrictLift  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.StrictLiftShape  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.Terminal  -- FROZEN: pre-M Unfolding/strict-hierarchy source, superseded by M/Carried
-- import ALMA.Cosmos.WIP  -- FROZEN: uniqueness blocked at FMap/cross-base layer; file retained

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
