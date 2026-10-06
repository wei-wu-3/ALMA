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
-- import ALMA.Cosmos.ContCatEquivFunctor  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.Unfolding  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.MorphismObject  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.MorphismObject.Covariant  -- ARCHIVED (M endgame): superseded by MCorr/MCorrSetoid; file retained
-- import ALMA.Cosmos.MorphismObject.MorphismObject  -- ARCHIVED (M endgame): superseded by MCorr/MCorrSetoid; file retained
-- import ALMA.Cosmos.ContCatEquivLemmas  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.MorphismMorphism  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
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
-- import ALMA.Cosmos.Terminal  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CoalgCat  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.Lambek  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CosmosCategory  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.MorphismCorrespondence  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.Closure  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.ContainerAutomorphism  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.ListCosmos  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CumulativeHierarchy  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CumulativeHierarchyInner  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.StrictLift  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.StrictLiftShape  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CumulativeHierarchyInstances  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CumulativeHierarchyLimit  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.CumulativeHierarchySewing  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNInnerSewing  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNWitness  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNTowerLemmas  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.ConditionalNontrivialLimit  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.LayerZeroMediator  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNColimit  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNEmbeddingMismatch  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.DependentEmbedding  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNColimitWithDep  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNSurjectivity  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNDefaultUnif  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNFunctorial  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNProjectiveObstruction  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNOuterObstruction  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNInnerObstruction  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNPermutedEmbedding  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatNNonCommutative  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatInfinity  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatInfinityProjection  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatInfinityTowerCompat  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatInfinityColimit  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.FinCatInfinityColimitUniversal  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
-- import ALMA.Cosmos.Instances  -- ARCHIVED (M endgame): superseded by M/Carried; file retained
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
