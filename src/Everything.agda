{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Everything where

------------------------------------------------------------------------
-- Active main line. Within each group modules are listed in dependency
-- order: foundations first, then the deterministic container M-Cosmos
-- and its carried, zero-subst colimit theory.
--
-- 活跃主线。各分组内按依赖顺序排列：先基础，后确定性容器 M-Cosmos 及其
-- 携带式、零 subst 的余极限理论。
------------------------------------------------------------------------

-- Indexed M-type, and the carried correspondence kernel with its
-- pull category, terminal coalgebra, forward (push) relation family and
-- the deterministic forward category.
-- 索引 M 型，以及携带式对应内核：pull 范畴、终余代数、前向（push）关系
-- 族与确定性前向范畴。
import ALMA.Base.IndexedMType
import ALMA.Base.MCategory
import ALMA.Base.MCorr  -- Carried correspondence kernel (zero subst / cast)
                        -- 携带式对应内核（零 subst / cast）
import ALMA.Base.MCorrSetoid
import ALMA.Base.MCorrSetoidCat
import ALMA.Base.MCorrSetoidCoalg
import ALMA.Base.MCorrSetoidPush
import ALMA.Base.MCorrSetoidPushMap
import ALMA.Base.MCorrSetoidPushComp
import ALMA.Base.DetCat

-- Observation-equivalence lattice: one indexed coinductive skeleton with
-- its two axes (scale invariance, discreteness) and their degenerations.
-- 观察等价格：单一索引余归纳骨架及其两轴（尺度不变、离散）与各自退化。
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

-- Container category, its lemmas, its polynomial-functor model and their
-- equivalence; Cosmos.agda is the thin re-export entry point.
-- 容器范畴、其引理、多项式函子模型及二者等价；Cosmos.agda 为薄 re-export
-- 入口。
import ALMA.Cosmos
import ALMA.Cosmos.ContCategory
import ALMA.Cosmos.ContCategoryLemmas
import ALMA.Cosmos.ContFunctor
import ALMA.Cosmos.ContCatEquiv

-- Deterministic container M-Cosmos: object layer first, then terminal
-- coalgebra vocabulary and the category, the congruence engines, the
-- worked examples, and the separation / obstruction results.
-- 确定性容器 M-Cosmos：先对象层，再终余代数词表与范畴、同余引擎、具体实
-- 例，以及分离／障碍结果。
import ALMA.Cosmos.M.Object
import ALMA.Cosmos.M.ContainerInstance
import ALMA.Cosmos.M.Terminal
import ALMA.Cosmos.M.CoalgCat
import ALMA.Cosmos.M.Lambek
import ALMA.Cosmos.M.CosmosCategory
import ALMA.Cosmos.M.DetCongruence
import ALMA.Cosmos.M.GenCongruence
import ALMA.Cosmos.M.ListCosmos
import ALMA.Cosmos.M.ListSwap
import ALMA.Cosmos.M.ListSwapDef
import ALMA.Cosmos.M.MorphismCorrespondence
import ALMA.Cosmos.M.ContainerAutomorphism
import ALMA.Cosmos.M.PermutationNonCommutative
import ALMA.Cosmos.M.PermutedEmbedding
import ALMA.Cosmos.M.TowerSeparation
import ALMA.Cosmos.M.NontrivialLimit
import ALMA.Cosmos.M.SewingObstruction

-- Carried colimit theory, strand A: trivial-fibre pull systems and the
-- deterministic Fin towers built on them.
-- 携带式余极限理论 A：平凡纤维 pull 系统与其上的确定性 Fin 塔。
import ALMA.Cosmos.Carried.FinNatUIP
import ALMA.Cosmos.Carried.DetSys
import ALMA.Cosmos.Carried.TrivProj
import ALMA.Cosmos.Carried.FinProj
import ALMA.Cosmos.Carried.SeqColimit
import ALMA.Cosmos.Carried.LimitSystem
import ALMA.Cosmos.Carried.FinEmbed
import ALMA.Cosmos.Carried.FinColimit
import ALMA.Cosmos.Carried.FinTower
import ALMA.Cosmos.Carried.DetColimit
import ALMA.Cosmos.Carried.Boundaries

-- Strand B: setoid forward (push) systems and their standard colimits.
-- B：setoid 前向（push）系统及其标准余极限。
import ALMA.Cosmos.Carried.SeqColimitS
import ALMA.Cosmos.Carried.SeqColimitCat
import ALMA.Cosmos.Carried.ColimitPolarity
import ALMA.Cosmos.Carried.LimitSystemS
import ALMA.Cosmos.Carried.FinPushMediateS
import ALMA.Cosmos.Carried.FinPushColimitS
import ALMA.Cosmos.Carried.FinPushColimitCat

-- Strand C: the same-index wide subcategory where the general ω-chain
-- colimit reaches its boundary, with push/pull obstruction towers.
-- C：同索引宽子范畴，一般 ω-链余极限在此到达边界，含 push/pull 障碍塔。
import ALMA.Cosmos.Carried.SameIndexCatS
import ALMA.Cosmos.Carried.NontrivialPullTowerS
import ALMA.Cosmos.Carried.NontrivialPushTowerS
import ALMA.Cosmos.Carried.ChainColimitS
import ALMA.Cosmos.Carried.ChainColimitPropS

------------------------------------------------------------------------
-- Frozen archives
-- The ontological root of subst: when A is essentially determined by B
-- at parameter p₀, yet is expressed independently, the misalignment
-- between A's self-contained appearance and its instance-position
-- must manifest as subst at every point of connection between A and B.
--
-- 冻结存档
-- subst 的本体论根源：当 A 本质上由 B 在参数 p₀ 处决定，却被独立表达时，
-- A 的自足外观与其实例位置之间的错位，必然在 A 与 B 的每个连接点上以 subst
-- 的形式显露。

import ALMA.SecondPass.ContCatEquivFunctor
import ALMA.SecondPass.Unfolding
import ALMA.SecondPass.MorphismObject
import ALMA.SecondPass.MorphismObject.Covariant
import ALMA.SecondPass.MorphismObject.MorphismObject
import ALMA.SecondPass.ContCatEquivLemmas
import ALMA.SecondPass.MorphismMorphism
import ALMA.SecondPass.Cosmos
import ALMA.SecondPass.Terminal
import ALMA.SecondPass.CoalgCat
import ALMA.SecondPass.Lambek
import ALMA.SecondPass.CosmosCategory
import ALMA.SecondPass.MorphismCorrespondence
import ALMA.SecondPass.Closure
import ALMA.SecondPass.ContainerAutomorphism
import ALMA.SecondPass.ListCosmos
import ALMA.SecondPass.CumulativeHierarchy
import ALMA.SecondPass.CumulativeHierarchyInner
import ALMA.SecondPass.StrictLift
import ALMA.SecondPass.StrictLiftShape
import ALMA.SecondPass.CumulativeHierarchyInstances
import ALMA.SecondPass.CumulativeHierarchyLimit
import ALMA.SecondPass.CumulativeHierarchySewing
import ALMA.SecondPass.FinCatNInnerSewing
import ALMA.SecondPass.FinCatNWitness
import ALMA.SecondPass.FinCatNTowerLemmas
import ALMA.SecondPass.ConditionalNontrivialLimit
import ALMA.SecondPass.LayerZeroMediator
import ALMA.SecondPass.FinCatNColimit
import ALMA.SecondPass.FinCatNEmbeddingMismatch
import ALMA.SecondPass.DependentEmbedding
import ALMA.SecondPass.FinCatNColimitWithDep
import ALMA.SecondPass.FinCatNSurjectivity
import ALMA.SecondPass.FinCatNDefaultUnif
import ALMA.SecondPass.FinCatNFunctorial
import ALMA.SecondPass.FinCatNProjectiveObstruction
import ALMA.SecondPass.FinCatNOuterObstruction
import ALMA.SecondPass.FinCatNInnerObstruction
import ALMA.SecondPass.FinCatNPermutedEmbedding
import ALMA.SecondPass.FinCatNNonCommutative
import ALMA.SecondPass.FinCatInfinity
import ALMA.SecondPass.FinCatInfinityProjection
import ALMA.SecondPass.FinCatInfinityTowerCompat
import ALMA.SecondPass.FinCatInfinityColimit
import ALMA.SecondPass.FinCatInfinityColimitUniversal
import ALMA.SecondPass.Instances
-- import ALMA.SecondPass.WIP  -- uniqueness blocked at FMap/⇒ℱX layer
                               -- 唯一性在 FMap/⇒ℱX 层受阻

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
