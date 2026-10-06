------------------------------------------------------------------------
-- Absorption manifest for the strict cumulative hierarchy.
--
-- The legacy cross-universe cumulative hierarchy
--
--   Cosmos/StrictLift.agda
--   Cosmos/CumulativeHierarchy.agda
--   Cosmos/CumulativeHierarchyInner.agda
--   Cosmos/StrictLiftShape.agda
--   Cosmos/CumulativeHierarchyInstances.agda
--   Cosmos/CumulativeHierarchyLimit.agda
--   Cosmos/CumulativeHierarchySewing.agda
--   Cosmos/DependentEmbedding.agda
--
-- together with the FinCatN* / FinCatInfinity* tower cluster built on
-- top of them, existed to grow a container universe one level per
-- iteration and to thread embeddings (strictEmbed / dep-embed) and
-- their limits through that tower.  It carries 40+ subst sites: ~38 are
-- native Agda Lift/lower commutation across universes, and the rest are
-- container-morphism position transports (subst PosOf along shape
-- equations).
--
-- On the carried M base the reason for the whole tower disappears:
--
--   * iterating ShapeCat is iterating the M index
--     MO.I = Sigma (Obj C) (ShapeOf FC), so the strict level tower is
--     absorbed inductively by the indexed coinductive type;
--   * CosmosM is universe-polymorphic in a single level
--     Set (o ⊔ h ⊔ e ⊔ s ⊔ p): there is no per-step lsuc lifting, hence
--     no Lift/lower commutation to carry;
--   * edge fibres carry their own adjunction FiberAdjˢ, so moving
--     positions along a shape equation is a function (to/fro), not a
--     subst.
--
-- Every RESULT of the strict hierarchy is therefore re-established on
-- M / Carried.  This module has no definitions: its import closure is
-- the formal coverage manifest.  Removing or weakening any replacement
-- below makes this module fail to compile, which is the guard that
-- licenses archiving the legacy cluster.
--
-- Coverage map (legacy result -> replacement):
--
--   finite / sequential tower colimit universal property
--     (existence, triangle, uniqueness)
--     -> Carried.SeqColimit (IsColimit/Colimit),
--        Carried.FinColimit (FinCone/colimitUniv),
--        Carried.FinTower, Carried.LimitSystem, Carried.DetColimit
--
--   per-layer / limit terminality; unit (singleton) tower lifted limit
--     -> M.Object / M.CoalgCat / M.Terminal (cosmosMIsTerminal, ana),
--        M.NontrivialLimit (total fibre collapses),
--        M.SewingObstruction (singleton sufficiency direction)
--
--   sewing obstruction + outer/inner direction dichotomy
--     -> M.SewingObstruction
--
--   permuted embedding refuting criterion C
--     -> M.PermutedEmbedding
--
--   idN != const0N bisimulation separation
--     -> M.TowerSeparation
--
--   S_n non-abelian for n >= 3, order-3 cycle
--     -> M.PermutationNonCommutative
--
--   projective / surjective / inner-outer boundary obstructions
--     -> Carried.Boundaries (inject₁ non-surjective, clamp saturation)
--
--   cross-level embedding mismatch diagnostic
--     -> no M counterpart: the two embeddings it compares belong to the
--        strict tower that M absorbs; the diagnostic is archived with
--        the tower it diagnoses.
--
-- The native Lift/lower commutation lemmas are NOT re-homed: an audit
-- shows their only consumers are modules inside the legacy cluster
-- itself.  They are stdlib-flavoured facts about a per-step universe
-- growth that the M base does not perform, so extracting them into a
-- standalone library would recreate machinery that has no consumer.
--
-- 严格累积层级的吸收清单。
--
-- 旧的跨宇宙累积层级（StrictLift / CumulativeHierarchy* /
-- DependentEmbedding）以及建于其上的 FinCatN* / FinCatInfinity* 塔簇，
-- 用于每层迭代把容器宇宙抬一级，并把嵌入（strictEmbed / dep-embed）及
-- 其极限贯穿该塔。它带有 40+ 处 subst：约 38 处是 Agda 原生跨 universe
-- 的 Lift/lower 交换，其余是容器态射沿形状等式搬位置（subst PosOf）。
--
-- 在携带式 M 底座上，整塔存在的理由消失：
--
--   * 迭代 ShapeCat 就是迭代 M 索引
--     MO.I = Σ (Obj C) (ShapeOf FC)，故严格层塔被索引余归纳类型归纳
--     吸收；
--   * CosmosM 在单一层次 Set (o ⊔ h ⊔ e ⊔ s ⊔ p) 上 universe 多态：没有
--     逐层 lsuc 抬级，也就无需贯穿 Lift/lower 交换；
--   * 边纤维自带伴随 FiberAdjˢ，沿形状等式搬位置是函数（to/fro），不是
--     subst。
--
-- 因此严格层级的每个结果都在 M / Carried 上重建。本模块没有定义：其
-- import 闭包即形式化覆盖清单。移除或削弱下面任一替代者都会使本模块
-- 编译失败，这正是许可归档旧簇的守卫。
--
-- 覆盖映射（旧结果 -> 替代者）见上表；原生 Lift/lower 交换引理不迁移：
-- 审计表明其唯一消费者都在旧簇内部，而 M 底座不执行逐层 universe 增长，
-- 抽成独立库只会重建无消费者的机器。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.HierarchyAbsorption where

-- Terminality of the indexed coinductive cosmos and the anamorphism.
-- 索引余归纳宇宙的终性与 anamorphism。
import ALMA.Cosmos.M.Object
import ALMA.Cosmos.M.CoalgCat
import ALMA.Cosmos.M.Terminal

-- Positive tower-colimit universal properties on the carried base.
-- 携带式底座上的正面塔余极限泛性质。
import ALMA.Cosmos.Carried.SeqColimit
import ALMA.Cosmos.Carried.FinColimit
import ALMA.Cosmos.Carried.FinTower
import ALMA.Cosmos.Carried.LimitSystem
import ALMA.Cosmos.Carried.DetColimit

-- Constructive boundary obstructions (projective / surjective).
-- 构造性边界障碍（投射/满射）。
import ALMA.Cosmos.Carried.Boundaries

-- Negative results that replace the strict-hierarchy obstruction cluster.
-- 取代严格层级障碍簇的否定性结果。
import ALMA.Cosmos.M.TowerSeparation
import ALMA.Cosmos.M.PermutationNonCommutative
import ALMA.Cosmos.M.NontrivialLimit
import ALMA.Cosmos.M.SewingObstruction
import ALMA.Cosmos.M.PermutedEmbedding
