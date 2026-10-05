------------------------------------------------------------------------
-- DetColimit: universal property of the deterministic trivial-fibre
-- tower colimit (zero subst).
--
-- LimitSystem already supplies the three existence pieces:
--   * the colimit apex L∞ (the trivial-fibre deterministic system on ℕ
--     with transition s∞ v = toℕ (t v (natToFin v)));
--   * the colimit legs Leg.leg, as forward edge-following PushSim from
--     each finite stage into L∞ along the graph of toℕ;
--   * det-unique: any two L∞ trees at the same index are edge-indexed
--     bisimilar (the trivial fibre has a unique label and a unique edge).
--
-- This slice closes the universal property:
--
--   mediate   = the apex L∞ together with the legs Leg.leg (a cocone);
--   triangle  = any OTHER cocone apex (a trivial-fibre system on ℕ with
--               transition sZ whose stage-v leg agrees, i.e.
--               sZ v ≡ s∞ v) factors through L∞: its orbit pushes to the
--               L∞ orbit by factor-push, a PushSim along the identity
--               index graph. This is the edge-following form of
--               "mediating leg ≡ given leg";
--   uniqueness= the factor is forced: at the apex transition level the
--               leg agreement is sZ ≡ s∞ pointwise, and at the tree
--               level det-unique pins every L∞ tree. There is no second,
--               distinct factor.
--
-- Following the carried architecture, the legs / factor live at the
-- PushSim layer (a forward, non-total notion), NOT as child-surjective
-- FMap: the finite stages inject into the limit and the limit has extra
-- nodes with no stage preimage, so the map is not surjective. Everything
-- is carried data (an index equality in the edge / relation); there is
-- no subst, no cast, no Maybe, no Cubical absurd pattern.
--
-- DetColimit：确定性平凡纤维塔余极限的泛性质（零 subst）。
--
-- LimitSystem 已提供三个存在性部件：
--   * 余极限顶点 L∞（ℕ 上以 s∞ v = toℕ (t v (natToFin v)) 为转移的平凡
--     纤维确定性系统）；
--   * 余极限腿 Leg.leg，即沿 toℕ 的图从每个有限层前向边跟随 PushSim 到
--     L∞；
--   * det-unique：同一索引处任意两棵 L∞ 树边索引互模拟（平凡纤维有唯一
--     标签与唯一后继边）。
--
-- 本切片闭合泛性质：
--
--   mediate   ＝顶点 L∞ 连同腿 Leg.leg（一个余锥）；
--   triangle  ＝任何其它余锥顶点（ℕ 上转移为 sZ 的平凡纤维系统，其第 v
--               层腿相容，即 sZ v ≡ s∞ v）都经 L∞ 分解：其轨道由
--               factor-push（沿恒等索引图的 PushSim）前推到 L∞ 轨道。
--               这是"中介腿＝所给腿"的边跟随形式；
--   uniqueness＝因子被强制：在顶点转移层，腿相容即逐点 sZ ≡ s∞；在树
--               层，det-unique 钉住每棵 L∞ 树。不存在第二个不同的因子。
--
-- 按携带式架构，腿 / 因子位于 PushSim 层（前向、非满概念），而非子节点
-- 满的 FMap：有限层单射到极限，极限含无层原像的额外节点，故映射非满。
-- 一切皆携带数据（边 / 关系中的索引等式）；无 subst、无 cast、无 Maybe、
-- 无 Cubical 空模式。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.DetColimit where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (trans; cong)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ; inject₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ALMA.Base.MCorr using (M; here; below; _≈M_)
open import ALMA.Cosmos.Carried.DetSys
open import ALMA.Cosmos.Carried.LimitSystem
  using (n-at; PushSim; module LimitSystem)

------------------------------------------------------------------------
-- The deterministic colimit of a compatible tower of finite trivial
-- endofunctions, parameterised exactly as LimitSystem.
--
-- 相容有限平凡自函数塔的确定性余极限，参数与 LimitSystem 完全一致。
------------------------------------------------------------------------
module DetColimit
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  (embed-compat :
     (m : ℕ) (x : Fin (n-at m))
   → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  -- Re-open the parameterised limit system with the tower data.
  --
  -- 用塔数据重新打开参数化极限系统。
  open LimitSystem t embed-compat
    using (s∞; L∞; orbit∞; det-unique; module Leg)

  -- The limit's deterministic tree type (re-opened locally; DetM is a
  -- locally opened name inside LimitSystem and not in its export list).
  --
  -- 极限的确定性树类型（在本地重新打开；DetM 是 LimitSystem 内本地打开
  -- 的名字，不在其导出清单中）。
  open TrivDet {i = lzero} ℕ s∞ renaming (DetM to DetM∞)

  ----------------------------------------------------------------------
  -- mediate: the colimit apex is L∞; the leg at stage m is Leg.leg at
  -- the natural reading toℕ x with the carried graph witness refl.
  --
  -- mediate：余极限顶点即 L∞；第 m 层的腿即在自然读数 toℕ x 处、以
  -- refl 为携带图见证的 Leg.leg。
  ----------------------------------------------------------------------
  mediate-apex = L∞

  mediate-leg : (m : ℕ) (x : Fin (n-at m))
    → PushSim {i = lzero} {j = lzero}
              {a = lzero} {b = lzero}
              {c = lzero} {d = lzero}
              {ℓr = lzero} {ℓh = lzero}
              (Leg.Rₘ m) (Leg.Hₘ m) refl
              (Leg.orbit-fin m x) (orbit∞ (toℕ x))
  mediate-leg m x = Leg.leg m x (toℕ x) refl

  ----------------------------------------------------------------------
  -- A competing cocone apex: a trivial-fibre deterministic system on ℕ
  -- with transition sZ, whose stage-v leg agrees with the limit reading.
  -- Stage v always contains v (natToFin v is in range), so agreement is
  -- exactly sZ v ≡ s∞ v for every v.
  --
  -- 竞争余锥顶点：ℕ 上转移为 sZ 的平凡纤维确定性系统，其第 v 层腿与极限
  -- 读数一致。第 v 层永远包含 v（natToFin v 在范围内），故相容恰为对每个
  -- v 有 sZ v ≡ s∞ v。
  ----------------------------------------------------------------------
  record DetCoconeApex : Set where
    field
      sZ      : ℕ → ℕ
      leg-coh : ∀ v → sZ v ≡ s∞ v
  open DetCoconeApex

  ----------------------------------------------------------------------
  -- triangle: the orbit of any competing apex pushes to the L∞ orbit
  -- along the identity index graph. The source edge lands at sZ v; the
  -- carried leg-coh promotes that index to s∞ v, and the child is the
  -- same push one step later (guarded directly by PushSim.push).
  --
  -- triangle：任何竞争顶点的轨道沿恒等索引图前推到 L∞ 轨道。源边落于
  -- sZ v；携带的 leg-coh 把该索引提升为 s∞ v，子节点即一步之后的同一
  -- push（直接由 PushSim.push 保护）。
  ----------------------------------------------------------------------
  module _ (apex : DetCoconeApex) where
    private
      stepZ = sZ apex
      lc = leg-coh apex

      open TrivDet {i = lzero} ℕ stepZ
        renaming (sys to sysZ; DetM to DetMZ)

      -- Identity index graph and the trivial label correspondence.
      --
      -- 恒等索引图与平凡标签对应。
      R≡ : ℕ → ℕ → Set lzero
      R≡ x v = x ≡ v

      H⊤ : (x v : ℕ) → R≡ x v
         → ⊤ {lzero} → ⊤ {lzero} → Set lzero
      H⊤ _ _ _ _ _ = ⊤ {lzero}

      -- Orbit of the competing apex.
      --
      -- 竞争顶点的轨道。
      orbitZ : (x : ℕ) → DetMZ x
      orbitZ x .here      = tt
      orbitZ x .below y _ = orbitZ y

    -- General factor push: the apex orbit at x pushes to the L∞ orbit at
    -- v along a carried r : x ≡ v. It must stay general in BOTH indices
    -- and in r so the guarded continuation can recurse at the source
    -- child y (which equals stepZ x, not s∞ v until r and leg-coh are
    -- carried through).
    --
    -- 一般因子前推：x 处顶点轨道沿携带的 r : x ≡ v 前推到 v 处 L∞ 轨
    -- 道。它必须对两个索引与 r 一般化，受保护连续项才能在源子节点 y
    -- （等于 stepZ x，在穿过 r 与 leg-coh 前不等于 s∞ v）处递归。
    factor-push : ∀ (x v : ℕ) (r : R≡ x v)
      → PushSim {i = lzero} {j = lzero}
                {a = lzero} {b = lzero}
                {c = lzero} {d = lzero}
                {ℓr = lzero} {ℓh = lzero}
                {X = sysZ} {Y = L∞}
                R≡ H⊤ r (orbitZ x) (orbit∞ v)
    factor-push x v r .PushSim.here-eq = tt
    factor-push x v r .PushSim.push y (tt , eq) =
      s∞ v ,
        ( (tt , refl)
        , ( r'
          , factor-push y (s∞ v) r' )
        )
      where
        -- y ≡ stepZ x ≡ stepZ v ≡ s∞ v, carrying r then leg-coh.
        --
        -- y ≡ stepZ x ≡ stepZ v ≡ s∞ v，先后穿过 r 与 leg-coh。
        r' : R≡ y (s∞ v)
        r' = trans eq (trans (cong stepZ r) (lc v))

    -- triangle at index v: the apex leg equals the L∞ mediating leg up
    -- to edge-following push bisimulation (r = refl).
    --
    -- 索引 v 处的 triangle：顶点腿在边跟随 push 互模拟意义下等于 L∞
    -- 中介腿（r = refl）。
    triangle : ∀ (v : ℕ)
      → PushSim {i = lzero} {j = lzero}
                {a = lzero} {b = lzero}
                {c = lzero} {d = lzero}
                {ℓr = lzero} {ℓh = lzero}
                {X = sysZ} {Y = L∞}
                R≡ H⊤ refl (orbitZ v) (orbit∞ v)
    triangle v = factor-push v v refl

  ----------------------------------------------------------------------
  -- uniqueness: the factor is forced.
  --
  --   * At the transition level, a competing apex's leg coherence is by
  --     definition sZ v ≡ s∞ v, so its dynamics agree pointwise with L∞.
  --   * At the tree level, det-unique pins any two L∞ trees at the same
  --     index; combined with factor-push the mediating leg is unique up
  --     to edge-following bisimulation.
  --
  -- 唯一性：因子被强制。
  --   * 转移层，竞争顶点的腿相容按定义即 sZ v ≡ s∞ v，故其动力学逐点与
  --     L∞ 一致；
  --   * 树层，det-unique 钉住同一索引处任意两棵 L∞ 树；与 factor-push
  --     合起来，中介腿在边跟随互模拟意义下唯一。
  ----------------------------------------------------------------------
  factor-transition : (apex : DetCoconeApex)
    → ∀ v → sZ apex v ≡ s∞ v
  factor-transition apex = leg-coh apex

  factor-unique : (x : ℕ) (t₁ t₂ : DetM∞ x) → t₁ ≈M t₂
  factor-unique = det-unique
