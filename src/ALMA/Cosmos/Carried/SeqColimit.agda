------------------------------------------------------------------------
-- Carried sequential colimit — specification slice (zero subst). A
-- Chain is an ℕ-indexed sequence of edge-indexed systems together with
-- carried embedding FMap between successive layers. Two design choices
-- eliminate the two transport axes that made the propositional-equality
-- version collapse:
--
--   * Layer arithmetic axis: the d-fold embedding iterates compF, and
--     its target stage shift d m computes by recursion on d so that
--     shift (suc d) m ≡ shift d (suc m) holds definitionally; no
--     +-suc / +-assoc cast, no castCosmos / ShiftedTower.
--   * Position axis: a cocone leg is itself a carried FMap, and leg
--     compatibility is behavioural equivalence _≈F_; no source-object
--     equality, no defaultFin / subst-src-FinCatN / cancel-subst-src.
--
-- This slice fixes the interface and the carried iterated embedding.
-- The apex construction, mediate, the triangle equations and
-- uniqueness are filled in the following slices.
--
-- 携带式序列余极限 —— 规范切片（零 subst）。Chain 是以 ℕ 为索引的边
-- 索引系统序列，相邻两层间携带嵌入 FMap。两处设计消去了让命题等式
-- 版本崩溃的两条传输轴：
--
--   * 层算术轴：d 次嵌入迭代 compF，其目标层 shift d m 对 d 递归使得
--     shift (suc d) m ≡ shift d (suc m) 定义性成立；无 +-suc / +-assoc
--     的 cast，无 castCosmos / ShiftedTower。
--   * 位置轴：余锥腿本身就是携带 FMap，腿相容性是行为等价 _≈F_；
--     无源对象等式，无 defaultFin / subst-src-FinCatN /
--     cancel-subst-src。
--
-- 本切片固定接口与携带的迭代嵌入；apex 构造、mediate、三角等式与
-- 唯一性在后续切片补齐。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.SeqColimit where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import ALMA.Base.MCorr
  using (Sys; FMap; _≈F_; idF; compF; I; A; ≈F-refl; ≈F-trans
        ; ∘-resp-≈; sym-assoc-f; identityʳ-f)

------------------------------------------------------------------------
-- Stage shift by d successor edges. Recursion on d in the form that
-- makes shift (suc d) m = shift d (suc m) hold by reduction; the
-- layer-arithmetic equality is baked into the recursion, so nothing is
-- ever transported along it.
-- 沿 d 条后继边的层偏移。按对 d 递归的方式书写，使
-- shift (suc d) m = shift d (suc m) 经归约成立；层算术等式已烤进
-- 递归，无需沿之传输任何东西。

shift : ℕ → ℕ → ℕ
shift zero    m = m
shift (suc d) m = shift d (suc m)

------------------------------------------------------------------------
-- A carried chain: systems X m and a carried embedding at each layer.
-- 携带式链：系统 X m 与每层的携带嵌入。

record Chain (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    X   : ℕ → Sys i a b
    emb : (m : ℕ) → FMap (X m) (X (suc m))

  -- Iteration of compF; the target stage computes via shift, so no
  -- arithmetic cast is needed at any step.
  -- compF 的迭代；目标层经 shift 计算，任一步都无需算术 cast。
  emb^d : (m d : ℕ) → FMap (X m) (X (shift d m))
  emb^d m zero    = idF (X m)
  emb^d m (suc d) = compF (emb^d (suc m) d) (emb m)

open Chain public

------------------------------------------------------------------------
-- A carried cocone with apex Y: a leg out of every layer, and
-- behavioural compatibility compF (leg (suc m)) (emb m) ≈F leg m.
-- 以 Y 为 apex 的携带余锥：每层一条出站腿，以及行为相容性
-- compF (leg (suc m)) (emb m) ≈F leg m。

record Cocone {i a b : Level} (ch : Chain i a b) (Y : Sys i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    leg : (m : ℕ) → FMap (X ch m) Y
    coh : (m : ℕ)
        → compF (leg (suc m)) (emb ch m) ≈F leg m

open Cocone public

------------------------------------------------------------------------
-- d-fold leg coherence, by induction on d from the one-step coh; a
-- finite chain of behavioural equivalences (associativity, congruence,
-- coh), with no source-object equality and no dependent transport.
-- d 次腿相干性，由一步 coh 对 d 归纳；行为等价的有限链（结合律、
-- 同余、coh），无源对象等式、无依赖传输。

module _ {i a b : Level} {ch : Chain i a b} {L : Sys i a b}
         (coc : Cocone ch L) where

  leg-coh^d : (m d : ℕ)
            → compF (leg coc (shift d m)) (emb^d ch m d) ≈F leg coc m
  leg-coh^d m zero =
    identityʳ-f (leg coc m)
  leg-coh^d m (suc d) =
    ≈F-trans
      (sym-assoc-f
         (emb ch m)
         (emb^d ch (suc m) d)
         (leg coc (shift d (suc m))))
      (≈F-trans
         (∘-resp-≈
            (leg-coh^d (suc m) d)
            (≈F-refl (emb ch m)))
         (coh coc m))

------------------------------------------------------------------------
-- The colimit universal property, expressed entirely with carried
-- morphisms and behavioural equivalence.
-- 余极限泛性质，完全用携带态射与行为等价表达。

record IsColimit {i a b : Level} {ch : Chain i a b}
                (Apex : Sys i a b) (coc : Cocone ch Apex)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    mediate  : {Y : Sys i a b} (k : Cocone ch Y) → FMap Apex Y
    triangle : {Y : Sys i a b} (k : Cocone ch Y) (m : ℕ)
             → compF (mediate k) (leg coc m) ≈F leg k m
    unique   : {Y : Sys i a b} (h : FMap Apex Y) (k : Cocone ch Y)
             → ((m : ℕ) → compF h (leg coc m) ≈F leg k m)
             → h ≈F mediate k

open IsColimit public

------------------------------------------------------------------------
-- A bundled colimit: apex, its cocone and the universal property.
-- 打包的余极限：apex、其余锥与泛性质。

record Colimit (i a b : Level) (ch : Chain i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    Apex : Sys i a b
    coc  : Cocone ch Apex
    has  : IsColimit Apex coc

open Colimit public

------------------------------------------------------------------------
-- Carried colimit limit structure (existence data). The colimit exists
-- relative to a pre-given limit system L with unbounded positions, a
-- plain (non-FMap, not child-surjective) position/label injection of
-- each stage into L, together with inj-coh (the embedding preserves
-- the injected position; one homogeneous equation on I L) and rep
-- (every limit point has a specified, total finite-stage
-- representative with a homogeneous graph witness).
--
-- rep replaces the old partial defaultFin: limit positions are
-- unbounded (ℕ), so the representative at position k is simply stage
-- k — no bound, no out-of-range case, no threshold. The graph witness
-- is homogeneous in I L; dependent fibres are aligned by carried
-- FiberAdj (added later as rep-child), never transported.
--
-- 携带式余极限的极限结构（存在性数据）。余极限相对于预给的、位置无界
-- 的极限系统 L 存在，每层到 L 有普通的（非 FMap、不满足子节点满）位置
-- 与标签注入，附带 inj-coh（嵌入保持注入位置；I L 上的单一同质等式）
-- 与 rep（每个极限点有指定的全函数有限层代表及同质图见证）。
--
-- rep 取代旧的偏函数 defaultFin：极限位置无界（ℕ），故位置 k 的代表
-- 就是第 k 层——无界、无越界、无阈值。图见证在 I L 中同质；依赖纤维
-- 由携带的 FiberAdj（后续以 rep-child 加入）对齐，绝不传输。

record Limit {i a b : Level} (ch : Chain i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where

  field
    L : Sys i a b

    -- Stage→limit position injection (toℕ). NOT an FMap: not
    -- child-surjective, hence no tree action.
    -- 阶段→极限的位置注入（toℕ）。不是 FMap：不满足子节点满，故无树
    -- 作用。
    inj-u : (m : ℕ) → I (X ch m) → I L

    inj-shape : (m : ℕ) (x : I (X ch m))
              → A (X ch m) x → A L (inj-u m x)

    -- Embedding preserves limit positions (analogue of toℕ-inject₁);
    -- a single homogeneous equation on I L.
    -- 嵌入保持极限位置（类比 toℕ-inject₁）；I L 上的单一同质等式。
    inj-coh : (m : ℕ) (x : I (X ch m))
            → inj-u (suc m) (FMap.u (emb ch m) x) ≡ inj-u m x

    -- Total representative: position k is represented at stage k,
    -- which always contains k. Replaces the partial defaultFin.
    -- 全函数代表：位置 k 在第 k 层有典范代表，而第 k 层必含 k。取代
    -- 偏函数 defaultFin。
    rep   : (v : I L)
          → Σ ℕ λ m →
            Σ (I (X ch m)) λ x →
            inj-u m x ≡ v

open Limit public
