------------------------------------------------------------------------
-- Carried sequential colimit — specification slice (zero subst)
--
-- A Chain is an ℕ-indexed sequence of edge-indexed systems
-- (ALMA.Base.MCorr.Sys) together with CARRIED embedding morphisms
-- (ALMA.Base.MCorr.FMap) between successive layers.
--
-- Two design choices eliminate the two transport axes that made the
-- propositional-equality version (WIP.agda) collapse:
--
--   * Layer arithmetic axis. The d-fold embedding is iteration of the
--     carried composition compF, and its target stage is `shift d m`,
--     which computes by recursion on d so that
--       shift (suc d) m ≡ shift d (suc m)
--     holds DEFINITIONALLY. There is therefore no +-suc / +-assoc
--     equality to cast along: the old castCosmos / ShiftedTower
--     machinery (subst over the layer index) never appears.
--
--   * Position axis. A cocone leg is itself a carried FMap (it carries
--     the canonical child correspondence childF and the whole-fibre
--     FiberAdj). Leg compatibility is behavioural equivalence _≈F_,
--     never transport of a cross-category morphism along an equation
--     between source objects: the old partial defaultFin /
--     subst-src-FinCatN / cancel-subst-src machinery never appears.
--
-- This slice fixes the interface and the carried iterated embedding.
-- The concrete apex construction, mediate, the triangle equations and
-- uniqueness are filled in the following slices, each compiled green.
--
-- 携带式序列余极限 —— 规范切片（零 subst）
--
-- Chain 是以 ℕ 为索引的边索引系统（ALMA.Base.MCorr.Sys）序列，并在相
-- 邻两层之间携带嵌入态射（ALMA.Base.MCorr.FMap）。
--
-- 两处设计消去了让命题等式版本（WIP.agda）崩溃的两条传输轴：
--
--   * 层算术轴。d 次嵌入是携带复合 compF 的迭代，其目标层为
--     `shift d m`，对 d 递归使得 shift (suc d) m ≡ shift d (suc m)
--     定义性成立。因此不存在需要沿之 cast 的 +-suc / +-assoc 等式：
--     旧的 castCosmos / ShiftedTower 机器（沿层索引的 subst）不再出现。
--
--   * 位置轴。余锥腿本身就是携带的 FMap（携带规范子对应 childF 与整
--     纤维 FiberAdj）。腿的相容性是行为等价 _≈F_，绝不沿源对象等式
--     传输跨范畴态射：旧的偏函数 defaultFin / subst-src-FinCatN /
--     cancel-subst-src 机器不再出现。
--
-- 本切片固定接口与携带的迭代嵌入；具体 apex 构造、mediate、三角等
-- 式与唯一性在后续切片补齐，每片均编译通过。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.SeqColimit where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat.Base using (ℕ; zero; suc)

open import ALMA.Base.MCorr
  using (Sys; FMap; _≈F_; idF; compF
        ; ≈F-refl; ≈F-trans
        ; ∘-resp-≈; sym-assoc-f; identityʳ-f)

------------------------------------------------------------------------
-- Stage shift by d successor edges.
--
-- It is written to recurse on d in the form that makes
--   shift (suc d) m = shift d (suc m)
-- hold by reduction. This is the carried replacement for the layer
-- arithmetic equality m + suc d ≡ suc m + d (+-suc): the equality is
-- baked into the recursion, so nothing is ever transported along it.
--
-- 沿 d 条后继边的层偏移。
-- 按对 d 递归的方式书写，使 shift (suc d) m = shift d (suc m) 经归约
-- 成立。这是层算术等式 m + suc d ≡ suc m + d（+-suc）的携带替代：等
-- 式已烤进递归，无需沿之传输任何东西。
------------------------------------------------------------------------
shift : ℕ → ℕ → ℕ
shift zero    m = m
shift (suc d) m = shift d (suc m)

------------------------------------------------------------------------
-- A carried chain: systems X m and a carried embedding at each layer.
--
-- 携带式链：系统 X m 与每层的携带嵌入。
------------------------------------------------------------------------
record Chain (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    X   : ℕ → Sys i a b
    emb : (m : ℕ) → FMap (X m) (X (suc m))

  -- The d-fold embedding as iteration of the carried composition.
  -- At d = 0 it is the identity; at suc d it is emb m followed by the
  -- d-fold embedding starting at suc m. The target stage computes via
  -- shift, so no arithmetic cast is needed at any step.
  --
  -- d 次嵌入即携带复合的迭代。d = 0 为恒等；suc d 为先 emb m 再接从
  -- suc m 起的 d 次嵌入。目标层经 shift 计算，任一步都无需算术 cast。
  emb^d : (m d : ℕ) → FMap (X m) (X (shift d m))
  emb^d m zero    = idF (X m)
  emb^d m (suc d) = compF (emb^d (suc m) d) (emb m)

open Chain public

------------------------------------------------------------------------
-- A carried cocone over a chain with apex Y: a leg out of every layer
-- and behavioural compatibility saying that the leg at suc m factors
-- through the embedding.
--
-- 以 Y 为 apex 的携带余锥：每层一条出站腿，以及"suc m 处的腿经嵌入
-- 分解"的行为相容性。
------------------------------------------------------------------------
record Cocone {i a b : Level} (ch : Chain i a b) (Y : Sys i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    leg : (m : ℕ) → FMap (X ch m) Y
    -- compF (leg (suc m)) (emb ch m) ≈F leg m, carried as a behavioural
    -- equivalence; no source-object equality is involved.
    --
    -- compF (leg (suc m)) (emb ch m) ≈F leg m，作为行为等价携带；不涉
    -- 及任何源对象等式。
    coh : (m : ℕ)
        → compF (leg (suc m)) (emb ch m) ≈F leg m

open Cocone public

------------------------------------------------------------------------
-- d-fold leg coherence, carried.
--
-- From the one-step compatibility coh m we derive, by induction on d,
-- that the leg at the stage reached after d embeddings, factored
-- through the d-fold embedding, is the leg at m:
--
--   compF (leg (shift d m)) (emb^d m d) ≈F leg m
--
-- This is the carried replacement for the old transport wrapping: the
-- old code packaged every cocone / g leg in subst-src-FinCatN along a
-- defaultFin-src-eq and realigned the iterated embedCosmos^d with the
-- E1…E5 transport lemmas before every coinductive step. Here the
-- iteration is plain carried composition; coherence is a finite chain
-- of behavioural equivalences (associativity, congruence, the one-step
-- coh), with no source-object equality and no dependent transport.
--
-- d 次腿的携带相干性。
-- 由一步相容性 coh m 对 d 归纳，得到：经 d 次嵌入分解后的、偏移 d 层
-- 处的腿，在行为等价意义下就是 m 处的腿：
--
--   compF (leg (shift d m)) (emb^d m d) ≈F leg m
--
-- 这是旧传输包裹的携带替代：旧代码把每条余锥 / g 腿沿
-- defaultFin-src-eq 包一层 subst-src-FinCatN，并在每个余归纳步前用
-- E1…E5 传输引理对齐迭代的 embedCosmos^d。此处迭代就是纯携带复合，
-- 相干性是行为等价的有限链（结合律、同余、一步 coh），无源对象等式，
-- 无依赖传输。
------------------------------------------------------------------------
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
-- morphisms and behavioural equivalence:
--   mediate   — every cocone factors through the apex;
--   triangle  — mediating after a leg equals the cocone leg;
--   unique    — any morphism satisfying the triangles is mediating, up
--               to behavioural equivalence.
--
-- 余极限泛性质，完全用携带态射与行为等价表达：
--   mediate  —— 任意余锥经 apex 分解；
--   triangle —— 中介态射接余锥腿等于该余锥腿；
--   unique   —— 满足三角的任意态射在行为等价意义下等于 mediate。
------------------------------------------------------------------------
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
--
-- 打包的余极限：apex、其余锥与泛性质。
------------------------------------------------------------------------
record Colimit (i a b : Level) (ch : Chain i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    Apex : Sys i a b
    coc  : Cocone ch Apex
    has  : IsColimit Apex coc

open Colimit public
