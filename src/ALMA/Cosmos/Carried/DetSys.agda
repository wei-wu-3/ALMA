------------------------------------------------------------------------
-- Deterministic indexed M-types as edge-indexed MCorr systems.
--
-- The original ALMA core (IndexedMType.Mᵢ) is a DETERMINISTIC coinductive
-- type: at a node x with label a, each position p : B x a points to the
-- single successor next x a p. MCorr instead indexes children by an
-- edge relation E x a y over the target index. This module is the bridge
-- between the two: a deterministic (I , A , B , next) presentation gives
-- an MCorr system whose edge fibre
--
--   E x a y = Σ (B x a) λ p → y ≡ next x a p
--
-- has exactly one inhabitant per reachable child (p determines y, and
-- the equation is refl), and is empty for every non-successor y. No
-- dependent transport appears: the successor equation y ≡ next x a p is
-- a homogeneous equation on the single index type I, carried inside the
-- edge witness rather than eliminated by J.
--
-- This is the object-level bridge that lets the carried colimit
-- machinery act on the existing Cosmos / Mᵢ tower. The orientation of
-- MORPHISMS over these systems (child-surjective FMap vs. a partial
-- Morph relation) is fixed separately from the live tower maps; this
-- module only fixes the objects.
--
-- 确定性索引 M 型到边索引 MCorr 系统的桥接。
-- ALMA 原内核（IndexedMType.Mᵢ）是确定性余归纳类型：在节点 x、标签 a
-- 处，每个位置 p : B x a 指向唯一后继 next x a p。MCorr 则用目标索引
-- 上的边关系 E x a y 给子节点加索引。本模块是二者的桥接：确定性的
-- (I , A , B , next) 给出一个 MCorr 系统，其边纤维
--
--   E x a y = Σ (B x a) λ p → y ≡ next x a p
--
-- 对每个可达子节点恰有一个栖居者（p 决定 y，等式为 refl），对非后继
-- y 为空。全程无依赖传输：后继等式 y ≡ next x a p 是单一索引类型 I
-- 上的同质等式，携带在边见证内，而非用 J 消去。
--
-- 这是让携带式余极限机制作用于既有 Cosmos / Mᵢ 塔的对象层桥接。这些
-- 系统上态射的方向（子节点满的 FMap 还是偏关系 Morph）将对照真实塔映
-- 射另行确定；本模块只固定对象。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.DetSys where

open import Agda.Primitive using (Level; _⊔_; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ALMA.Base.MCorr using (Sys; M)

------------------------------------------------------------------------
-- The deterministic system built from (I , A , B , next).
--
-- 由 (I , A , B , next) 构造的确定性系统。
------------------------------------------------------------------------
module DetSys {i a b : Level}
             (I : Set i)
             (A : I → Set a)
             (B : (x : I) (a : A x) → Set b)
             (next : (x : I) (a : A x) (p : B x a) → I)
             where

  -- Edge fibre: y is a successor iff it is next x a p for some p.
  -- The edge witness CARRIES the position p and the homogeneous
  -- successor equation; it is never transported.
  --
  -- 边纤维：y 是后继当且仅当存在 p 使 y = next x a p。边见证携带位置
  -- p 与同质后继等式，绝不传输。
  E : (x : I) (a : A x) (y : I) → Set (i ⊔ b)
  E x a y = Σ (B x a) λ p → y ≡ next x a p

  -- The edge level is i ⊔ b (the witness stores an index equation);
  -- labels stay at level a.
  --
  -- 边层级为 i ⊔ b（见证存一条索引等式）；标签层级仍为 a。
  sys : Sys i a (i ⊔ b)
  sys = record { I = I ; A = A ; E = E }

  -- The coinductive deterministic trees over this system.
  --
  -- 该系统上的余归纳确定性树。
  DetM : (x : I) → Set (a ⊔ i ⊔ b)
  DetM x = M A E x

------------------------------------------------------------------------
-- Trivial-fibre deterministic system over an index type I.
--
-- Every node carries one trivial label (⊤) and one trivial position
-- (⊤), hence exactly ONE successor step x : I. This is the shared shape
-- of the FinCat tower stages (I = Fin (n-at m)) and of the limit system
-- L∞ (I = ℕ) under TrivialFC∞: the only real data is the deterministic
-- transition step on indices. The edge fibre
--
--   E x tt y = y ≡ step x
--
-- is a singleton at the unique successor and empty elsewhere, so it
-- lives at the index level i and there is never any nontrivial position
-- or label transport (the K-sensitive general-fibre case is out of
-- scope, matching the live tower's Lift ⊤ fibres).
--
-- 索引类型 I 上的平凡纤维确定性系统。
-- 每个节点携带一个平凡标签（⊤）与一个平凡位置（⊤），故恰有一个后继
-- step x。这正是 FinCat 塔各层（I = Fin (n-at m)）与极限系统 L∞
-- （I = ℕ）在 TrivialFC∞ 下的共同形状：唯一的真实数据是索引上的确定
-- 性转移 step。边纤维
--
--   E x tt y = y ≡ step x
--
-- 在唯一后继处为单点、其余为空，故位于索引层 i，不存在任何非平凡的
-- 位置或标签传输（需 K 的一般纤维情形不在范围内，与真实塔的 Lift ⊤
-- 纤维一致）。
------------------------------------------------------------------------
module TrivDet {i : Level} (I : Set i) (step : I → I) where

  private
    Aᵗ : I → Set lzero
    Aᵗ _ = ⊤

    Bᵗ : (x : I) → Aᵗ x → Set lzero
    Bᵗ _ _ = ⊤

    nextᵗ : (x : I) (a : Aᵗ x) (p : Bᵗ x a) → I
    nextᵗ x _ _ = step x

  open DetSys I Aᵗ Bᵗ nextᵗ public
