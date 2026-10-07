------------------------------------------------------------------------
-- Nontrivial-fibre Fin push tower, kernel slice.
-- The trivial-fibre tower (LimitSystemS / FinPushColimitS) uses
-- TrivDetˢ, whose label fibre is ⊤. This slice keeps the deterministic
-- index growth (Fin positions extended by inject₁, one deterministic
-- child per node) but replaces the label fibre by an arbitrary carried
-- family L m x with a forward label map l-emb into the next stage. The
-- one-step stage embedding is a PushSimˢ whose label correspondence is
-- the graph of l-emb: labels move by function passing, and the target
-- index/edge are returned as Σ witnesses by push, so no Fin-indexed
-- iteration, no transport, no K.
--
-- 非平凡纤维 Fin push 塔，内核切片。
-- 平凡纤维塔（LimitSystemS / FinPushColimitS）采用 TrivDetˢ，其标签纤维
-- 为 ⊤。本切片保持确定性索引增长（Fin 位置经 inject₁ 扩张，每节点一个确定
-- 性子节点），但把标签纤维换成任意携带族 L m x，以及进入下一阶段的前向标签
-- 映射 l-emb。一步阶段嵌入是 PushSimˢ，其标签对应即 l-emb 的图：标签经函数
-- 传递移动，目标索引/边由 push 以 Σ 见证返回，故无 Fin 索引迭代、无传输、
-- 不用 K。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.NontrivialPushTowerS where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; inject₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; propEqOn)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)
open import ALMA.Cosmos.Carried.LimitSystemS using (n-at)

open SysEq

------------------------------------------------------------------------
-- A deterministic labelled Fin tower.
--
-- Stage m has positions Fin (n-at m), a deterministic transition t m,
-- and a label family L m over its positions. inject₁ adds one position
-- at each stage; l-emb carries a label at an old position into the next
-- stage. embed-compat is the deterministic-index compatibility;
-- label-emb-step states that carrying a label forward commutes with the
-- deterministic step (the label at a child is the carried-forward label
-- at the source child).
--
-- 确定性带标签 Fin 塔。
-- 第 m 阶段有位置 Fin (n-at m)、确定性转移 t m 与位置上的标签族 L m。
-- inject₁ 每阶段新增一个位置；l-emb 把旧位置标签携带到下一阶段。
-- embed-compat 是确定性索引相容性；label-emb-step 表明标签前向携带与确定性
-- 步进交换（子节点标签即源子节点标签的前向携带）。

record LabeledFinTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    t        : (m : ℕ) → Fin (n-at m) → Fin (n-at m)
    L        : (m : ℕ) → Fin (n-at m) → Set ℓ
    l-emb    : (m : ℕ) (x : Fin (n-at m))
             → L m x → L (suc m) (inject₁ x)
    embed-compat :
      (m : ℕ) (x : Fin (n-at m))
      → t (suc m) (inject₁ x) ≡ inject₁ (t m x)

module Tower {ℓ : Level} (T : LabeledFinTower ℓ) where

  open LabeledFinTower T

  ----------------------------------------------------------------------
  -- Stage systems: deterministic index dynamics, nontrivial labels.
  -- The edge fibre is the singleton proof y ≡ t m x (one child), exactly
  -- as in TrivDetˢ, but the label fibre is L m x.
  -- 阶段系统：确定性索引动力、非平凡标签。边纤维为单点证明 y ≡ t m x
  -- （唯一子节点），与 TrivDetˢ 相同，但标签纤维为 L m x。

  LStage : (m : ℕ) → SysEq lzero ℓ lzero ℓ lzero
  LStage m = record
    { I  = Fin (n-at m)
    ; A  = L m
    ; E  = λ x _ y → Σ (⊤ {lzero}) λ _ → y ≡ t m x
    ; ≈A = λ x → propEqOn (L m x)
    ; ≈E = λ x _ y → propEqOn (Σ (⊤ {lzero}) λ _ → y ≡ t m x)
    }

  -- Deterministic orbit tree at position x, with a label at every node.
  -- 位置 x 处的确定性轨道树，每节点带标签。
  orbit : (m : ℕ) (x : Fin (n-at m)) (lab : ∀ y → L m y)
        → M (A (LStage m)) (E (LStage m)) x
  orbit m x lab .M.here                = lab x
  orbit m x lab .M.below y _           = orbit m y lab

  ----------------------------------------------------------------------
  -- One-step index embedding.
  -- 一步索引嵌入。

  R-emb : (m : ℕ) → Fin (n-at m) → Fin (n-at (suc m)) → Set lzero
  R-emb m x y = inject₁ x ≡ y

  -- Label correspondence is the graph of l-emb: a source label a is
  -- related exactly to its carried image l-emb m x a.
  -- 标签对应即 l-emb 的图：源标签 a 恰与其携带像 l-emb m x a 相关。
  H-emb : (m : ℕ) (x : Fin (n-at m)) (y : Fin (n-at (suc m)))
        → R-emb m x y
        → A (LStage m) x → A (LStage (suc m)) y → Set ℓ
  H-emb m x .(inject₁ x) refl a b = l-emb m x a ≡ b

  -- The embedding as a forward simulation. lab₁ is the total labelling
  -- of the next stage (the new top position carries free data); coh
  -- states it agrees with l-emb on every old position. The source edge
  -- (unique child y = t m x) is pushed to inject₁ y, justified by
  -- embed-compat; the child label correspondence is again coh.
  -- 嵌入作为前向模拟。lab₁ 是下一阶段的全标签族（新顶点位置携带自由
  -- 数据）；coh 表明它在每个旧位置上与 l-emb 一致。源边（唯一子节点
  -- y = t m x）被推到 inject₁ y，由 embed-compat 见证；子节点标签对应
  -- 仍由 coh 给出。
  emb-sim : (m : ℕ) (lab : ∀ y → L m y) (lab₁ : ∀ z → L (suc m) z)
          → (coh : ∀ y → l-emb m y (lab y) ≡ lab₁ (inject₁ y))
          → (x : Fin (n-at m))
          → PushSimˢ (LStage m) (LStage (suc m)) (R-emb m) (H-emb m)
                      refl (orbit m x lab) (orbit (suc m) (inject₁ x) lab₁)
  emb-sim m lab lab₁ coh x .PushSimˢ.here-eq = coh x
  emb-sim m lab lab₁ coh x .PushSimˢ.push y (_ , eq) =
    inject₁ y , ((tt , edge) , (refl , emb-sim m lab lab₁ coh y))
    where
      edge : inject₁ y ≡ t (suc m) (inject₁ x)
      edge = trans (cong inject₁ eq) (sym (embed-compat m x))
