------------------------------------------------------------------------
-- Nontrivial-fibre Fin push tower, kernel.
-- The trivial-fibre tower (LimitSystemS / FinPushColimitS) uses
-- TrivDetˢ, whose label fibre is ⊤. Here the deterministic Fin position
-- dynamics is kept (positions extended by inject₁, one deterministic
-- child per node) but labels are indexed by the STABLE GLOBAL ID ℕ, not
-- by the dependent Fin position. A stage-m label at position x is
-- L m (toℕ x); the forward label map l-emb m v stays at the same global
-- id v, so its type mentions no Fin. The apex label Thread v is a
-- stage-tagged element of L _ v; forward iteration changes only the
-- stage, never a Fin index. Consequently labels cross stages purely by
-- function passing: no Fin alignment, no transport, no K, no retraction.
--
-- 非平凡纤维 Fin push 塔内核。
-- 平凡纤维塔（LimitSystemS / FinPushColimitS）采用 TrivDetˢ，标签纤维为
-- ⊤。此处保留确定性 Fin 位置动力（位置经 inject₁ 扩张，每节点一个确定
-- 性子节点），但标签按稳定全局 id ℕ 索引，而非依赖的 Fin 位置。阶段 m
-- 位置 x 处的标签为 L m (toℕ x)；前向标签映射 l-emb m v 停留在同一全局
-- id v，故其类型不涉及 Fin。顶点标签 Thread v 是 L _ v 的阶段标签化元素；
-- 前向迭代只改阶段，不改 Fin 索引。因此标签跨阶段纯由函数传递：无 Fin
-- 对齐、无传输、不用 K、无需收缩。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.NontrivialPushTowerS where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin.Base using (Fin; inject₁; toℕ)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; propEqOn)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)
open import ALMA.Cosmos.Carried.LimitSystemS using (n-at)
import ALMA.Cosmos.Carried.LimitSystemS as LS

open SysEq

------------------------------------------------------------------------
-- A deterministic Fin tower with labels indexed by global id.
--
-- t is the deterministic position transition; embed-compat is its
-- compatibility with the one-position extension inject₁. L m v is the
-- label at global id v as present at stage m (total over v; labels at
-- not-yet-born positions are free). l-emb carries a label at global id v
-- from stage m to stage m+1 at the SAME v.
--
-- 标签按全局 id 索引的确定性 Fin 塔。
-- t 为确定性位置转移；embed-compat 是其与单位置扩张 inject₁ 的相容性。
-- L m v 是全局 id v 在阶段 m 的标签（对 v 全；未诞生位置的标签自由）。
-- l-emb 把全局 id v 的标签从阶段 m 携带到阶段 m+1，v 不变。

record LabeledFinTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    t        : (m : ℕ) → Fin (n-at m) → Fin (n-at m)
    L        : (m : ℕ) → ℕ → Set ℓ
    l-emb    : (m v : ℕ) → L m v → L (suc m) v
    embed-compat :
      (m : ℕ) (x : Fin (n-at m))
      → t (suc m) (inject₁ x) ≡ inject₁ (t m x)

module Tower {ℓ : Level} (T : LabeledFinTower ℓ) where

  open LabeledFinTower T
  open LS.LimitSystemS t embed-compat using (s∞)

  ----------------------------------------------------------------------
  -- Stage systems. Labels are pulled from the global-id family via toℕ;
  -- the edge fibre is the singleton proof y ≡ t m x (one child).
  -- 阶段系统。标签经 toℕ 取自全局 id 族；边纤维为单点证明 y ≡ t m x
  -- （唯一子节点）。

  LStage : (m : ℕ) → SysEq lzero ℓ lzero ℓ lzero
  LStage m = record
    { I  = Fin (n-at m)
    ; A  = λ x → L m (toℕ x)
    ; E  = λ x _ y → Σ (⊤ {lzero}) λ _ → y ≡ t m x
    ; ≈A = λ x → propEqOn (L m (toℕ x))
    ; ≈E = λ x _ y → propEqOn (Σ (⊤ {lzero}) λ _ → y ≡ t m x)
    }

  -- Deterministic orbit under a global labelling (lab by global id).
  -- 全局标签族（按全局 id）下的确定性轨道。
  orbit : (m : ℕ) (x : Fin (n-at m)) (lab : ∀ v → L m v)
        → M (A (LStage m)) (E (LStage m)) x
  orbit m x lab .M.here      = lab (toℕ x)
  orbit m x lab .M.below y _ = orbit m y lab

  ----------------------------------------------------------------------
  -- One-step index embedding and the graph label correspondence.
  -- 一步索引嵌入与图标签对应。

  R-emb : (m : ℕ) → Fin (n-at m) → Fin (n-at (suc m)) → Set lzero
  R-emb m x y = inject₁ x ≡ y

  -- At y = inject₁ x the two positions share global id toℕ x, so the
  -- label correspondence is the graph of l-emb m (toℕ x): no Fin in its
  -- type.
  -- 在 y = inject₁ x 处两位置共享全局 id toℕ x，故标签对应即
  -- l-emb m (toℕ x) 的图：类型中无 Fin。
  H-emb : (m : ℕ) (x : Fin (n-at m)) (y : Fin (n-at (suc m)))
        → R-emb m x y
        → A (LStage m) x → A (LStage (suc m)) y → Set ℓ
  H-emb m x .(inject₁ x) refl a b rewrite toℕ-inject₁ x =
    l-emb m (toℕ x) a ≡ b

  -- The embedding as a forward simulation. lab₁ is the next-stage
  -- global labelling, coherent with lab under l-emb.
  -- 嵌入作为前向模拟。lab₁ 是下一阶段全局标签族，与 lab 经 l-emb 相干。
  emb-sim : (m : ℕ) (lab : ∀ v → L m v) (lab₁ : ∀ v → L (suc m) v)
          → (coh : ∀ v → l-emb m v (lab v) ≡ lab₁ v)
          → (x : Fin (n-at m))
          → PushSimˢ (LStage m) (LStage (suc m)) (R-emb m) (H-emb m)
                      refl (orbit m x lab) (orbit (suc m) (inject₁ x) lab₁)
  emb-sim m lab lab₁ coh x .PushSimˢ.here-eq rewrite toℕ-inject₁ x =
    coh (toℕ x)
  emb-sim m lab lab₁ coh x .PushSimˢ.push y (_ , eq) =
    inject₁ y , ((tt , edge) , (refl , emb-sim m lab lab₁ coh y))
    where
      edge : inject₁ y ≡ t (suc m) (inject₁ x)
      edge = trans (cong inject₁ eq) (sym (embed-compat m x))

  ----------------------------------------------------------------------
  -- Eventual label at global id v: a stage-tagged element of L _ v.
  -- There is no Fin position in the carrier; extend changes only the
  -- stage and applies l-emb at the fixed v.
  -- 全局 id v 处的最终标签：L _ v 的阶段标签化元素。载体内无 Fin 位置；
  -- extend 只改阶段并在固定 v 上应用 l-emb。

  record Thread (v : ℕ) : Set (ℓ ⊔ lzero) where
    inductive
    constructor mk
    field
      stage  : ℕ
      tlabel : L stage v
  open Thread public

  extend : ∀ {v} → Thread v → Thread v
  extend {v} (mk m a) = mk (suc m) (l-emb m v a)

  extend^ : ∀ {v} → ℕ → Thread v → Thread v
  extend^ zero    t = t
  extend^ (suc n) t = extend (extend^ n t)

  thread-at : (v : ℕ) (m : ℕ) → L m v → Thread v
  thread-at v m a = mk m a

  ----------------------------------------------------------------------
  -- Finest carried equivalence: two threads are the same ray when some
  -- forward iterates coincide as full records. Built from ℕ iteration
  -- arithmetic and cong only; labels always live in L _ v at the same v.
  -- 最细携带等价：当某前向迭代作为整条记录重合时，两线程为同一射线。
  -- 仅由 ℕ 迭代算术与 cong 构造；标签始终处于同一 v 的 L _ v 中。

  record _≈Thread_ {v : ℕ} (t u : Thread v) : Set (ℓ ⊔ lzero) where
    field
      dl   : ℕ
      dr   : ℕ
      same : extend^ dl t ≡ extend^ dr u
  open _≈Thread_

  extend^-comp : ∀ {v} (a b : ℕ) (t : Thread v)
               → extend^ a (extend^ b t) ≡ extend^ (a + b) t
  extend^-comp zero    b t = refl
  extend^-comp (suc a) b t = cong extend (extend^-comp a b t)

  iter-add-comm : ∀ {v} (a b : ℕ) (t : Thread v)
                → extend^ (a + b) t ≡ extend^ (b + a) t
  iter-add-comm a b t rewrite +-comm a b = refl

  ≈Thread-refl : ∀ {v} {t : Thread v} → t ≈Thread t
  ≈Thread-refl = record { dl = zero ; dr = zero ; same = refl }

  ≈Thread-sym : ∀ {v} {t u : Thread v} → t ≈Thread u → u ≈Thread t
  ≈Thread-sym p = record { dl = dr p ; dr = dl p ; same = sym (same p) }

  ≈Thread-trans : ∀ {v} {t u w : Thread v}
                → t ≈Thread u → u ≈Thread w → t ≈Thread w
  ≈Thread-trans {u = u} p q = record
    { dl = c + a
    ; dr = b + d
    ; same =
        trans (sym (extend^-comp c a _))
        (trans (cong (extend^ c) (same p))
        (trans (extend^-comp c b u)
        (trans (iter-add-comm c b u)
        (trans (sym (extend^-comp b c u))
        (trans (cong (extend^ b) (same q))
               (extend^-comp b d _))))))
    }
    where
    a = dl p ; b = dr p ; c = dl q ; d = dr q

  ≈A∞ : (v : ℕ) → EqOn {ℓ = ℓ ⊔ lzero} (Thread v)
  ≈A∞ v = record
    { _≈_ = _≈Thread_
    ; isEquivalence = record
      { refl  = ≈Thread-refl
      ; sym   = ≈Thread-sym
      ; trans = ≈Thread-trans
      }
    }

  ----------------------------------------------------------------------
  -- Apex system: ℕ index, deterministic dynamics s∞, Thread labels,
  -- singleton deterministic edges.
  -- 顶点系统：ℕ 索引、确定性动力 s∞、Thread 标签、单点确定性边。

  L∞ : SysEq lzero (ℓ ⊔ lzero) lzero (ℓ ⊔ lzero) lzero
  L∞ = record
    { I  = ℕ
    ; A  = Thread
    ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ s∞ v
    ; ≈A = ≈A∞
    ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v)
    }
