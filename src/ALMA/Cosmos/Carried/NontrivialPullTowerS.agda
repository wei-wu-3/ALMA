------------------------------------------------------------------------
-- Non-trivial fibre inverse (pull / limit) system on identity-index
-- carried functors.
--
-- The push tower only carries labels forward (l-emb).  A cochain needs
-- a backward arrow, so an inverse system adds l-proj, the retraction of
-- l-emb on the already-born part (proj-emb : l-proj ∘ l-emb ≡ id).  Every
-- arrow keeps the global id, hence is an identity-index Idx⇒ and the
-- construction lives in SameIndexCatS: no Fin alignment, no transport,
-- no K, no function extensionality (the limit fibre carries a pointwise
-- setoid).
--
-- 同索引携带函子上的非平凡纤维逆向（pull / limit）系统。
--
-- push 塔只向前携带标签（l-emb）。余链需要反向箭头，故逆向系统加入
-- l-proj，即 l-emb 在已诞生部分上的收缩（proj-emb：l-proj ∘ l-emb ≡
-- id）。每条箭头保持全局 id，因而是索引恒等的 Idx⇒，构造落在
-- SameIndexCatS 中：无 Fin 对齐、无传输、不用 K、不用函数外延性（极限
-- 纤维携带逐点 setoid）。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.NontrivialPullTowerS where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid
  using (SysEq; EqOn; propEqOn; idAdjˢ; _≈Mˢ_)
open import ALMA.Base.MCorrSetoidCat using (FMapˢ)
open import ALMA.Cosmos.Carried.SameIndexCatS
  using (LabelSys; dsys; Idx⇒; idxi; compi; _≈i_)

open SysEq

------------------------------------------------------------------------
-- Inverse system of non-trivial label fibres.
-- 非平凡标签纤维的逆向系统。

record LabeledInverseTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    d        : ℕ → ℕ
    L        : (m v : ℕ) → Set ℓ
    l-emb    : (m v : ℕ) → L m v → L (suc m) v
    l-proj   : (m v : ℕ) → L (suc m) v → L m v
    proj-emb : (m v : ℕ) (a : L m v) → l-proj m v (l-emb m v a) ≡ a

module PullTower {ℓ : Level} (T : LabeledInverseTower ℓ) where

  open LabeledInverseTower T

  private
    s = d
    sYS = dsys s

  -- Stage label family (propositional fibre setoid).
  -- 阶段标签族（命题纤维 setoid）。
  stageLS : ℕ → LabelSys ℓ
  stageLS m = record
    { A₀  = L m
    ; ≈A₀ = λ v → propEqOn (L m v)
    }

  ----------------------------------------------------------------------
  -- Pointwise equality of two fibre maps into a propositional-fibre
  -- family, as a pointwise label-tree bisimulation.  The source label
  -- family may carry any setoid; only the target is propositional.  Both
  -- maps are identity-index, so the child index and child tree coincide:
  -- the head is the given equation and the children recurse guardedly.
  --
  -- 两个进入命题纤维族的纤维映射逐点相等，写成逐点标签树互模拟。源标签族
  -- 可带任意 setoid，仅目标为命题的。两映射索引恒等，故子节点索引与子树
  -- 重合：头部为所给等式，子节点守卫递归。
  module _ (X : LabelSys ℓ) (Q : ℕ → Set ℓ) where
    private
      YQ : LabelSys ℓ
      YQ = record { A₀ = Q ; ≈A₀ = λ v → propEqOn (Q v) }
      sx = sYS X
      sy = sYS YQ
      edgeEQ : (v w : ℕ) → Set lzero
      edgeEQ v w = Σ (⊤ {lzero}) λ _ → w ≡ s v
      fmap : ((v : ℕ) → LabelSys.A₀ X v → Q v) → FMapˢ sx sy
      fmap sh = record
        { u      = λ z → z
        ; shape  = sh
        ; childF = λ z _ w → w , refl
        ; adjFˢ  = λ z _ w → idAdjˢ (propEqOn (edgeEQ z w))
        }
      img : ((v : ℕ) → LabelSys.A₀ X v → Q v)
          → (v : ℕ) → M (A sx) (E sx) v → M (A sy) (E sy) v
      img sh v t = FMapˢ.mapFˢ (fmap sh) v t

    pointwise→≈i
      : (shf shg : (v : ℕ) → LabelSys.A₀ X v → Q v)
      → ((v : ℕ) (a : LabelSys.A₀ X v) → shf v a ≡ shg v a)
      → (v : ℕ) (t : M (A sx) (E sx) v)
      → _≈Mˢ_ (≈A sy) (≈E sy) (img shf v t) (img shg v t)
    pointwise→≈i shf shg eq v t = go v t
      where
      edgeAdj : (v w : ℕ) → _
      edgeAdj v w = idAdjˢ (propEqOn (edgeEQ v w))
      mutual
        go : (v : ℕ) (u : M (A sx) (E sx) v)
           → _≈Mˢ_ (≈A sy) (≈E sy) (img shf v u) (img shg v u)
        go v u ._≈Mˢ_.here-eq = eq v (M.here u)
        go v u ._≈Mˢ_.below-eq w =
            edgeAdj v w
          , ( (λ e → go w (M.below u w e))
            , (λ e → go˘ w (M.below u w e)) )

        go˘ : (v : ℕ) (u : M (A sx) (E sx) v)
            → _≈Mˢ_ (≈A sy) (≈E sy) (img shg v u) (img shf v u)
        go˘ v u ._≈Mˢ_.here-eq = EqOn.sym (≈A sy v) (eq v (M.here u))
        go˘ v u ._≈Mˢ_.below-eq w =
            edgeAdj v w
          , ( (λ e → go˘ w (M.below u w e))
            , (λ e → go w (M.below u w e)) )

  ----------------------------------------------------------------------
  -- Forward embedding and backward restriction (the cochain arrow).
  -- 前向嵌入与反向限制（余链箭头）。

  embIdx : (m : ℕ) → Idx⇒ s (stageLS m) (stageLS (suc m))
  embIdx m = record
    { shape      = λ v a → l-emb m v a
    ; shape-cong = λ e → cong (l-emb m _) e
    }

  resIdx : (m : ℕ) → Idx⇒ s (stageLS (suc m)) (stageLS m)
  resIdx m = record
    { shape      = λ v b → l-proj m v b
    ; shape-cong = λ e → cong (l-proj m _) e
    }

  -- Retraction triangle: restriction after embedding is the identity.
  -- 收缩三角：嵌入后限制为恒等。
  res-emb : (m : ℕ)
          → _≈i_ s (compi s (resIdx m) (embIdx m)) (idxi s (stageLS m))
  res-emb m =
    pointwise→≈i (stageLS m) (L m)
      (λ v a → l-proj m v (l-emb m v a))
      (λ v a → a)
      (λ v a → proj-emb m v a)

  ----------------------------------------------------------------------
  -- Limit apex: a compatible family of stage labels at each global id.
  -- Equality is pointwise over stages (a setoid), so uniqueness of the
  -- mediating morphism needs no function extensionality and no K.
  --
  -- 极限顶点：每个全局 id 处阶段标签的相容族。相等按阶段逐点给出（一个
  -- setoid），故 mediate 态射的唯一性既不需函数外延性也不用 K。
  record LimLabel (v : ℕ) : Set ℓ where
    field
      at  : (m : ℕ) → L m v
      coh : (m : ℕ) → l-proj m v (at (suc m)) ≡ at m
  open LimLabel

  apex≈ : (v : ℕ) → EqOn (LimLabel v)
  apex≈ v = record
    { _≈_ = λ a b → (m : ℕ) → at a m ≡ at b m
    ; isEquivalence = record
      { refl  = λ m → refl
      ; sym   = λ h m → sym (h m)
      ; trans = λ h k m → trans (h m) (k m)
      }
    }

  apexLS : LabelSys ℓ
  apexLS = record
    { A₀  = LimLabel
    ; ≈A₀ = apex≈
    }

  -- Projection legs: read the stage-m component of the compatible family.
  -- 投影锥腿：读取相容族的阶段 m 分量。
  projLeg : (m : ℕ) → Idx⇒ s apexLS (stageLS m)
  projLeg m = record
    { shape      = λ v a → at a m
    ; shape-cong = λ h → h m
    }

  -- Limit cone coherence: resIdx m ∘ projLeg (m+1) ≈ projLeg m.
  -- 极限锥相干：resIdx m ∘ projLeg (m+1) ≈ projLeg m。
  cone-coh : (m : ℕ)
    → _≈i_ s (compi s (resIdx m) (projLeg (suc m))) (projLeg m)
  cone-coh m =
    pointwise→≈i apexLS (L m)
      (λ v a → l-proj m v (at a (suc m)))
      (λ v a → at a m)
      (λ v a → coh a m)
