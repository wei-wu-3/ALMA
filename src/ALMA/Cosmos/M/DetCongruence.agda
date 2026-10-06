------------------------------------------------------------------------
-- Deterministic congruence engine for the fixed-label container regime
--
-- This is the setoid analogue of the propositional "gow" relabelling
-- machine, restricted to the regime that actually models the old
-- deterministic container endomorphism _⇒ℱ[S]_ on a FIXED Cosmos:
--
--   * labels are PRESERVED: the deterministic shape action is the
--     identity (a fixed Cosmos carries one CosmosData label repeated at
--     every node; S reroutes indices and positions, not the label);
--   * the canonical child pullback is LABEL-INDEPENDENT: the source
--     index covering a target index v depends only on v, not on the
--     source head.
--
-- Under these two conditions the cross-label child coherence that the
-- propositional gow had to carry as FMap.childF-coh (and that cannot be
-- reconstructed pointwise without K or subst: the two heads are neutral
-- projections, see the negative boundary in ContainerInstance) is
-- DEFINITIONAL: both image trees pull a target edge back to the SAME
-- source index x'.  The only cross-label piece that remains is the
-- bisimulation already carried by the hypothesis h (its below-eq
-- FiberAdjˢ), and the two per-label edge adjunctions.  Composing these
-- three FiberAdjˢ with compAdjˢ gives the image-tree below adjunction.
--
-- The engine go is a SINGLE coinductive function indexed by the
-- (propositional, not necessarily refl) graph witness r.  It is defined
-- by the J rule with r generalised to ≡refl on the rigid index variable
-- (v = F₀ S x); the witness stays neutral at recursive calls, exactly
-- like the kernel CongIdxˢ.mapR-cross machine.  Each pulled child is
-- mapR eqw of a source child, so a recursive go eqw is the IMMEDIATE
-- (guarded) body of each forward/backward field.  The adjunction
-- round-trips (η) are closed at the SOURCE level purely from the
-- hypothesis projections and edge-reloc; no recursive call sits inside
-- them.  No K, no subst, no relocate/cast is used anywhere.
--
-- 固定标签容器制度下的确定性同余引擎
--
-- 这是命题版 "gow" 重排机器的 setoid 对应物，限定于真正刻画旧确定性
-- 容器自态射 _⇒ℱ[S]_（在固定 Cosmos 上）的制度：
--
--   * 标签保持：确定性 shape 作用为恒等（固定 Cosmos 只携带一份在每个
--     节点重复的 CosmosData 标签；S 重排索引与位置，不改标签）；
--   * 规范子拉回与标签无关：覆盖目标索引 v 的源索引只依赖 v，不依赖源
--     头部。
--
-- 在这两条下，命题版 gow 须作为 FMap.childF-coh 携带、且逐点无法在无
-- K/subst 下重建的跨标签子相干（两头部是中性投影，见 ContainerInstance
-- 的否定边界）是定义性的：两棵像树把目标边拉回到同一个源索引 x'。唯一
-- 残留的跨标签部件是假设 h 已携带的互模拟（其 below-eq FiberAdjˢ）与两
-- 个逐标签边伴随。用 compAdjˢ 复合这三个 FiberAdjˢ 即得像树 below 伴随。
--
-- 引擎 go 是单个余归纳函数，以（命题的、未必 refl 的）图见证 r 为索引。
-- 它在刚性索引变量（v = F₀ S x）上用 J 把 r 一般化为 ≡refl 来定义；递
-- 归调用处见证保持中性，与内核 CongIdxˢ.mapR-cross 机器完全同构。每个
-- 被拉回的子节点都是某源子节点的 mapR eqw，故递归 go eqw 就是每个
-- 正/反向字段的直接（受保护）函数体。伴随往返（η）在源层完全由假设的
-- 投影与 edge-reloc 闭合，其中不含任何递归调用。全程不用 K、不用
-- subst、不用 relocate/cast。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.DetCongruence where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid
  using (EqOn; SysEq; propEqOn; FiberAdjˢ; symAdjˢ; compAdjˢ
        ; Morphˢ
        ; _≈Mˢ_; here-eq; below-eq
        ; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)
open import ALMA.Base.MCorrSetoidCat
  using (FMapˢ; FMˢ)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  private
    iL = o ⊔ s
    aL = o ⊔ h ⊔ e ⊔ s ⊔ p
    bL = o ⊔ s ⊔ p

    -- Propositional label regime (the container regime).
    -- 命题标签制度（容器制度）。
    propLabel : (i : MO.I C FC) → EqOn {ℓ = aL} (MO.CosmosData C FC)
    propLabel _ = propEqOn _

    sysP : SysEq iL aL bL aL bL
    sysP = MO.sys C FC propLabel

    ≈A = SysEq.≈A sysP
    ≈E = SysEq.≈E sysP

    EM = MO.E C FC

  ----------------------------------------------------------------------
  -- Uniform deterministic data: label-preserving with a label-independent
  -- coverage pullback.  This is the carried shape of a fixed-Cosmos
  -- _⇒ℱ[S]_ (the onPos bijection supplies the per-label edge adjunction).
  --
  -- 一致确定性数据：标签保持且覆盖拉回与标签无关。这是固定 Cosmos
  -- _⇒ℱ[S]_ 的携带形状（onPos 双射供给逐标签边伴随）。
  ----------------------------------------------------------------------
  record UniDet (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         : Set aL where
    field
      pb  : (v : MO.I C FC)
          → Σ (MO.I C FC) λ x' → Functor.F₀ S x' ≡ v
      adj : (x : MO.I C FC) (d : MO.CosmosData C FC) (v : MO.I C FC)
          → FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) d v))
                      (propEqOn (EM x d (proj₁ (pb v))))
  open UniDet public

  ----------------------------------------------------------------------
  -- The underlying deterministic carried functor: labels are fixed.
  --
  -- 底层确定性携带函子：标签固定。
  ----------------------------------------------------------------------
  uniFMapˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
             (u : UniDet S) → FMapˢ sysP sysP
  FMapˢ.u      (uniFMapˢ S u) = Functor.F₀ S
  FMapˢ.shape  (uniFMapˢ S u) x d = d
  FMapˢ.childF (uniFMapˢ S u) x d v = pb u v
  FMapˢ.adjFˢ  (uniFMapˢ S u) x d v = adj u x d v

  ----------------------------------------------------------------------
  -- Edge relocation under the propositional edge EqOn: two
  -- propositionally equal edges of the same node lead to bisimilar
  -- children.  Matching the equality with a rigid edge variable is a
  -- legal J step (not K): z is generalised, not a neutral projection.
  --
  -- 命题边 EqOn 下的边重定位：同一节点两根命题相等的边导致互模拟的子
  -- 树。用刚性边变量匹配该等式是合法 J 步骤（非 K）：z 被一般化，不是
  -- 中性投影。
  ----------------------------------------------------------------------
  private
    edge-reloc : ∀ {x y : MO.I C FC}
                 (u : MO.CosmosM C FC x)
                 {e e' : EM x (M.here u) y}
               → e ≡ e'
               → MO.≈CosmosM C FC propLabel
                   (M.below u y e) (M.below u y e')
    edge-reloc u {e = z} {e' = .z} ≡refl =
      ≈Mˢ-refl ≈A ≈E (M.below u _ z)

  ----------------------------------------------------------------------
  -- The coinductive congruence engine.  go relates the two image trees
  -- obtained by relabelling along the deterministic index morphism, at
  -- an arbitrary target index v reached by the (propositional) graph
  -- witness r : F₀ S x ≡ v.  It is defined by J with r ≡refl; child
  -- coverage pb v = (x' , eqw) keeps eqw neutral and recurses directly.
  --
  -- 余归纳同余引擎。go 把沿确定性索引态射重标得到的两棵像树在由（命题）
  -- 图见证 r : F₀ S x ≡ v 到达的任意目标索引 v 处相关联。它以 r ≡refl
  -- 做 J 定义；子覆盖 pb v = (x' , eqw) 保持 eqw 中性并直接递归。
  ----------------------------------------------------------------------
  private
    mapR-of : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (u : UniDet S)
            → ∀ {x v} → Functor.F₀ S x ≡ v
            → MO.CosmosM C FC x → MO.CosmosM C FC v
    mapR-of S u = Morphˢ.mapR (FMapˢ.asMorphˢ (uniFMapˢ S u))

  -- go is a single coinductive function.  Both below fields make a
  -- DIRECT guarded go call on the pulled source-child bisimulation (the
  -- backward one first reverses the SOURCE-level bisimulation with the
  -- non-recursive ≈Mˢ-sym, which wraps only hypothesis projections, not
  -- a go call).
  --
  -- go 是单个余归纳函数。两个 below 字段都对拉回的源子互模拟作直接受保
  -- 护的 go 调用（反向先用非递归的 ≈Mˢ-sym 反转发源层互模拟，它只包裹
  -- 假设的投影，不包裹 go 调用）。
  private
    go : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         (u : UniDet S)
       → ∀ {x v : MO.I C FC} (r : Functor.F₀ S x ≡ v)
         {t s : MO.CosmosM C FC x}
       → MO.≈CosmosM C FC propLabel t s
       → MO.≈CosmosM C FC propLabel (mapR-of S u r t) (mapR-of S u r s)
    go S u {x = x} {.(Functor.F₀ S x)} ≡refl {t = t} {s = s} h
        .here-eq = h .here-eq
    go S u {x = x} {.(Functor.F₀ S x)} ≡refl {t = t} {s = s} h
        .below-eq v =
        adjOut , ( (λ q → go S u eqw (hF q))
                 , (λ r → go S u eqw (≈Mˢ-sym ≈A ≈E (hT r))) )
      where
      dT = M.here t
      dS = M.here s
      x'  = proj₁ (pb u v)
      eqw = proj₂ (pb u v)

      -- Per-label target↔source edge adjunctions at the common child.
      -- 公共子节点上逐标签的 目标↔源 边伴随。
      Aₜ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dT v))
                     (propEqOn (EM x dT x'))
      Aₜ = adj u x dT v

      Aₛ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dS v))
                     (propEqOn (EM x dS x'))
      Aₛ = adj u x dS v

      -- The hypothesis's own cross-label source adjunction.
      -- 假设自带的跨标签源伴随。
      adjH : FiberAdjˢ (propEqOn (EM x dS x'))
                       (propEqOn (EM x dT x'))
      adjH = proj₁ (h .below-eq x')

      hfwd : ∀ (e₁ : EM x dT x')
           → MO.≈CosmosM C FC propLabel
               (M.below t x' e₁)
               (M.below s x' (FiberAdjˢ.to adjH e₁))
      hfwd = proj₁ (proj₂ (h .below-eq x'))

      hbwd : ∀ (e₂ : EM x dS x')
           → MO.≈CosmosM C FC propLabel
               (M.below s x' e₂)
               (M.below t x' (FiberAdjˢ.fro adjH e₂))
      hbwd = proj₂ (proj₂ (h .below-eq x'))

      -- Stage 1: target-t ET → source-t Tsrc (sym Aₜ), then Tsrc →
      -- source-s Ssrc (adjH); overall FiberAdjˢ Ssrc ET.
      -- 第一阶段：target-t ET → source-t Tsrc（sym Aₜ），再 Tsrc →
      -- source-s Ssrc（adjH）；整体为 FiberAdjˢ Ssrc ET。
      c1 : FiberAdjˢ (propEqOn (EM x dS x'))
                     (propEqOn (EM (Functor.F₀ S x) dT v))
      c1 = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dT v))
                    (propEqOn (EM x dT x'))
                    (propEqOn (EM x dS x'))
                    (symAdjˢ Aₜ) adjH

      adjOut : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dS v))
                        (propEqOn (EM (Functor.F₀ S x) dT v))
      adjOut = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dT v))
                        (propEqOn (EM x dS x'))
                        (propEqOn (EM (Functor.F₀ S x) dS v))
                        c1 Aₛ

      -- Forward SOURCE-level child bisimulation.  The target-t edge q
      -- pulls back via Aₜ to eT; h carries eT to the s-edge to adjH eT,
      -- and the Aₛ η round-trip identifies that with the s-edge reached
      -- by the image-s pull fro Aₛ (to adjOut q).  Built only from h and
      -- edge-reloc: no go call occurs here.
      --
      -- 正向的源层子互模拟。target-t 边 q 经 Aₜ 拉回为 eT；h 把 eT 带到
      -- s 边 to adjH eT，Aₛ 的 η 往返再把它与像-s 拉回所达的 s 边
      -- fro Aₛ (to adjOut q) 等同。仅由 h 与 edge-reloc 构造，其中无 go。
      hF : ∀ (q : EM (Functor.F₀ S x) dT v)
         → MO.≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ q))
             (M.below s x' (FiberAdjˢ.fro Aₛ (FiberAdjˢ.to adjOut q)))
      hF q =
        let eT = FiberAdjˢ.fro Aₜ q
            eS = FiberAdjˢ.to adjH eT
        in ≈Mˢ-trans ≈A ≈E (hfwd eT)
               (≈Mˢ-sym ≈A ≈E (edge-reloc s (FiberAdjˢ.η Aₛ eS)))

      -- Backward SOURCE-level child bisimulation, oriented t-child ≈
      -- s-child so that a single go (then image symmetry ≈Mˢ-sym) gives
      -- the goal.
      --
      -- 反向的源层子互模拟，方向取 t-子 ≈ s-子，使单个 go（再取像对称
      -- ≈Mˢ-sym）即得目标。
      hT : ∀ (r : EM (Functor.F₀ S x) dS v)
         → MO.≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ (FiberAdjˢ.fro adjOut r)))
             (M.below s x' (FiberAdjˢ.fro Aₛ r))
      hT r =
        let eSsrc = FiberAdjˢ.fro Aₛ r
            z     = FiberAdjˢ.fro adjH eSsrc
        in ≈Mˢ-trans ≈A ≈E (edge-reloc t (FiberAdjˢ.η Aₜ z))
               (≈Mˢ-sym ≈A ≈E (hbwd eSsrc))

  ----------------------------------------------------------------------
  -- mapFˢ is mapR along ≡refl, so the desired congruence is go ≡refl.
  --
  -- mapFˢ 即沿 ≡refl 的 mapR，故所求同余为 go ≡refl。
  ----------------------------------------------------------------------
  uni-map-cong : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                 (u : UniDet S)
               → ∀ {x : MO.I C FC} {t s : MO.CosmosM C FC x}
               → MO.≈CosmosM C FC propLabel t s
               → MO.≈CosmosM C FC propLabel
                   (FMapˢ.mapFˢ (uniFMapˢ S u) x t)
                   (FMapˢ.mapFˢ (uniFMapˢ S u) x s)
  uni-map-cong S u = go S u ≡refl

  ----------------------------------------------------------------------
  -- The categorical endomorphism bundle FMˢ for a uniform deterministic
  -- S.  shape-cong is the identity (labels fixed); map-cong is the
  -- coinductive engine above.
  --
  -- 一致确定性 S 的范畴自态射束 FMˢ。shape-cong 为恒等（标签固定）；
  -- map-cong 为上述余归纳引擎。
  ----------------------------------------------------------------------
  uniFMˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
           (u : UniDet S) → FMˢ sysP sysP
  uniFMˢ S u = record
    { mor        = uniFMapˢ S u
    ; shape-cong = λ ea → ea
    ; map-cong   = uni-map-cong S u
    }
