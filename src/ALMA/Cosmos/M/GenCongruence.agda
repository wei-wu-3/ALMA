------------------------------------------------------------------------
-- Deterministic congruence engine for the LABEL-CHANGING container regime
--
-- This is the strict generalisation of DetCongruence.  The fixed-label
-- engine there forces the deterministic shape action to be the identity
-- (FMapˢ.shape x d = d).  Here a label action
--
--   σ : (x : I) → CosmosData → CosmosData
--
-- is carried, so the image tree at F₀ S x carries the (possibly
-- different) label σ x d.  This is the regime of the old label-changing
-- _⇒ℱ_ witnesses such as the list swap01: the position permutation
-- changes the position-to-shape map pts, hence changes the label.
--
-- The one hypothesis that survives from the fixed-label engine is that
-- the canonical child coverage is LABEL-INDEPENDENT: a target index v is
-- covered by a source index x' (with F₀ S x' ≡ v) depending only on v.
-- This still holds for the list swap (S is the identity on the index,
-- pb v = (v , refl)): relabelling pts is exactly what makes the swapped
-- target edge at child v correspond to the source edge that already
-- reaches v, so the two per-label image trees pull a target edge back to
-- the SAME source index x'.
--
-- Under that hypothesis the coinductive engine is structurally the
-- fixed-label one; the only change is that the TARGET edge fibres carry
-- σ x dT / σ x dS instead of dT / dS.  The hypothesis's own source-level
-- cross-label adjunction, the two per-label adjunctions and compAdjˢ line
-- up unchanged, because FiberAdjˢ relates two possibly-different fibre
-- types by carried to/fro functions (no transport).  The output head
-- coherence is cong (σ x) (h .here-eq), which is also the FMˢ shape-cong.
--
-- The fixed-label engine is the special case σ x d = d (see
-- DetCongruence); it is kept as a separate file.  No K, UIP, subst or
-- cast is used here.
--
-- 改标签容器制度下的确定性同余引擎
--
-- 这是 DetCongruence 的严格泛化。固定标签引擎强制确定性形状作用为恒等
-- （FMapˢ.shape x d = d）。这里携带一个标签作用
--
--   σ : (x : I) → CosmosData → CosmosData
--
-- 使 F₀ S x 处的像树携带（可能不同的）标签 σ x d。这正是旧的改标签
-- _⇒ℱ_ 见证（如列表 swap01）所处的制度：位置置换改变位置到形状映射
-- pts，从而改变标签。
--
-- 从固定标签引擎保留的唯一假设是规范子覆盖与标签无关：目标索引 v 由只
-- 依赖 v 的源索引 x'（满足 F₀ S x' ≡ v）覆盖。列表 swap 仍满足（S 在索
-- 引上为恒等，pb v = (v , refl)）：重标 pts 恰使子节点 v 处被交换的目
-- 标边对应于本就到达 v 的源边，故两棵逐标签像树把目标边拉回到同一个源
-- 索引 x'。
--
-- 在此假设下余归纳引擎与固定标签版结构相同；唯一变化是目标边纤维携带
-- σ x dT / σ x dS 而非 dT / dS。假设自带的源层跨标签伴随、两个逐标签
-- 伴随与 compAdjˢ 对齐方式不变，因为 FiberAdjˢ 以携带的 to/fro 函数
-- 联系两个可能不同的纤维类型（无传输）。输出头部相干为
-- cong (σ x) (h .here-eq)，它同时是 FMˢ 的 shape-cong。
--
-- 固定标签引擎是 σ x d = d 的特例（见 DetCongruence），另文保留。此处
-- 不用 K、UIP、subst 或 cast。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.GenCongruence where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong)

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
  -- General deterministic data: a carried label action σ together with
  -- a LABEL-INDEPENDENT coverage pullback and a per-label edge
  -- adjunction.  This is the carried shape of a label-changing
  -- deterministic container endomorphism (the onPos bijection and the
  -- new pts are encoded in σ and adj).
  --
  -- 一般确定性数据：携带的标签作用 σ，连同与标签无关的覆盖拉回和逐标签
  -- 边伴随。这是改标签确定性容器自态射的携带形状（onPos 双射与新 pts
  -- 编码进 σ 与 adj）。
  ----------------------------------------------------------------------
  record GenDet (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         : Set aL where
    field
      -- The image label at F₀ S x (may differ from d).
      -- F₀ S x 处的像标签（可与 d 不同）。
      σ   : (x : MO.I C FC) → MO.CosmosData C FC → MO.CosmosData C FC

      -- Label-independent coverage of a target index.
      -- 与标签无关的目标索引覆盖。
      pb  : (v : MO.I C FC)
          → Σ (MO.I C FC) λ x' → Functor.F₀ S x' ≡ v

      -- Per-label edge adjunction between the relabelled target fibre
      -- and the source fibre at the canonical child.
      -- 重标目标纤维与规范子处源纤维之间的逐标签边伴随。
      adj : (x : MO.I C FC) (d : MO.CosmosData C FC) (v : MO.I C FC)
          → FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) (σ x d) v))
                      (propEqOn (EM x d (proj₁ (pb v))))
  open GenDet public

  ----------------------------------------------------------------------
  -- The underlying deterministic carried functor: labels are acted on
  -- by σ; the canonical child and edge adjunction are carried.
  --
  -- 底层确定性携带函子：标签由 σ 作用；规范子与边伴随被携带。
  ----------------------------------------------------------------------
  genFMapˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (g : GenDet S) → FMapˢ sysP sysP
  FMapˢ.u      (genFMapˢ S g) = Functor.F₀ S
  FMapˢ.shape  (genFMapˢ S g) x d = σ g x d
  FMapˢ.childF (genFMapˢ S g) x d v = pb g v
  FMapˢ.adjFˢ  (genFMapˢ S g) x d v = adj g x d v

  ----------------------------------------------------------------------
  -- Edge relocation under the propositional edge EqOn (identical to the
  -- fixed-label engine): equal edges of the same node lead to bisimilar
  -- children; matching with a rigid edge variable is a legal J step.
  --
  -- 命题边 EqOn 下的边重定位（与固定标签引擎相同）：同节点相等的边导
  -- 致互模拟子树；用刚性边变量匹配是合法 J 步骤。
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

  private
    mapR-of : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (g : GenDet S)
            → ∀ {x v} → Functor.F₀ S x ≡ v
            → MO.CosmosM C FC x → MO.CosmosM C FC v
    mapR-of S g = Morphˢ.mapR (FMapˢ.asMorphˢ (genFMapˢ S g))

  -- The coinductive congruence engine for the relabelling action.  Both
  -- below fields make a DIRECT guarded go call on the pulled source
  -- child bisimulation (the backward one first reverses the non-recursive
  -- source bisimulation with ≈Mˢ-sym).  The target fibre labels are
  -- σ x dT / σ x dS; everything else is the fixed-label construction.
  --
  -- 重标作用的余归纳同余引擎。两个 below 字段都对拉回的源子互模拟作直
  -- 接受保护的 go 调用（反向先用非递归 ≈Mˢ-sym 反转发源层互模拟）。目
  -- 标纤维标签为 σ x dT / σ x dS；其余与固定标签构造相同。
  private
    go : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         (g : GenDet S)
       → ∀ {x v : MO.I C FC} (r : Functor.F₀ S x ≡ v)
         {t s : MO.CosmosM C FC x}
       → MO.≈CosmosM C FC propLabel t s
       → MO.≈CosmosM C FC propLabel (mapR-of S g r t) (mapR-of S g r s)
    go S g {x = x} {.(Functor.F₀ S x)} ≡refl {t = t} {s = s} h
        .here-eq = cong (σ g x) (h .here-eq)
    go S g {x = x} {.(Functor.F₀ S x)} ≡refl {t = t} {s = s} h
        .below-eq v =
        adjOut , ( (λ q → go S g eqw (hF q))
                 , (λ r → go S g eqw (≈Mˢ-sym ≈A ≈E (hT r))) )
      where
      dT  = M.here t
      dS  = M.here s
      dTσ = σ g x dT
      dSσ = σ g x dS
      x'  = proj₁ (pb g v)
      eqw = proj₂ (pb g v)

      -- Per-label target↔source edge adjunctions at the common child;
      -- the target fibre carries the relabelled head σ x d.
      -- 公共子节点上逐标签 目标↔源 边伴随；目标纤维携带重标头 σ x d。
      Aₜ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dTσ v))
                     (propEqOn (EM x dT x'))
      Aₜ = adj g x dT v

      Aₛ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dSσ v))
                     (propEqOn (EM x dS x'))
      Aₛ = adj g x dS v

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

      -- target-t relabel fibre → source-t → source-s.
      -- target-t 重标纤维 → source-t → source-s。
      c1 : FiberAdjˢ (propEqOn (EM x dS x'))
                     (propEqOn (EM (Functor.F₀ S x) dTσ v))
      c1 = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dTσ v))
                    (propEqOn (EM x dT x'))
                    (propEqOn (EM x dS x'))
                    (symAdjˢ Aₜ) adjH

      adjOut : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dSσ v))
                        (propEqOn (EM (Functor.F₀ S x) dTσ v))
      adjOut = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dTσ v))
                        (propEqOn (EM x dS x'))
                        (propEqOn (EM (Functor.F₀ S x) dSσ v))
                        c1 Aₛ

      -- Forward source-level child bisimulation (no go call inside).
      -- 正向源层子互模拟（其中无 go 调用）。
      hF : ∀ (q : EM (Functor.F₀ S x) dTσ v)
         → MO.≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ q))
             (M.below s x' (FiberAdjˢ.fro Aₛ (FiberAdjˢ.to adjOut q)))
      hF q =
        let eT = FiberAdjˢ.fro Aₜ q
            eS = FiberAdjˢ.to adjH eT
        in ≈Mˢ-trans ≈A ≈E (hfwd eT)
               (≈Mˢ-sym ≈A ≈E (edge-reloc s (FiberAdjˢ.η Aₛ eS)))

      -- Backward source-level child bisimulation.
      -- 反向源层子互模拟。
      hT : ∀ (r : EM (Functor.F₀ S x) dSσ v)
         → MO.≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ (FiberAdjˢ.fro adjOut r)))
             (M.below s x' (FiberAdjˢ.fro Aₛ r))
      hT r =
        let eSsrc = FiberAdjˢ.fro Aₛ r
            z     = FiberAdjˢ.fro adjH eSsrc
        in ≈Mˢ-trans ≈A ≈E (edge-reloc t (FiberAdjˢ.η Aₜ z))
               (≈Mˢ-sym ≈A ≈E (hbwd eSsrc))

  ----------------------------------------------------------------------
  -- mapFˢ is mapR along ≡refl, so the congruence is go ≡refl.
  --
  -- mapFˢ 即沿 ≡refl 的 mapR，故同余为 go ≡refl。
  ----------------------------------------------------------------------
  gen-map-cong : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                 (g : GenDet S)
               → ∀ {x : MO.I C FC} {t s : MO.CosmosM C FC x}
               → MO.≈CosmosM C FC propLabel t s
               → MO.≈CosmosM C FC propLabel
                   (FMapˢ.mapFˢ (genFMapˢ S g) x t)
                   (FMapˢ.mapFˢ (genFMapˢ S g) x s)
  gen-map-cong S g = go S g ≡refl

  ----------------------------------------------------------------------
  -- The categorical endomorphism bundle FMˢ.  shape-cong is the
  -- propositional congruence of σ; map-cong is the coinductive engine.
  --
  -- 范畴自态射束 FMˢ。shape-cong 为 σ 的命题同余；map-cong 为余归纳
  -- 引擎。
  ----------------------------------------------------------------------
  genFMˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
           (g : GenDet S) → FMˢ sysP sysP
  genFMˢ S g = record
    { mor        = genFMapˢ S g
    ; shape-cong = λ {x} {d} {d'} eq → cong (σ g x) eq
    ; map-cong   = gen-map-cong S g
    }
