------------------------------------------------------------------------
-- The M-Cosmos category: MCorrCatˢ specialised to the M-Cosmos levels
--
-- This is the strictly stronger replacement of the container
-- Cosmos/CosmosCategory.agda.  The generic category Base.MCorrSetoidCat
-- has setoid systems (SysEq) as objects and deterministic carried
-- setoid functors FMˢ as morphisms, with behavioural bisimulation as
-- hom equality.  Here we only PIN THE LEVELS so that the M-Cosmos
-- system Object.sys ≈CD is a canonical object; no construction is
-- duplicated and there is no transport.
--
-- Scope, stated precisely:
--
--   * Objects of CosmosMCat are all SysEq at the M-Cosmos levels; the
--     particular system built in Object.agda, sys ≈CD (index = base
--     object ⊎ shape, label = CosmosData, edge = position with a
--     constructive homogeneous index equation), is the canonical
--     M-Cosmos object.
--
--   * A morphism between two such systems is a FMˢ: a deterministic
--     carried functor (total index map u, shape map, canonical child
--     pullback with an edge FiberAdjˢ) that additionally carries its
--     label congruence and tree-bisimulation congruence.
--
--   * The ENDOMORPHISMS of sys ≈CD (CosmosM-endo) are the carried type
--     of the old container deterministic self-morphism _⇒ℱ[S]_: taking
--     u to be the object map of a shape endofunctor S and the edge
--     FiberAdjˢ to be the onPos adjunction recovers it.  ContainerInstance
--     supplies that data (DetData); the DetData → FMˢ conversion is the
--     container-inhabitation slice.  The identity is idFMˢ and
--     composition is compFMˢ, both zero-subst.
--
-- The general (possibly non-deterministic, non-total) correspondence
-- over an arbitrary index relation R is Object.CosmosM⇒ (a Morphˢ),
-- which is deliberately NOT a total-functor category; this module fixes
-- the deterministic, categorical fragment.
--
-- M-Cosmos 范畴：MCorrCatˢ 在 M-Cosmos 层级处的特化
--
-- 这是容器版 Cosmos/CosmosCategory.agda 的严格更强替代。通用范畴
-- Base.MCorrSetoidCat 以 setoid 系统（SysEq）为对象、确定性携带 setoid
-- 函子 FMˢ 为态射、行为互模拟为 hom 等价。此处只钉住层级，使 M-Cosmos
-- 系统 Object.sys ≈CD 成为典范对象；不重复任何构造，也无传输。
--
-- 范围，精确陈述：
--
--   * CosmosMCat 的对象是 M-Cosmos 层级上的全部 SysEq；Object.agda 所
--     建的特定系统 sys ≈CD（索引 = 基对象 ⊎ 形状，标签 = CosmosData，
--     边 = 位置加构造性同质索引等式）是典范 M-Cosmos 对象。
--
--   * 两系统间的态射是 FMˢ：确定性携带函子（全索引映射 u、shape 映
--     射、带边 FiberAdjˢ 的规范子拉回），并额外携带其标签同余与树互模
--     拟同余。
--
--   * sys ≈CD 的自态射（CosmosM-endo）即旧容器确定性自态射 _⇒ℱ[S]_ 的
--     携带式类型：令 u 为形状自函子 S 的对象映射、边 FiberAdjˢ 为
--     onPos 伴随即恢复之。ContainerInstance 供给该数据（DetData）；
--     DetData → FMˢ 的转换是容器实例化切片。恒等为 idFMˢ、复合为
--     compFMˢ，二者皆零 subst。
--
-- 任意索引关系 R 上的一般（可能非确定、非全）对应是
-- Object.CosmosM⇒（一个 Morphˢ），它刻意不是全函子范畴；本模块固定确
-- 定性的、范畴性的片段。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.CosmosCategory where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn)
open import ALMA.Base.MCorrSetoidCat
  using (MCorrCatˢ; FMˢ; idFMˢ; compFMˢ)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  ----------------------------------------------------------------------
  -- Level shorthands for the M-Cosmos system (see Object.sys).
  -- M-Cosmos 系统的层级简写（见 Object.sys）。
  ----------------------------------------------------------------------
  private
    iL = o ⊔ s
    aL = o ⊔ h ⊔ e ⊔ s ⊔ p
    bL = o ⊔ s ⊔ p

  ----------------------------------------------------------------------
  -- The canonical M-Cosmos system at a chosen label EqOn ≈CD.
  -- ≈CD is the single seam selecting propositional labels (container
  -- regime) vs natural-isomorphism labels (general category regime).
  --
  -- 在所选标签 EqOn ≈CD 下的典范 M-Cosmos 系统。≈CD 是选择命题标签
  -- （容器制度）还是自然同构标签（一般范畴制度）的唯一接缝。
  ----------------------------------------------------------------------
  cosmosSys : ∀ {ℓd : Level}
              (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
            → SysEq iL aL bL ℓd bL
  cosmosSys ≈CD = MO.sys C FC ≈CD

  ----------------------------------------------------------------------
  -- The category of setoid systems at the M-Cosmos levels, with
  -- deterministic carried functors as morphisms.  This is MCorrCatˢ
  -- with its level arguments pinned; sys ≈CD is an object of it.
  --
  -- M-Cosmos 层级上的 setoid 系统范畴，以确定性携带函子为态射。这就是
  -- 钉住层级参数的 MCorrCatˢ；sys ≈CD 是其一个对象。
  ----------------------------------------------------------------------
  CosmosMCat : ∀ {ℓd : Level}
               (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
             → Category (lsuc (aL ⊔ ℓd)) (aL ⊔ ℓd) (aL ⊔ ℓd)
  CosmosMCat {ℓd = ℓd} _ = MCorrCatˢ iL aL bL ℓd bL

  ----------------------------------------------------------------------
  -- Deterministic carried endofunctors of the M-Cosmos system: the
  -- carried type that replaces the old _⇒ℱ[S]_.  The identity and
  -- composition are the generic carried ones, with no transport.
  --
  -- M-Cosmos 系统的确定性携带自函子：取代旧 _⇒ℱ[S]_ 的携带式类型。恒
  -- 等与复合为通用携带版本，无传输。
  ----------------------------------------------------------------------
  CosmosM-endo : ∀ {ℓd : Level}
                  (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
                → Set (aL ⊔ ℓd)
  CosmosM-endo ≈CD = FMˢ (cosmosSys ≈CD) (cosmosSys ≈CD)

  id-endo : ∀ {ℓd : Level}
              (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
          → CosmosM-endo ≈CD
  id-endo _ = idFMˢ

  comp-endo : ∀ {ℓd : Level}
                (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
              → CosmosM-endo ≈CD → CosmosM-endo ≈CD → CosmosM-endo ≈CD
  comp-endo _ g f = compFMˢ g f
