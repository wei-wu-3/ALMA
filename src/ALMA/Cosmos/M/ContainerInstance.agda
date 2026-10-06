------------------------------------------------------------------------
-- Container instance of the M-Cosmos: type seam
--
-- This module pins down where the OLD container Cosmos (the terminal
-- coalgebra with its deterministic shape-functor morphisms _⇒ℱ[S]_)
-- lives as a SPECIAL CASE of the strictly stronger M-Cosmos.
--
-- The old morphism _⇒ℱ[S]_ is parameterised by a shape endofunctor
-- S : Functor (ShapeCat C FC) (ShapeCat C FC).  The objects of
-- ShapeCat are exactly the M-Cosmos index I = Σ Obj Shape.  Hence:
--
--   * the index relation R is the PROPOSITIONAL GRAPH of S.₀:
--         Graph S i j = S.₀ i ≡ j ;
--   * the label EqOn is propositional (propEqOn on CosmosData): in the
--     container regime labels are compared up to propositional equality;
--   * the edge FiberAdjˢ is the onPos adjunction (fro = onPos), with
--     η/ε replacing the old pts-compat / onActP (no subst).
--
-- DetCosmosM⇒ S is therefore the exact carried type of the old
-- _⇒ℱ[S]_; inhabiting it from an onPos map and the round-trip laws is
-- the next slice.  The general M-Cosmos strictly generalises this by
-- allowing a non-propositional label EqOn (natural isomorphism at
-- C._≈_) and an arbitrary (non-graph) index relation.
--
-- M-Cosmos 的容器实例：类型接缝
--
-- 本模块钉住旧容器 Cosmos（带确定性形状函子态射 _⇒ℱ[S]_ 的终余代数）
-- 作为严格更强 M-Cosmos 的特例所处的位置。
--
-- 旧态射 _⇒ℱ[S]_ 以形状自函子 S : Functor (ShapeCat C FC)
-- (ShapeCat C FC) 为参数。ShapeCat 的对象恰为 M-Cosmos 索引
-- I = Σ Obj Shape。因此：
--
--   * 索引关系 R 是 S.₀ 的命题图：Graph S i j = S.₀ i ≡ j；
--   * 标签 EqOn 是命题的（CosmosData 上的 propEqOn）：容器制度下标签
--     按命题相等比较；
--   * 边 FiberAdjˢ 是 onPos 伴随（fro = onPos），η/ε 取代旧
--     pts-compat / onActP（不用 subst）。
--
-- 故 DetCosmosM⇒ S 正是旧 _⇒ℱ[S]_ 的携带式类型；由 onPos 映射与往返
-- 律构造其 inhabitant 是下一切片。一般 M-Cosmos 严格地推广它：允许非
-- 命题标签 EqOn（C._≈_ 处的自然同构）与任意（非图）索引关系。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ContainerInstance where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Base.MCorrSetoid using (EqOn; propEqOn)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  -- The propositional graph of a shape endofunctor on the index.
  -- 形状自函子在索引上的命题图。
  Graph : Functor (ShapeCat C FC) (ShapeCat C FC)
        → MO.I C FC → MO.I C FC → Set (o ⊔ s)
  Graph S i j = Functor.F₀ S i ≡ j

  -- Propositional label equivalence: the container regime.
  -- 命题标签等价：容器制度。
  propLabel : (i : MO.I C FC)
            → EqOn {ℓ = o ⊔ h ⊔ e ⊔ s ⊔ p} (MO.CosmosData C FC)
  propLabel _ = propEqOn _

  -- The carried type of the old deterministic _⇒ℱ[S]_: a M-Cosmos
  -- correspondence over the propositional graph of S with propositional
  -- labels.  Inhabiting it is the onPos/η/ε construction (next slice).
  -- 旧确定性 _⇒ℱ[S]_ 的携带式类型：S 的命题图上、命题标签的 M-Cosmos
  -- 对应。其 inhabitant 为 onPos/η/ε 构造（下一切片）。
  DetCosmosM⇒ : Functor (ShapeCat C FC) (ShapeCat C FC)
              → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  DetCosmosM⇒ S = MO.CosmosM⇒ C FC propLabel (Graph S)

  -- The identity shape functor gives the identity deterministic Cosmos
  -- morphism: Graph id is (definitionally) the index path relation, so
  -- the carried morphism is idCosmosM.  This recovers the old id⇒ℱ (the
  -- only deterministic endomorphism that exists canonically).
  --
  -- 恒等形状函子给出恒等确定性 Cosmos 态射：Graph id（定义地）即索引
  -- 路径关系，故携带态射为 idCosmosM。这恢复了旧 id⇒ℱ（唯一典范存在
  -- 的确定性自态射）。
  Det-id : DetCosmosM⇒ idF
  Det-id = MO.idCosmosM C FC propLabel
